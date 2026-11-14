"""Independent scalar oracle for exact bounded Library-value classification."""
from collections import Counter
from itertools import combinations,product
import signal
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E
from algen.conditions import PackedConditions
from algen.value_classify import PreparedValues,ValueBudgetExceeded,primitive_expansions,library


def fake(rows,atoms=None):
    f = object.__new__(E.Form)
    n = len(atoms) if atoms is not None else len(rows[0]) if rows else 3
    f.atoms = list(atoms or [('p',chr(97+i),'G') for i in range(n)])
    f.fixed = []
    f.req = {}
    f.m = np.zeros((len(rows),2*n),dtype=bool)
    for r,row in enumerate(rows):
        for i,v in enumerate(row):
            if v is not None:
                f.m[r,2*i+(0 if v else 1)] = True
    f.s,f.e = f.m.copy(),f.m.copy()
    return f


def oracle(form,queries):
    """Per-row ordinary booleans; no bitsets, native helper or shared expansion."""
    index = {a:i for i,a in enumerate(form.atoms)}
    kinds,singles,multis,refuters,offsets,rows,columns,sparse = [],[],[],[],[0],[],[],Counter()
    for prem,goal in queries:
        requested = set()
        for c in (*prem,*form.fixed,goal^1):
            atom = form.atoms[c//2]
            if atom[0]=='pair':
                if c%2:
                    raise ValueError('NOT-AND is not a conjunction')
                _,p,x,y,pol = atom
                requested.update(2*index[('p',p,t)]+(0 if pol else 1) for t in (x,y))
            else:
                requested.add(c)
        if any(c^1 in requested for c in requested):
            raise ValueError('contradictory forbidden')
        one,two,alltrue = [],0,0
        for r in range(form.m.shape[0]):
            if any(form.m[r,c^1] for c in requested):
                continue
            missing = [c for c in requested if not form.m[r,c]]
            if len(missing)==1:
                one.append((r,missing[0]))
            elif len(missing)>1:
                two += 1
            else:
                alltrue += 1
        kind = 3 if alltrue else 1 if one else 2 if two else 0
        kinds.append(kind); singles.append(len(one)); multis.append(two); refuters.append(alltrue)
        rows.extend(r for r,c in one); columns.extend(c for r,c in one); offsets.append(len(rows))
        if kind==1:
            sparse.update(r*form.m.shape[1]+c for r,c in one)
    order = sorted(sparse)
    return [np.asarray(a,dtype=d) for a,d in zip((kinds,singles,multis,refuters,offsets,rows,columns,
        order,[sparse[k] for k in order]),('u1','u8','u8','u8','u8','u8','i4','u8','u8'))]


def packed(form,queries):
    p = PackedConditions(form.m.shape[1],3,form.m.shape[0])
    for q in sorted(set(queries),key=lambda q:(len(q[0]),p._encode(*q))):
        p[q] = 0
    return p


def queries_for(n,k=3):
    for depth in range(k+1):
        for atoms in combinations(range(n),depth):
            for signs in product((0,1),repeat=depth):
                prem = tuple(2*a+s for a,s in zip(atoms,signs))
                for goal in range(2*n):
                    if goal//2 not in atoms:
                        yield prem,goal


class ValueClassifyTest(unittest.TestCase):
    def compare(self,form,queries,batch_size=10000,max_events=262144):
        p = packed(form,queries)
        before = [(d,bytes(k),bytes(v)) for d,(k,v) in p.blocks.items()]
        matrix_before = form.m.copy()
        prepared = PreparedValues(form)
        batches = list(prepared.iter_batches(p,batch_size,max_events))
        decoded = list(p)
        cursor = 0
        for b in batches:
            qs = decoded[cursor:cursor+len(b.keys)]
            expected = oracle(form,qs)
            actual = [b.kinds,b.single,b.multi,b.refuting,b.offsets,b.rows,b.columns,b.sparse_keys,b.sparse_counts]
            for i,(a,e) in enumerate(zip(actual,expected)):
                np.testing.assert_array_equal(a,e,err_msg=str((qs,i)))
            self.assertEqual(b.context_sha256,prepared.context_sha256)
            self.assertEqual(b.engine_sha256,library().source_hash)
            self.assertEqual(b.start,cursor-sum(len(v[0]) for d,v in p.blocks.items() if d<b.depth))
            self.assertLessEqual(len(b.rows),max_events)
            cursor += len(b.keys)
        self.assertEqual(cursor,len(p))
        self.assertEqual(before,[(d,bytes(k),bytes(v)) for d,(k,v) in p.blocks.items()])
        np.testing.assert_array_equal(form.m,matrix_before)
        return prepared,batches

    def test_all_queries_tails_zero_rows_and_partial_matrices(self):
        rng = np.random.default_rng(5142026)
        for nr in (0,1,2,7,63,64,65,127,128,129):
            raw = rng.integers(0,3,size=(nr,4))
            form = fake([[None if x==2 else bool(x) for x in row] for row in raw],
                        [('p',p,'G') for p in 'abcd'])
            with self.subTest(rows=nr):
                self.compare(form,queries_for(4),batch_size=37)

    def test_duplicates_and_fixed_overlap_count_one_atomic_value(self):
        form = fake([(None,True,False)])
        form.fixed = [0,0]
        _,batches = self.compare(form,[((0,),4),((0,0),4)])
        for b in batches:
            self.assertEqual(b.kinds.tolist(),[1])
            self.assertEqual(b.rows.tolist(),[0])
            self.assertEqual(b.columns.tolist(),[0])
            self.assertEqual(b.multi.tolist(),[0])

    def test_pairs_expand_both_components_with_correct_sign(self):
        atoms = [('p','p','A'),('p','p','B'),('p','q','G')]
        for row,pair,expected in [((True,None,False),6,2),((False,None,False),8,3)]:
            form = fake([row],atoms)
            E.add_pairs(form,[('A','B')])
            _,batches = self.compare(form,[((pair,),4)])
            self.assertEqual(batches[0].columns.tolist(),[expected])
        form = fake([(None,None,False)],atoms)
        E.add_pairs(form,[('A','B')])
        _,batches = self.compare(form,[((6,),4),((8,),4)])
        self.assertEqual(batches[0].kinds.tolist(),[2,2])
        self.assertFalse(len(batches[0].rows))

    def test_refutation_is_explicit_and_not_added_to_pending_value_counter(self):
        form = fake([(True,None,False),(True,None,None)])
        _,batches = self.compare(form,[((0,),4)])
        b = batches[0]
        self.assertEqual(b.kinds.tolist(),[3])
        self.assertEqual(b.refuting.tolist(),[1])
        self.assertEqual(b.single.tolist(),[1])
        self.assertEqual(b.rows.tolist(),[1])
        self.assertFalse(len(b.sparse_keys))

    def test_bounded_events_split_without_loss_and_single_too_large_is_error(self):
        form = fake([(True,True,None)]*5)
        qs = [((),4),((0,),4),((2,),4)]
        prepared,batches = self.compare(form,qs,batch_size=9,max_events=5)
        self.assertGreater(prepared.budget_retries,0)
        self.assertEqual(sum(len(b.rows) for b in batches),15)
        p = packed(form,qs)
        with self.assertRaises(ValueBudgetExceeded):
            list(PreparedValues(form).iter_batches(p,max_events=4))

    def test_key_item_sizes_endian_and_strided_arrays(self):
        form = fake([(None,)], [('p','a','G')])
        prepared = PreparedValues(form)
        for dtype in ('u1','u2','u4','u8','>u2','>u8'):
            with self.subTest(dtype=dtype):
                raw = np.asarray([2,99,3,99],dtype=dtype)[::2]
                b = prepared.classify(raw,0,1)
                self.assertEqual(b.kinds.tolist(),[1,1])
                self.assertEqual(b.columns.tolist(),[1,0])

    def test_snapshot_and_padding_are_immutable_and_context_is_specific(self):
        f = fake([(None,True,False)])
        _,P,_ = f._bits(f.m)
        P |= np.uint64((2**64-1)^1)  # dirty unused tail bits are never real rows
        prepared = PreparedValues(f)
        p = packed(f,[((0,),4)])
        batch = next(prepared.iter_batches(p))
        f.m[:,:] = False
        P[:,:] = 0
        second = next(prepared.iter_batches(p))
        np.testing.assert_array_equal(batch.kinds,second.kinds)
        self.assertFalse(prepared.P.flags.writeable)
        f2 = fake([(True,True,False)])
        self.assertNotEqual(prepared.context_sha256,PreparedValues(f2).context_sha256)

    def test_matches_current_reference_on_unique_primitive_unrefuted_domain(self):
        from tools.value_tasks import classify
        f = fake([(None,True,False),(False,True,True),(True,None,True)])
        prepared,batches = self.compare(f,queries_for(3))
        p = packed(f,queries_for(3))
        for b in batches:
            for i,key in enumerate(b.keys):
                code=int(key); goal=code&p.mask; code>>=p.width
                prem=[]
                for _ in range(b.depth):
                    prem.append(code&p.mask);code>>=p.width
                kind,pairs,multi,refuting = classify(f,list(reversed(prem))+[goal^1])
                if not refuting:
                    self.assertEqual(kind,('C','A','B','R')[b.kinds[i]])
                    j,k = map(int,b.offsets[i:i+2])
                    self.assertEqual(set(pairs),set(zip(b.rows[j:k],b.columns[j:k])))
                    self.assertEqual(multi,b.multi[i])

    def test_invalid_keys_metadata_contradictions_and_negated_pair_fail(self):
        from tools.bench_value_classify import fixture
        with self.assertRaisesRegex(ValueError,'finite benchmark domain'):
            fixture(1,2048,'partial')
        f = fake([(None,None,None)])
        prepared = PreparedValues(f)
        for kw in (dict(depth=4,width=3),dict(depth=0,width=0),dict(depth=0,width=1),
                   dict(depth=0,width=3,max_events=-1)):
            with self.subTest(kw=kw),self.assertRaises(ValueError):
                prepared.classify(np.array([8],dtype='u1'),**kw)
        for raw in (np.array([0],dtype='u1'),np.array([14],dtype='u1'),np.array([-1],dtype='i8')):
            with self.assertRaises(ValueError):
                prepared.classify(raw,0,3)
        p=packed(f,[((0,),0)])
        with self.assertRaisesRegex(ValueError,'contradictory'):
            list(prepared.iter_batches(p))
        f.m[0,:2] = True
        with self.assertRaisesRegex(ValueError,'contradictory primitive'):
            PreparedValues(f)
        f=fake([(None,None,None)],[('p','p','A'),('p','p','B'),('p','q','G')])
        E.add_pairs(f,[('A','B')])
        for q in (((7,),4),((),6)):
            with self.assertRaisesRegex(ValueError,'unsupported literal'):
                list(PreparedValues(f).iter_batches(packed(f,[q])))
        f.pair_atoms[3] = {0}
        with self.assertRaisesRegex(ValueError,'pair components'):
            primitive_expansions(f)

    def test_alarm_interrupts_kernel_and_later_call_works(self):
        f = fake([(True,True,True)]*129)
        prepared = PreparedValues(f)
        p=packed(f,[((0,),4)])
        keys = np.repeat(np.asarray(p.blocks[1][0]),1_000_000)
        library()  # compile before installing the very short signal deadline
        def timeout(signum,frame):
            raise TimeoutError('numeric value deadline')
        old=signal.signal(signal.SIGALRM,timeout)
        try:
            signal.setitimer(signal.ITIMER_REAL,.001)
            with self.assertRaises(TimeoutError):
                prepared.classify(keys,1,p.width)
        finally:
            signal.setitimer(signal.ITIMER_REAL,0)
            signal.signal(signal.SIGALRM,old)
        self.assertEqual(prepared.classify(keys[:1],1,p.width).kinds.tolist(),[0])

    def test_exception_at_native_return_boundary_frees_published_handle(self):
        from algen import value_classify as V
        prepared = PreparedValues(fake([(None,None,None)]))
        lib = library()
        freed = []
        class Proxy:
            def __getattr__(self,name):
                return getattr(lib,name)
            def algen_values(self,*args):
                lib.algen_values(*args)
                raise TimeoutError('interrupt before Python assigns call result')
            def algen_values_free(self,handle):
                freed.append(handle.value)
                lib.algen_values_free(handle)
        with patch.object(V,'library',return_value=Proxy()),self.assertRaises(TimeoutError):
            prepared.classify(np.array([12],dtype='u1'),0,3)
        self.assertEqual(len(freed),1)
        self.assertTrue(freed[0])


if __name__=='__main__':
    unittest.main()
