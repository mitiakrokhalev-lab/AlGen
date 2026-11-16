"""Research-only lazy selector search with guarded rows and proof cuts.

One solver owns original T. The meta solver contains only the finite selector
grammar and guarded filters. Updates are in-process; SQLite persistence,
the full native grammar and theory/language changes are NOT implemented.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import resource
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from tools import check_candidate_search as R


def canonical(q):
    return tuple(q[0]), q[1]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


class LazySearch:
    def __init__(self, domain, clauses, variables):
        self.d = deepcopy(domain)
        self.context = digest(vars(self.d))
        self.variables = tuple(variables)
        if type(self.d.n) is not int or self.d.n < 1 or type(self.d.k) is not int or not 0 <= self.d.k <= 3:
            raise ValueError('small domain needs n>=1, k=0..3')
        if len(self.variables) != self.d.n or len(set(self.variables)) != self.d.n or any(type(v) is not int or v <= 0 for v in self.variables):
            raise ValueError('invalid selected variables')
        self.lits = R.literals(self.d.n)
        if any(type(lit) is not int or lit not in self.lits for lit in (*self.d.fixed,*self.d.available,*(r for rs in self.d.requirements.values() for r in rs))):
            raise ValueError('invalid domain literal')
        if any(type(a) is not int or not 1 <= a <= self.d.n for a in self.d.requirements):
            raise ValueError('invalid requirement atom')
        if any(any(type(a) is not int or not 1 <= a <= self.d.n for a in group) for group in self.d.cover):
            raise ValueError('invalid coverage atom')
        base = [tuple(c) for c in clauses]
        if any(type(lit) is not int or lit == 0 for c in base for lit in c):
            raise ValueError('invalid theory literal')
        self.nv = max([*variables,*(abs(lit) for c in base for lit in c)])
        self.theory_hash = digest([base,self.variables,self.d.fixed])
        self.tp, self.mp = IDPool(start_from=self.nv+1), IDPool()
        self.P = {lit:self.mp.id(('P',lit)) for lit in self.lits}
        self.G = {lit:self.mp.id(('G',lit)) for lit in self.lits}
        self.stats = dict(meta_solves=0, positive_solves=0, countermodel_solves=0,
                          admission_solves=0, validation_solves=0)
        self.guards, self.basis, self.outside = {}, {}, {}
        self.rows, self.cuts, self.blocks = {}, [], []
        self.revision, self.complete_revision = 0, None
        self.backend = Solver(name='g4', bootstrap_with=base+[(self.tlit(lit),) for lit in self.d.fixed])
        self.meta = None
        try:
            if not self._solve('validation_solves', []):
                raise ValueError('inconsistent original theory/fixed')
            for lit in self.d.available:
                if self._solve('validation_solves',[-self.tlit(lit)]):
                    raise ValueError('unproved available requirement')
            cnf = CardEnc.atmost(list(self.P.values()),bound=min(self.d.k,len(self.P)),vpool=self.mp,encoding=EncType.seqcounter).clauses
            cnf += CardEnc.equals(list(self.G.values()),bound=1,vpool=self.mp,encoding=EncType.seqcounter).clauses
            available = set(self.d.fixed)|set(self.d.available)
            for lit in self.lits:
                cnf += [[-self.G[lit],-self.P[lit]],[-self.G[lit],-self.P[-lit]]]
                if lit > 0:
                    cnf.append([-self.P[lit],-self.P[-lit]])
                if abs(lit) in {abs(x) for x in self.d.fixed}:
                    cnf.append([-self.G[lit]])
                for req in self.d.requirements.get(abs(lit),()):
                    if req not in available:
                        cnf += [[-self.P[lit],self.P[req]],[-self.G[lit],self.P[req]]]
            for group in self.d.cover:
                cnf.append([sel[lit] for lit in self.lits if abs(lit) in group for sel in (self.P,self.G)])
            self.initial_meta_clauses = len(cnf)
            self.meta = Solver(name='g4',bootstrap_with=cnf)
        except BaseException:
            self.close()
            raise

    def __enter__(self):
        return self

    def __exit__(self,*_):
        self.close()

    def close(self):
        if self.meta is not None:
            self.meta.delete()
            self.meta = None
        if self.backend is not None:
            self.backend.delete()
            self.backend = None

    def _context(self):
        if digest(vars(self.d)) != self.context:
            raise ValueError('domain changed: create a new session/context')

    def tlit(self,lit):
        return self.variables[abs(lit)-1]*(1 if lit>0 else -1)

    def _solve(self,counter,assumptions):
        self.stats[counter] += 1
        answer = self.backend.solve(assumptions=list(assumptions))
        if answer is not True and answer is not False:
            raise RuntimeError('theory solver incomplete')
        return answer

    def _theory_assumptions(self,active=()):
        active = set(active)
        return [guard if q in active else -guard for q,guard in self.guards.items()]

    def add_row(self,key,values):
        self._context()
        if key in self.rows:
            raise ValueError('row id already exists; preserve history')
        values = tuple(values)
        if len(values)!=self.d.n or any(v is not None and type(v) is not bool for v in values):
            raise ValueError('row needs n bool/None values')
        assumptions = self._theory_assumptions()+[self.tlit(i if v else -i) for i,v in enumerate(values,1) if v is not None]
        if not self._solve('validation_solves',assumptions):
            raise ValueError('row contradicts original theory/fixed')
        self.complete_revision = None
        self.revision += 1  # before mutation: an interrupted update stays dirty
        # Fresh IDs also on retries: an interrupted mutation can leave an
        # unrecorded guarded clause, which must never be reactivated by alias.
        gate, miss = self.mp.id(), self.mp.id()
        bad = [self.P[lit] for lit in self.lits if not R.holds(lit,values)]
        clauses = [[-miss,*bad]]+[[-p,miss] for p in bad]
        clauses += [[-self.G[g],miss] for g in self.lits if R.holds(-g,values)]
        for c in clauses:
            self.meta.add_clause([-gate,*c])
        self.rows[key] = dict(values=values,active=True,gate=gate)

    def set_row_active(self,key,active):
        self._context()
        if type(active) is not bool:
            raise ValueError('row activation must be bool')
        if self.rows[key]['active'] != active:
            self.complete_revision = None
            self.revision += 1
            self.rows[key]['active'] = active

    def _refuted(self,q):
        prem,goal = q
        return any(row['active'] and all(R.holds(p,row['values']) for p in prem)
                   and R.holds(-goal,row['values']) for row in self.rows.values())

    def _refresh(self):
        gone_b = [q for q in self.basis if self._refuted(q)]
        gone_e = [q for q in self.outside if self._refuted(q)]
        new_b = {q:g for q,g in self.basis.items() if q not in gone_b}
        new_e = {q:True for q in self.outside if q not in gone_e}
        self.basis,self.outside = new_b,new_e
        return gone_b,gone_e

    def _cut_active(self,cut):
        return all(q in self.basis for q in cut['dependencies'])

    def _meta_assumptions(self):
        out = [r['gate'] if r['active'] else -r['gate'] for r in self.rows.values()]
        out += [c['gate'] if self._cut_active(c) else -c['gate'] for c in self.cuts]
        out += [b['gate'] if b['question'] in self.basis or b['question'] in self.outside else -b['gate'] for b in self.blocks]
        return out

    def _exact_block(self,q):
        prem,goal = q
        chosen = {self.P[p] for p in prem}|{self.G[goal]}
        c = [-v if v in chosen else v for v in (*self.P.values(),*self.G.values())]
        gate = self.mp.id()
        self.meta.add_clause([-gate,*c])
        self.blocks.append(dict(question=q,gate=gate))

    def _learn(self,q,phase,assumptions):
        prem,goal = q
        core = self.backend.get_core()
        if core is None or not set(core)<=set(assumptions):
            raise RuntimeError('missing/invalid UNSAT core')
        by_p = {self.tlit(p):p for p in prem}
        by_guard = {g:q for q,g in self.guards.items()}
        glit = self.tlit(goal)*(1 if phase=='positive' else -1)
        ps,has_goal,deps = [],False,[]
        for lit in core:
            if lit in by_p:
                ps.append(by_p[lit])
            elif lit == glit:
                has_goal = True
            elif abs(lit) in by_guard:
                if lit>0:
                    dep = by_guard[lit]
                    if phase!='countermodel' or dep not in self.basis:
                        raise RuntimeError('basis leaked into original-positive check')
                    deps.append(dep)
            else:
                raise RuntimeError('unmapped core assumption')
        if not ps and not has_goal:
            raise RuntimeError('original T or active B inconsistent')
        c = [-self.P[p] for p in ps]+([-self.G[goal]] if has_goal else [])
        gate = self.mp.id()
        self.meta.add_clause([-gate,*c])
        self.cuts.append(dict(gate=gate,phase=phase,question=q,core=tuple(core),
            assumptions=tuple(assumptions),guard_count=len(self.guards),
            basis_at_proof=tuple(self.basis),prem_core=tuple(ps),has_goal=has_goal,
            dependencies=tuple(deps),theory_hash=self.theory_hash))

    def _consider(self,q):
        """Private test hook; normal callers obtain q only from meta selectors."""
        prem,goal = q
        pos = self._theory_assumptions()+[self.tlit(p) for p in prem]+[self.tlit(goal)]
        if not self._solve('positive_solves',pos):
            self._learn(q,'positive',pos)
            return None
        neg = self._theory_assumptions(self.basis)+[self.tlit(p) for p in prem]+[-self.tlit(goal)]
        if not self._solve('countermodel_solves',neg):
            self._learn(q,'countermodel',neg)
            return None
        if q not in self.guards:
            guard = self.tp.id(('hypothesis',q))
            self.backend.add_clause([-guard,*[self.tlit(lit) for lit in R.clause(q)]])
            self.guards[q] = guard
        adm = self._theory_assumptions((*self.basis,q))
        accepted = self._solve('admission_solves',adm)
        if accepted:
            self.basis[q] = self.guards[q]
        else:
            self.outside[q] = True
        self._exact_block(q)
        return dict(prem=list(prem),goal=goal,admitted=accepted)

    def search(self):
        self._context()
        self.complete_revision = None
        revision = self.revision
        old_stats = dict(self.stats)
        gone_b,gone_e = self._refresh()
        blocked = {block['question'] for block in self.blocks}
        for q in (*self.basis,*self.outside):
            if q not in blocked:
                self._exact_block(q)
        initial_b,initial_e = tuple(self.basis),tuple(self.outside)
        trace = []
        while True:
            self.stats['meta_solves'] += 1
            answer = self.meta.solve(assumptions=self._meta_assumptions())
            if answer is False:
                break
            if answer is not True:
                raise RuntimeError('meta solver incomplete')
            positive = {lit for lit in self.meta.get_model() if lit>0}
            prem = tuple(lit for lit in self.lits if self.P[lit] in positive)
            goal, = (lit for lit in self.lits if self.G[lit] in positive)
            entry = self._consider((prem,goal))
            if entry is not None:
                trace.append(entry)
        if revision != self.revision:
            raise RuntimeError('rows changed during search; coverage is stale')
        self.complete_revision = revision
        return dict(complete=True,revision=revision,theory_hash=self.theory_hash,
            domain_hash=self.context,
            rows_hash=digest({k:dict(values=r['values'],active=r['active']) for k,r in self.rows.items()}),
            initial_basis=initial_b,initial_exceptions=initial_e,
            removed_basis=gone_b,removed_exceptions=gone_e,
            basis=list(self.basis),exceptions=list(self.outside),trace=trace,
            cuts=[dict(c,active=self._cut_active(c)) for c in self.cuts],
            blocks=[dict(b,active=b['question'] in self.basis or b['question'] in self.outside) for b in self.blocks],
            theory_guards=[dict(question=q,guard=g) for q,g in self.guards.items()],
            rows=deepcopy(self.rows),stats={k:self.stats[k]-old_stats[k] for k in self.stats},
            theory_variables=self.nv,meta_variables=self.meta.nof_vars(),
            initial_meta_clauses=self.initial_meta_clauses)


def verify_generation(d,variables,models,result):
    """Check all cuts against ONLY their stated deps and the WHOLE domain."""
    assert models and result['complete'] is True
    assert result['domain_hash']==digest(vars(d))
    assert result['rows_hash']==digest({k:dict(values=r['values'],active=r['active']) for k,r in result['rows'].items()})
    assert all(all(R.holds(lit,m) for m in models) for lit in (*d.fixed,*d.available))
    assert all(any(all(v is None or v==m[i] for i,v in enumerate(row['values'])) for m in models)
               for row in result['rows'].values())
    rows = [r['values'] for r in result['rows'].values() if r['active']]
    candidates = list(R.all_candidates(d))
    kinds,unknown = {},set()
    for q in candidates:
        kind = R.classify(q,rows,models)
        kinds[kind] = kinds.get(kind,0)+1
        if kind=='unknown':
            unknown.add(q)
    basis = [canonical(q) for q in result['initial_basis']]
    outside = [canonical(q) for q in result['initial_exceptions']]
    assert len(set(basis+outside))==len(basis+outside)
    assert set(basis+outside)<=unknown
    live = [m for m in models if all(R.question_true(q,m) for q in basis)]
    assert live
    seen = set(basis+outside)
    for step in result['trace']:
        q = (tuple(step['prem']),step['goal'])
        assert q in unknown and q not in seen
        seen.add(q)
        assert any(not R.question_true(q,m) for m in live)
        after = [m for m in live if R.question_true(q,m)]
        assert step['admitted'] is bool(after)
        if after:
            basis.append(q)
            live = after
        else:
            outside.append(q)
    assert basis==[canonical(q) for q in result['basis']]
    assert outside==[canonical(q) for q in result['exceptions']]
    assert all(q in unknown for q in outside)
    assert all(q in outside or all(R.question_true(q,m) for m in live) for q in unknown)
    guards = {entry['guard']:canonical(entry['question']) for entry in result['theory_guards']}
    inv = {v:i for i,v in enumerate(variables,1)}
    checks = 0
    for cut in result['cuts']:
        q = canonical(cut['question'])
        deps = [canonical(dep) for dep in cut['dependencies']]
        assert cut['theory_hash']==result['theory_hash']
        assert cut['phase'] in ('positive','countermodel')
        assert cut['phase']!='positive' or not deps
        assert bool(cut['active'])==all(dep in basis for dep in deps)
        proof_b = [canonical(b) for b in cut['basis_at_proof']]
        assert set(deps)<=set(proof_b)
        known_guards = list(guards)[:cut['guard_count']]
        expected = {g if guards[g] in proof_b and cut['phase']=='countermodel' else -g for g in known_guards}
        expected |= {variables[abs(p)-1]*(1 if p>0 else -1) for p in q[0]}
        glit = variables[abs(q[1])-1]*(1 if q[1]>0 else -1)*(1 if cut['phase']=='positive' else -1)
        expected.add(glit)
        assert set(cut['assumptions'])==expected
        assert set(cut['core'])<=expected
        ps,dep_from_core,goal_in_core = [],[],False
        for lit in cut['core']:
            if abs(lit) in guards:
                if lit>0:
                    dep_from_core.append(guards[lit])
            elif lit==glit:
                goal_in_core = True
            else:
                p = inv[abs(lit)]*(1 if lit>0 else -1)
                assert p in q[0]
                ps.append(p)
        assert ps==list(cut['prem_core']) and goal_in_core==cut['has_goal']
        assert dep_from_core==deps
        assert ps or goal_in_core
        conditioned = [m for m in models if all(R.question_true(dep,m) for dep in deps)]
        assert conditioned
        for candidate in candidates:  # deliberately NOT filtered by Library rows
            p,g = candidate
            if not set(ps)<=set(p) or goal_in_core and g!=q[1]:
                continue
            checks += 1
            if cut['phase']=='positive':
                assert not any(all(R.holds(lit,m) for lit in p) and R.holds(g,m) for m in conditioned)
            else:
                assert all(R.question_true(candidate,m) for m in conditioned)
    for block in result['blocks']:
        q = canonical(block['question'])
        assert bool(block['active'])==(q in basis or q in outside)
        if block['active']:
            assert q in unknown
    return dict(candidates=len(candidates),kinds=kinds,unknown=len(unknown),basis=len(basis),
                exceptions=len(outside),retained=len(basis)+len(outside),uncovered=0,
                checked_cuts=len(result['cuts']),cut_candidate_checks=checks,
                active_cuts=sum(c['active'] for c in result['cuts']),
                disabled_cuts=sum(not c['active'] for c in result['cuts']))


def verify_transition(d,models,previous,current):
    """Unchanged retained questions and immutable proof IDs cannot disappear."""
    assert previous['theory_hash']==current['theory_hash']
    assert previous['domain_hash']==current['domain_hash']==digest(vars(d))
    assert previous['revision']<current['revision']
    assert set(previous['rows'])<=set(current['rows'])
    for key,row in previous['rows'].items():
        assert tuple(row['values'])==tuple(current['rows'][key]['values'])
        assert row['gate']==current['rows'][key]['gate']
    rows = [r['values'] for r in current['rows'].values() if r['active']]
    def refuted(q):
        p,g = q
        return any(all(R.holds(lit,r) for lit in p) and R.holds(-g,r) for r in rows)
    old_b = [canonical(q) for q in previous['basis']]
    old_e = [canonical(q) for q in previous['exceptions']]
    assert [q for q in old_b if not refuted(q)]==[canonical(q) for q in current['initial_basis']]
    assert [q for q in old_e if not refuted(q)]==[canonical(q) for q in current['initial_exceptions']]
    assert [q for q in old_b if refuted(q)]==[canonical(q) for q in current['removed_basis']]
    assert [q for q in old_e if refuted(q)]==[canonical(q) for q in current['removed_exceptions']]
    for field in ('cuts','blocks','theory_guards'):
        assert len(current[field])>=len(previous[field])
        for old,new in zip(previous[field],current[field]):
            assert digest({k:v for k,v in old.items() if k!='active'})==digest({k:v for k,v in new.items() if k!='active'})
    old_rows = [r['values'] for r in previous['rows'].values() if r['active']]
    candidates = list(R.all_candidates(d))
    old_unknown = {q for q in candidates if R.classify(q,old_rows,models)=='unknown'}
    new_unknown = {q for q in candidates if R.classify(q,rows,models)=='unknown'}
    initial_b = [canonical(q) for q in current['initial_basis']]
    initial_e = {canonical(q) for q in current['initial_exceptions']}
    live = [m for m in models if all(R.question_true(q,m) for q in initial_b)]
    assert live
    exposed = [q for q in new_unknown if q not in initial_e and any(not R.question_true(q,m) for m in live)]
    return dict(verified=True,retained_basis=len(initial_b),retained_exceptions=len(initial_e),
        removed_basis=len(current['removed_basis']),removed_exceptions=len(current['removed_exceptions']),
        newly_unknown=len(new_unknown-old_unknown),exposed_before_repair=len(exposed))


def run():
    start, cpu = time.perf_counter(),time.process_time()
    records = []
    fixtures = []
    for seed in range(8100,8112):
        kw,cnf,rows,models = R.synthetic(seed)
        fixtures.append((f'synthetic-{seed}',kw,cnf,list(range(1,6)),rows,models,{}))
    cnf,variables,rows,info = R.real_fixture()
    models = R.projected_models(cnf,variables)
    real = ('group-four-atom-slice',dict(n=4,cover=((1,2,3),(4,))),cnf,variables,rows,models,info)
    fixtures.append(real)
    for name,kw,cnf,variables,rows,models,info in fixtures:
        for k in range(4):
            d = R.Domain(k=k,**kw)
            a,b = time.perf_counter(),time.process_time()
            with LazySearch(d,cnf,variables) as search:
                for i,row in enumerate(rows):
                    search.add_row(str(i),row)
                result = search.search()
            elapsed,spent = time.perf_counter()-a,time.process_time()-b
            a = time.perf_counter()
            checked = verify_generation(d,variables,models,result)
            records.append(dict(fixture=name,k=k,domain=vars(d),metadata=info,
                input_sha256=digest([cnf,variables,rows]),search=result,verification=checked,
                search_wall_seconds=elapsed,search_cpu_seconds=spent,
                oracle_wall_seconds=time.perf_counter()-a))
    # Real data protocol frozen before observing results: preserve unaffected B.
    name,kw,cnf,variables,rows,models,info = real
    dynamic = []
    d = R.Domain(k=3,**kw)
    with LazySearch(d,cnf,variables) as search:
        actions = [('start-C1',lambda:search.add_row('C1',rows[0])),
            ('add-C2',lambda:search.add_row('C2',rows[1])),
            ('add-V4-S3',lambda:(search.add_row('V4',rows[2]),search.add_row('S3',rows[3]))),
            ('withdraw-S3',lambda:search.set_row_active('S3',False)),
            ('withdraw-C2',lambda:search.set_row_active('C2',False)),
            ('reactivate-S3',lambda:search.set_row_active('S3',True))]
        previous = None
        for name,action in actions:
            action()
            a = time.perf_counter()
            result = search.search()
            elapsed = time.perf_counter()-a
            checked = verify_generation(d,variables,models,result)
            transition = verify_transition(d,models,previous,result) if previous is not None else None
            dynamic.append(dict(action=name,search=result,verification=checked,transition=transition,search_wall_seconds=elapsed))
            previous = result
    return dict(version=1,scope='research lazy finite domain and in-process row updates; not production/native/SQLite integration',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        reference_source_sha256=hashlib.sha256(Path(R.__file__).read_bytes()).hexdigest(),
        static_cases=records,dynamic_real=dynamic,complete=True,
        wall_seconds=time.perf_counter()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',required=True)
    a = p.parse_args()
    path = Path(a.out)
    if path.exists():
        p.error('output exists; choose a new path')
    result = run()
    with path.open('x') as out:
        json.dump(result,out,ensure_ascii=False,indent=2)
        out.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('static_cases','dynamic_real')},ensure_ascii=False))


if __name__=='__main__':
    main()
