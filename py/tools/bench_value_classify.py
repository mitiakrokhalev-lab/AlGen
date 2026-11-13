"""Small numeric benchmark against the existing vectorized value_tasks tool.

Unique primitive inputs with no refuting rows: old and new meanings agree.
Witness order is canonicalized (row,column); no CAP/KEEP/naming or SAT/report.
Synthetic matrices are Boolean fixtures, never claimed as group examples.
"""
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import resource
import time

import numpy as np

from algen.enumerate import Form
from algen.conditions import PackedConditions
from algen.value_classify import PreparedValues,library
from tools.value_tasks import classify


def timing():
    return time.perf_counter(),time.process_time()


def elapsed(t):
    now=timing()
    return dict(wall_seconds=now[0]-t[0],cpu_seconds=now[1]-t[1])


def canonical(parts):
    offsets=[0]
    rows,cols=[],[]
    sparse=Counter()
    for p in parts:
        base=offsets[-1]
        offsets.extend(int(x)+base for x in p[6][1:])
        rows.append(p[7]);cols.append(p[8])
        sparse.update({int(k):int(v) for k,v in zip(p[9],p[10])})
    order=sorted(sparse)
    head=[np.concatenate([p[i] for p in parts]) for i in range(6)]
    return head+[np.array(offsets,dtype='u8'),np.concatenate(rows),np.concatenate(cols),
        np.asarray(order,dtype='u8'),np.asarray([sparse[k] for k in order],dtype='u8')]


def digest(arrays):
    h=hashlib.sha256()
    for a in arrays:
        h.update(str((a.dtype.str,a.shape)).encode());h.update(memoryview(a))
    return h.hexdigest()


def fixture(nrows,queries,mode):
    rng=np.random.default_rng(14112026)
    atoms=12
    possible=sum(math.comb(atoms-1,k)*2**k for k in range(4))
    if not 1<=queries<=possible:
        raise ValueError('requested questions exceed the finite benchmark domain')
    raw=rng.integers(0,10,size=(nrows,atoms))
    m=np.zeros((nrows,2*atoms),dtype=bool)
    for i in range(atoms):
        if mode=='partial':
            m[:,2*i]=raw[:,i]<4;m[:,2*i+1]=(raw[:,i]>=4)&(raw[:,i]<8)
        elif mode=='known':
            m[:,2*i]=raw[:,i]<5;m[:,2*i+1]=~m[:,2*i]
    # Goal is always unknown except known mode, where its True value makes
    # every forbidden conjunction false. No current refutation is possible.
    m[:,-2:]=False
    if mode=='known':m[:,-2]=True
    f=object.__new__(Form);f.m=m;f.fixed=[];f.atoms=[('p',str(i),'G') for i in range(atoms)]
    p=PackedConditions(2*atoms,3,nrows)
    wanted={((),2*atoms-2)}
    while len(wanted)<queries:
        size=int(rng.integers(1,4))
        selected=sorted(int(x) for x in rng.choice(atoms-1,size,replace=False))
        prem=tuple(2*i+int(rng.integers(0,2)) for i in selected)
        wanted.add((prem,2*atoms-2))
    for q in sorted(wanted,key=lambda q:(len(q[0]),p._encode(*q))):p[q]=0
    return f,p


def reference(f,p):
    parts=[]
    for q in p:
        prem,goal=q
        kind,pairs,multi,refuting=classify(f,[*prem,goal^1])
        if refuting:raise AssertionError('benchmark must remain in old/new equivalence domain')
        pairs.sort()
        sparse=Counter(r*f.m.shape[1]+c for r,c in pairs) if kind=='A' else Counter()
        ks=sorted(sparse)
        parts.append([np.array([len(prem)],dtype='u1'),np.array([p._encode(*q)],dtype='u8'),
            np.array([{'C':0,'A':1,'B':2}[kind]],dtype='u1'),np.array([len(pairs)],dtype='u8'),
            np.array([multi],dtype='u8'),np.array([refuting],dtype='u8'),np.array([0,len(pairs)],dtype='u8'),
            np.array([r for r,c in pairs],dtype='u8'),np.array([c for r,c in pairs],dtype='i4'),
            np.array(ks,dtype='u8'),np.array([sparse[k] for k in ks],dtype='u8')])
    return canonical(parts)


def run_case(nrows,queries,mode):
    f,p=fixture(nrows,queries,mode)
    inputs=hashlib.sha256(memoryview(f.m))
    for depth,(keys,_) in p.blocks.items():inputs.update(bytes([depth]));inputs.update(memoryview(keys))
    t=timing();f._bits(f.m);reference_prepare=elapsed(t)
    t=timing();expected=reference(f,p);reference_time=elapsed(t)
    t=timing();prepared=PreparedValues(f);native_prepare=elapsed(t)
    t=timing();parts=[];max_batch_bytes=0
    for b in prepared.iter_batches(p,batch_size=128,max_events=262144):
        max_batch_bytes=max(max_batch_bytes,b.nbytes)
        parts.append([np.full(len(b.keys),b.depth,dtype='u1'),b.keys.astype('u8'),b.kinds,b.single,b.multi,
            b.refuting,b.offsets,b.rows,b.columns,b.sparse_keys,b.sparse_counts])
    actual=canonical(parts);native_time=elapsed(t)
    for a,b in zip(expected,actual):np.testing.assert_array_equal(a,b)
    return dict(rows=nrows,primitive_atoms=12,conditions=len(p),mode=mode,input_sha256=inputs.hexdigest(),
        output_sha256=digest(actual),canonical_arrays_compared=len(actual),event_count=len(actual[7]),
        kinds={str(k):int(v) for k,v in zip(*np.unique(actual[2],return_counts=True))},
        distinct_requested_values=len(actual[9]),reference_prepare=reference_prepare,reference=reference_time,
        native_prepare=native_prepare,native=native_time,budget_retries=prepared.budget_retries,
        max_batch_result_bytes=max_batch_bytes,context_sha256=prepared.context_sha256)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',required=True)
    parser.add_argument('--include-table-size',action='store_true',help='add a synthetic30953-row projection; no real groups')
    args=parser.parse_args()
    target=Path(args.out)
    if target.exists():parser.error('preserve existing measurements; choose another output path')
    t=timing();lib=library();loader=elapsed(t)
    cases=[run_case(1024,256,'partial'),run_case(4096,256,'unknown'),run_case(4096,256,'known')]
    if args.include_table_size:cases.append(run_case(30953,1024,'partial'))
    result=dict(version=1,reference='existing vectorized tools.value_tasks.classify plus canonical numeric assembly',
        native='bounded PreparedValues plus same global canonical numeric assembly',
        scope='synthetic unique primitive/unrefuted inputs; not group examples, production reports or whole first pass',
        cases=cases,native_loader=loader,engine_sha256=lib.source_hash,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        one_pair_per_case=True,randomized_repeats=False,compilation_cache_preserved=True,
        import_and_fixture_startup_included=False,production_speedup_claimed=False,
        tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    target.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))


if __name__=='__main__':main()
