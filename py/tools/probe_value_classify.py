"""Read-only numeric control on a real table sample, including SAT-kind cross-tab.

Invoke like tools.value_tasks with ALGEN_SAMPLE. Adds one statistics field;
does not change original verdicts, compression or enumeration. Experimental
control supports unique primitive literals only; general API supports pairs.
"""
from collections import Counter
import hashlib
import json
import re
import time

import numpy as np

from algen.conditions import PackedConditions
from algen.value_classify import PreparedValues,KINDS,library
from tools.bench_value_classify import canonical,reference,digest


def stamp():
    return time.perf_counter(),time.process_time()


def seconds(start):
    t=stamp()
    return dict(wall_seconds=t[0]-start[0],cpu_seconds=t[1]-start[1])


def valid_receipt(r,sample):
    if not isinstance(r,dict) or r.get('exact_output') is not True:
        return False
    n=r.get('classified');picked=r.get('sampled_minimals');kinds=r.get('kinds')
    digest_ok=lambda x:isinstance(x,str) and re.fullmatch('[0-9a-f]{64}',x) is not None
    return (type(n) is int and type(picked) is int and 0<n<=picked<=sample
        and r.get('canonical_arrays_per_batch')==11 and isinstance(kinds,dict)
        and all(k in KINDS and type(v) is int and v>=0 for k,v in kinds.items())
        and sum(kinds.values())==n and kinds.get('R',0)==0
        and all(digest_ok(r.get(k)) for k in ('ordered_batch_output_sha256','projection_sha256','engine_sha256')))


def probe(form,mins,report,total):
    if any(a[0]=='pair' for a in form.atoms):
        raise ValueError('probe reference requires unique primitive literals')
    p=PackedConditions(len(form.atoms)*2,3,form.m.shape[0])
    by_key={}
    for row in report:
        cols=row.get('_cols')
        if not cols:continue
        whole=[*cols,*form.fixed]
        if len(set(whole))!=len(whole):
            raise ValueError('probe reference requires unique primitive literals')
        q=tuple(cols[:-1]),cols[-1]^1
        code=p._encode(*q)
        if code in by_key:raise ValueError('duplicate report condition')
        by_key[code]=(q,row)
    for code,(q,row) in sorted(by_key.items(),key=lambda x:(len(x[1][0][0]),x[0])):
        p[q]=0
    t=stamp();lib=library();loader=seconds(t)
    t=stamp();prepared=PreparedValues(form);prepare=seconds(t)
    native=dict(wall_seconds=0.,cpu_seconds=0.)
    old=dict(wall_seconds=0.,cpu_seconds=0.)
    check=dict(wall_seconds=0.,cpu_seconds=0.)
    kinds=Counter();kept=Counter();cross=Counter()
    output=hashlib.sha256();batches=maxbytes=events=0
    iterator=prepared.iter_batches(p,batch_size=128)
    while True:
        t=stamp()
        try:b=next(iterator)
        except StopIteration:break
        dt=seconds(t)
        for k,v in dt.items():native[k]+=v
        chunk=p.empty_like()
        for code in b.keys:
            q,_=by_key[int(code)];chunk[q]=0
        t=stamp();want=reference(form,chunk);dt=seconds(t)
        for k,v in dt.items():old[k]+=v
        t=stamp()
        got=canonical([[np.full(len(b.keys),b.depth,dtype='u1'),b.keys.astype('u8'),
            b.kinds,b.single,b.multi,b.refuting,b.offsets,b.rows,b.columns,b.sparse_keys,b.sparse_counts]])
        dt=seconds(t)
        for k,v in dt.items():native[k]+=v
        t=stamp()
        for a,e in zip(got,want):np.testing.assert_array_equal(a,e)
        output.update(bytes.fromhex(digest(got)))
        for code,kind in zip(b.keys,b.kinds):
            label=KINDS[int(kind)];row=by_key[int(code)][1]
            kinds[label]+=1;cross[label+' / '+row['вердикт']]+=1
            if not row.get('свёрнута'):kept[label]+=1
        dt=seconds(t)
        for k,v in dt.items():check[k]+=v
        events+=len(b.rows);batches+=1;maxbytes=max(maxbytes,b.nbytes)
    assert sum(kinds.values())==len(p)
    return dict(scope='real sampled report, all verdicts with _cols; unique primitive reference; no verdict mutation',
        total_minimals=total if total is not None else len(mins),sampled_minimals=len(mins),
        report_rows=len(report),report_rows_without_cols=len(report)-len(p),classified=len(p),
        canonical_arrays_per_batch=11,exact_output=True,ordered_batch_output_sha256=output.hexdigest(),
        projection_sha256=prepared.context_sha256,
        atom_schema_sha256=hashlib.sha256(json.dumps(form.atoms,default=str,ensure_ascii=False).encode()).hexdigest(),
        engine_sha256=lib.source_hash,rows=prepared.nrows,literal_columns=prepared.ncols,
        kinds=dict(kinds),kept_kinds=dict(kept),kind_by_verdict=dict(cross),single_events=events,
        batches=batches,max_batch_result_bytes=maxbytes,budget_retries=prepared.budget_retries,
        loader=loader,prepare=prepare,native=native,reference=old,verification=check,
        timing_scope='both reference/native include canonical numeric assembly; checks/hash/cross-tab separate',
        production_speedup_claimed=False,sat_only_c_enabled=False)


def install():
    from algen import enumerate as E
    original=E._sample_stats
    def stats(form,mins,report,total):
        out=original(form,mins,report,total)
        out['контроль классификатора']=probe(form,mins,report,total)
        return out
    E._sample_stats=stats


def main():
    install()
    from algen import table
    raise SystemExit(table.main())


if __name__=='__main__':main()
