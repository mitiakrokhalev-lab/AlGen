"""Private paired two-view value-layer control; no raw report/SQLite export."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import pickle
import resource
import shutil
from copy import copy
import signal
import subprocess
import sys
import tempfile
import time


SOURCE_FILES = ('algen/frozen_theory.py','algen/row_knowledge.py','algen/value_ledger.py',
    'algen/value_classify.py','algen/native_values.cpp','tools/probe_shared_theory.py',
    'tools/probe_row_knowledge.py','tools/probe_value_ledger.py','tools/profile_memory.py',
    'algen/enumerate.py','algen/table.py','algen/native_enum.py','algen/native_enum.cpp',
    'algen/logic.py','algen/library.py','algen/fast.py','algen/compress.py',
    'algen/compress_base.py','algen/conditions.py','algen/live.py')


EXPECTED_INPUTS = {'library-cache/библиотека-40179479aa259919.pickle': 'f9ff096ab49a358ab67b31518d6dbb85f9e1a7d45c65d111e336a69ca4663e29', 'skel/G.skel.pickle': 'ceb398b85452b8ee995f7e4642e860803a8422778426ff8903d6705845a2f5bd', 'tables/G.1-20.pickle': '2ae08bdfe2200090dfc753363a8db3b6ef9d292d26b51607f404739af6b452e7', 'tables/G.10-20.pickle': '17f8bc21be0691cc8a5fec2b27c947393542038cf86c41ac718d430661c02d7a', 'tables/G.11-20.pickle': '2d7592340dc9012fccdfe6c2d20e91271002048f9b125a5b2912fc5da94caf15', 'tables/G.12-20.pickle': 'ed8bf0c14953f2a93139c937230ac1aa3e40913af3f664a3f98813b34cdcc304', 'tables/G.13-20.pickle': 'eb707800fc8fc9fb8722dc731258f6bc10e7784361ee8ace4375455abbdb9ba6', 'tables/G.14-20.pickle': '6f3248e83f356a9d4c9ffde6402928523889d1c413217e5576d76c8242aecdaa', 'tables/G.15-20.pickle': 'ab345f588b6be8c50506a0dee38e1dab4644a07022848821d49e40c4a3ed6ebe', 'tables/G.16-20.pickle': '1e4c1f1cda67fd1c908c7f620ec3c34904edea74431290828e20adcaf0e4459a', 'tables/G.17-20.pickle': '9055bcf25151eaea16ab5589fd8df38d3d4fd4376c7d48033c2a31f0e3cf91de', 'tables/G.18-20.pickle': '4a96deb147e51c9efdbfd269a95585dd274806c2540e9d5f2aa67e5aee752917', 'tables/G.19-20.pickle': '21bae685bf62bb698920b4a6fa2f61c7618e61c89999ff80770cdfdaf9f8e103', 'tables/G.2-20.pickle': '837d57802797fb568c683b817229183e30d7a56cdcc6a4821a3524ab500914b2', 'tables/G.20-20.pickle': '66e6dc6056c2c4c281250d636574673965871e2707718d190fe4ad450ca3d765', 'tables/G.3-20.pickle': '2a89d7fbb78689bb8fae219b1177af55bfe78be52ba5750f359299013440132f', 'tables/G.4-20.pickle': '2431bca408e607010260aae0a9fd31f4ba989d8628c1839c5ec4123003897949', 'tables/G.5-20.pickle': 'ddabd15cb47d9a6412be25dcc790f04d1a8426630127e70bf7d9bef71042cbc2', 'tables/G.6-20.pickle': '5faca632cce8780c73ac6b30f787d72a7af3934c51f6f8f7913cd10ec6b34315', 'tables/G.7-20.pickle': 'aca9c3f9159d3e8b1d3520ce2e2cfd4ab05993e82ab9479a518474b6e860360d', 'tables/G.8-20.pickle': '5cb5099bcb4f071dbcd33477d6328ab15c6c2546a84a0c22524f1a8b0a84e953', 'tables/G.9-20.pickle': 'd062b0680cab37fd8f91f5b887162ed1763227080b87205d0490d7e4c0ca3004', 'tables/G.rep.pickle': '1717ce8d8b2bc7fef02eecdc9b0fc92138db1e7e1ff295e1283dc01e7ff9ba5d'}

def sources():
    root = Path(__file__).resolve().parents[1]
    return {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in SOURCE_FILES}


def rss(pid):
    try:
        return {s.split(':',1)[0]:int(s.split()[1]) for s in Path(f'/proc/{pid}/status').read_text().splitlines()
                if s.startswith(('VmRSS:','VmHWM:'))}
    except (OSError,ValueError):return {}


def tree_rss(pid):
    pending,seen,total = [pid],set(),0
    while pending:
        p=pending.pop()
        if p in seen:continue
        seen.add(p);total+=rss(p).get('VmRSS',0)
        try:pending.extend(map(int,Path(f'/proc/{p}/task/{p}/children').read_text().split()))
        except (OSError,ValueError):pass
    return total


def input_hashes(a):
    result={}
    for label,root in (('skel',a.skel),('tables',a.tables),('library-cache',a.library_cache)):
        root=Path(root)
        paths=[root] if root.is_file() else sorted(root.rglob('*.pickle'))
        if not paths:raise ValueError('missing frozen input files: '+label)
        for path in paths:
            rel=path.name if root.is_file() else path.relative_to(root).as_posix()
            with path.open('rb') as stream:result[label+'/'+rel]=hashlib.file_digest(stream,'sha256').hexdigest()
    return result


def kill_group(pid,signum):
    try:os.killpg(pid,signum)
    except ProcessLookupError:pass


def valid_mode(x,mode,expected):
    import re
    if (not isinstance(x,dict) or mode not in ('separate','shared') or not isinstance(expected,dict)
            or set(expected)!=set(SOURCE_FILES) or any(not isinstance(h,str) or not re.fullmatch('[0-9a-f]{64}',h) for h in expected.values())):return False
    return (x.get('basis_mode')==mode and x.get('source_sha256')==expected
        and x.get('assertions_active') is True
        and x.get('census') is True and type(x.get('sample')) is int and x['sample']==0
        and x.get('state_save') is False and x.get('in_process') is True
        and x.get('native_enum') is True and x.get('native_minimal') is True
        and x.get('close_marked') is True and type(x.get('size')) is int and x['size']==2
        and type(x.get('max_premises')) is int and x['max_premises']==3)


def child(a):
    if not __debug__:
        raise RuntimeError('paired external oracles require active assertions')
    start = time.perf_counter(),time.process_time()
    from algen import enumerate as E,library,table,logic
    from algen.value_ledger import assignment
    from tools.probe_shared_theory import PairControl,valid_receipt
    from tools.probe_value_ledger import _elapsed
    library.CACHE=Path(a.library_cache).resolve()
    def read_only_library(vocab=None):
        # Same cache-hit path as built_library, with no rebuild/deletion fallback.
        path=library.CACHE/f'библиотека-{library._fingerprint()}.pickle'
        with path.open('rb') as stream:return pickle.load(stream)
    table.built_library=read_only_library
    out=Path(a.out)
    source_hashes=sources()
    stream=(out/'stages.jsonl').open('a',encoding='utf-8',buffering=1)
    def record(stage,**data):
        stream.write(json.dumps(dict(stage=stage,seconds=time.perf_counter()-start[0],memory_kib=rss(os.getpid()),**data),ensure_ascii=False)+'\n')
    actual=dict(basis_mode=a.basis_mode,source_sha256=source_hashes,assertions_active=__debug__,census=E.CENSUS,sample=E.SAMPLE,
        state_save=table.STATE_SAVE,in_process=table.IN_PROCESS,native_enum=E.NATIVE_ENUM,
        native_minimal=E.NATIVE_MINIMAL,close_marked=E.CLOSE_MARKED,size=table.SIZE,max_premises=3)
    if not valid_mode(actual,a.basis_mode,source_hashes):raise ValueError('unexpected child mode; no paired control')
    record('start',**actual)
    plan=list(zip(a.scheme.split(','),map(int,a.expected_counts.split(','))))
    pair=PairControl(Path(tempfile.mkdtemp(prefix='algen-basis-control-'))/'databases',a.basis_mode,plan)
    order={sid:i for i,(sid,n) in enumerate(plan)}
    pool,one,run=table._run_pool,table._one,E.run
    active_sid=None
    def ordered(jobs,*args,**kwargs):
        if len(jobs)!=2 or {j[1] for j in jobs}!=set(order):raise ValueError('two complete selected scheme jobs required')
        return pool(sorted(jobs,key=lambda j:order[j[1]]),*args,**kwargs)
    def tracked(job):
        nonlocal active_sid
        active_sid=job[1]
        record('scheme:start',sid=active_sid)
        try:return one(job)
        finally:record('scheme:end',sid=active_sid);active_sid=None
    language=hashlib.sha256((logic.DATA/'vocab'/'grp.json').read_bytes()).hexdigest()
    def controlled(*args,**kwargs):
        result=run(*args,**kwargs)
        form,conditions,empty,report=result
        if active_sid not in order or report or not args or type(args[0]) is not int or args[0]!=3:
            raise ValueError('expected complete census with three premises before individual verdicts')
        record('enumeration:complete',sid=active_sid,conditions=len(conditions),rows=len(form.m),columns=form.m.shape[1])
        manifest=dict(scheme=active_sid,library=table._fp('G'),language=language,
            theory='FrozenTheoryBasis view snapshot in probe',sources=source_hashes,source_table_run=43434101930,
            numeric_stage='all minimals before individual condition SAT')
        receipt=pair.consume(active_sid,form,conditions,[assignment(x) for x in form.envs],manifest,
            dict(kind='library',reference='existing projection from checked table build43434101930; '+table._fp('G')))
        record('value-view:complete',sid=active_sid,conditions=receipt['conditions'],state=receipt['state_hashes']['restored'])
        return result
    table._run_pool,table._one,E.run=ordered,tracked,controlled
    sys.argv=['table','перебор','G','--каталог',a.tables,'--выход',str(out/'results'),
              '--схемы',a.scheme,'--нитей','1','--посылок','3','--предел',str(a.seconds)]
    try:
        table.main()
        pair.seal_first_pass()
        first_pass=dict(**_elapsed(start),peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            scope='child entry before algen imports through both distinct views and basis cleanup; excludes fresh replay validation')
        record('first-value-pass:complete',**first_pass)
        receipt=pair.finish()
        if not valid_receipt(receipt):raise ValueError('invalid complete paired value control receipt')
        statuses={}
        for sid,n in plan:
            summary=json.loads((out/'results'/(sid+'.json')).read_text())
            statuses[sid]=dict(status=summary.get('статус'),minimals=summary.get('перепись',{}).get('минимальных'))
            if statuses[sid]!=dict(status='перепись',minimals=n):raise ValueError('actual full scheme summary differs from plan')
        receipt.update(first_value_pass=first_pass,scheme_statuses=statuses)
        (out/'paired-probe.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
        record('paired:verified',domains=2,classified=receipt['proof_pending'])
    finally:
        pair.abort()
        stream.close()


def run_mode(a):
    ids=a.scheme.split(',');counts=list(map(int,a.expected_counts.split(',')))
    out=Path(a.out);out.mkdir(parents=True,exist_ok=False)
    env={k:v for k,v in os.environ.items() if not k.startswith('ALGEN_')}
    env.update(PYTHONOPTIMIZE='0',ALGEN_SIZE='2',ALGEN_FAST='1',ALGEN_COMPRESS='1',ALGEN_STATE_SAVE='0',ALGEN_CENSUS='1',
        ALGEN_SAMPLE='0',ALGEN_SKEL=a.skel,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
    if getattr(a,'temporary_root',None):
        Path(a.temporary_root).mkdir(parents=True,exist_ok=True)
        env['TMPDIR']=a.temporary_root
        env['XDG_CACHE_HOME']=str(Path(a.temporary_root)/'cache')
    cmd=[sys.executable,'-B','-m','tools.profile_memory','--child','--tables',a.tables,'--skel',a.skel,
        '--library-cache',a.library_cache,'--scheme',a.scheme,'--out',a.out,'--expected-counts',a.expected_counts,
        '--basis-mode',a.basis_mode,'--seconds',str(a.seconds),'--rss-gib',str(a.rss_gib),'--no-state-save','--shared-theory-probe']
    audit_start=time.perf_counter(),time.process_time()
    before_inputs=input_hashes(a)
    if before_inputs!=EXPECTED_INPUTS:raise ValueError('frozen source inputs differ from independently verified control')
    input_before=dict(wall_seconds=time.perf_counter()-audit_start[0],cpu_seconds=time.process_time()-audit_start[1])
    start=time.monotonic();reason='exited';sampled=0;tree_peak=0;monitored_peak=0;usage=None
    with (out/'process.log').open('wb') as log,(out/'rss.jsonl').open('w') as trace:
        proc=subprocess.Popen(cmd,cwd=getattr(a,'execution_py_root',Path(__file__).resolve().parents[1]),env=env,stdout=log,stderr=log,start_new_session=True)
        try:
            stopping=None
            while True:
                pid,status,observed=os.wait4(proc.pid,os.WNOHANG)
                if pid:
                    usage=observed;proc.returncode=os.waitstatus_to_exitcode(status);break
                elapsed=time.monotonic()-start
                memory=rss(proc.pid);sampled=max(sampled,memory.get('VmRSS',0))
                total=tree_rss(proc.pid);tree_peak=max(tree_peak,total)
                monitored=total+rss(os.getpid()).get('VmRSS',0);monitored_peak=max(monitored_peak,monitored)
                trace.write(json.dumps(dict(seconds=elapsed,child=memory,tree_rss_kib=total,tree_plus_parent_rss_kib=monitored))+'\n');trace.flush()
                if stopping is None and (elapsed>a.seconds or monitored>a.rss_gib*1024**2 or time.monotonic()>getattr(a,'deadline',float('inf'))):
                    reason='time_budget' if elapsed>a.seconds or time.monotonic()>getattr(a,'deadline',float('inf')) else 'rss_budget'
                    stopping=time.monotonic();kill_group(proc.pid,signal.SIGTERM)
                elif stopping is not None and time.monotonic()-stopping>10 and ':forced_kill' not in reason:
                    reason+=':forced_kill';kill_group(proc.pid,signal.SIGKILL)
                time.sleep(.25)
        finally:
            if proc.returncode is None:
                kill_group(proc.pid,signal.SIGKILL)
                pid,status,usage=os.wait4(proc.pid,0);proc.returncode=os.waitstatus_to_exitcode(status)
            kill_group(proc.pid,signal.SIGKILL)  # no leftover compiler descendants
    result=dict(version=1,scheme=a.scheme,basis_mode=a.basis_mode,returncode=proc.returncode,stop_reason=reason,
        wall_seconds=time.monotonic()-start,cpu_seconds=usage.ru_utime+usage.ru_stime,peak_rss_kib=usage.ru_maxrss,
        sampled_child_rss_kib=sampled,sampled_tree_rss_kib=tree_peak,sampled_tree_plus_parent_rss_kib=monitored_peak,
        limits=dict(seconds=a.seconds,rss_gib=a.rss_gib,rss_scope='polled sum of child process tree plus parent RSS; shared pages may be counted twice'),
        expected_cases=[list(x) for x in zip(ids,counts)],code_sha256=sources(),complete=False,
        scope='paired first pass of experimental value layer, not production report')
    try:
        audit_start=time.perf_counter(),time.process_time()
        after_inputs=input_hashes(a)
        result['input_files_sha256']=before_inputs
        result['input_files_unchanged']=before_inputs==after_inputs
        result['input_audit_before_child']=input_before
        result['input_audit_after_child']=dict(wall_seconds=time.perf_counter()-audit_start[0],cpu_seconds=time.process_time()-audit_start[1])
        from tools.probe_shared_theory import valid_receipt
        r=json.loads((out/'paired-probe.json').read_text())
        stages=[json.loads(s) for s in (out/'stages.jsonl').read_text().splitlines()]
        actual=next((s for s in stages if s.get('stage')=='start'),{})
        result['actual_mode']=actual
        result['mode_verified']=valid_mode(actual,a.basis_mode,result['code_sha256'])
        result['paired_probe_valid']=valid_receipt(r) and r['mode']==a.basis_mode and r['expected_cases']==result['expected_cases']
        summaries={sid:json.loads((out/'results'/(sid+'.json')).read_text()) for sid in ids}
        result['scheme_statuses']={sid:s.get('статус') for sid,s in summaries.items()}
        counts_valid=all(type(s.get('перепись',{}).get('минимальных')) is int and s['перепись']['минимальных']==n
            and s.get('статус')=='перепись' for (sid,n),s in zip(zip(ids,counts),(summaries[x] for x in ids)))
        phase=r.get('first_value_pass',{})
        phase_valid=(isinstance(phase,dict) and all(type(phase.get(k)) in (int,float) and math.isfinite(phase[k]) and 0<=phase[k]<=result['wall_seconds']+1
            for k in ('wall_seconds',)) and type(phase.get('cpu_seconds')) in (int,float) and phase['cpu_seconds']>=0
            and math.isfinite(phase['cpu_seconds']) and type(phase.get('peak_rss_kib')) is int and phase['peak_rss_kib']>0)
        result['paired_probe']=r
        result['complete']=(reason=='exited' and proc.returncode==0 and result['mode_verified'] and result['paired_probe_valid']
            and counts_valid and phase_valid and result['input_files_unchanged'])
    except (OSError,ValueError,TypeError,KeyError,AttributeError) as e:
        result['validation_error']=str(e)
    (out/'measurement.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    return result


def run_both(a):
    out=Path(a.out);out.mkdir(parents=True,exist_ok=False)
    start=time.monotonic();cpu=time.process_time();measurements={};failures={};setups={}
    repo=Path(__file__).resolve().parents[2]
    for mode in ('separate','shared'):
        if time.monotonic()-start>=a.seconds:
            failures[mode]='not started: total paired deadline';break
        if mode == 'shared' and (failures.get('separate') or not measurements.get('separate',{}).get('complete')):
            failures[mode]='not started: separate mode incomplete or raised';break
        t=time.monotonic();tcpu=time.process_time()
        # Both child processes compile in fresh independent locations. Copying
        # source and symlinking frozen data does not reuse a completed scheme.
        clone=Path(tempfile.mkdtemp(prefix='algen-basis-'+mode+'-'))
        shutil.copytree(repo/'py',clone/'py',ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.so','*.o'))
        (clone/'data').symlink_to(repo/'data',target_is_directory=True)
        setups[mode]=dict(wall_seconds=time.monotonic()-t,cpu_seconds=time.process_time()-tcpu)
        config=copy(a);config.basis_mode=mode;config.out=str(out/mode)
        config.execution_py_root=clone/'py';config.temporary_root=str(clone/'tmp')
        config.seconds=max(1,a.seconds//2);config.deadline=start+a.seconds
        try:measurements[mode]=run_mode(config)
        except Exception as e:failures[mode]=type(e).__name__+': '+str(e)
    complete=(not failures and set(measurements)=={'separate','shared'}
        and all(m.get('complete') is True for m in measurements.values()))
    equal=False
    if complete:
        left,right=measurements['separate'],measurements['shared']
        equal=(left['code_sha256']==right['code_sha256']
            and left['input_files_sha256']==right['input_files_sha256']
            and [c['canonical_output_sha256'] for c in left['paired_probe']['cases']]
                ==[c['canonical_output_sha256'] for c in right['paired_probe']['cases']])
    result=dict(version=1,scope='same-runner paired first pass of experimental value layer; not production report',
        complete=complete and equal,canonical_outputs_equal=equal,same_parent_and_runner=True,
        fresh_isolated_source_and_compiler_cache_per_mode=True,scheme=a.scheme,mode_measurements=measurements,
        failures=failures,source_copy_setup=setups,parent_total_wall_seconds=time.monotonic()-start,
        parent_cpu_seconds=time.process_time()-cpu,
        cpu_model=next((x.split(':',1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')),None),
        mem_total_kib=rss_memory_total(),limits=dict(total_seconds=a.seconds,per_mode_child_seconds=max(1,a.seconds//2),rss_gib=a.rss_gib))
    (out/'measurement.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    return result


def rss_memory_total():
    return next((int(x.split()[1]) for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemTotal:')),None)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('tables','skel','library-cache','scheme','out','expected-counts'):
        p.add_argument('--'+name,required=True)
    p.add_argument('--basis-mode',required=True,choices=('separate','shared','both'))
    p.add_argument('--seconds',type=int,default=1200)
    p.add_argument('--rss-gib',type=float,default=14.)
    p.add_argument('--no-state-save',action='store_true')
    p.add_argument('--shared-theory-probe',action='store_true')
    p.add_argument('--child',action='store_true',help=argparse.SUPPRESS)
    a=p.parse_args()
    try:
        ids=a.scheme.split(',');counts=list(map(int,a.expected_counts.split(',')))
        valid=(len(ids)==len(set(ids))==len(counts)==2 and all(x.startswith('G-') for x in ids)
            and all(0<n<=10000 for n in counts) and a.seconds>1 and 0<a.rss_gib<=15
            and a.no_state_save and a.shared_theory_probe and not (a.child and a.basis_mode=='both'))
    except ValueError:valid=False
    if not valid:p.error('two complete distinct G domains, counts, explicit probe/no-state-save and finite positive limits required')
    if a.child:
        child(a);return
    for name in ('tables','skel','library_cache','out'):setattr(a,name,str(Path(getattr(a,name)).resolve()))
    result=run_both(a) if a.basis_mode=='both' else run_mode(a)
    print(json.dumps(result,ensure_ascii=False))


if __name__=='__main__':main()
