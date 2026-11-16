"""Resumable exact scheme inventory; no Library/theory/table/task enumeration.

One bounded child per base. Completed same-context files are validated and
reused. Incomplete attempts and logs remain on disk; unknown counts stay null.
"""

import argparse
import ctypes
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import shutil
import subprocess
import sys
import time
import uuid


def atomic(path,value):
    temp = path.with_name(path.name+'.tmp')
    temp.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
    temp.replace(path)


def inputs():
    root = Path(__file__).resolve().parents[2]
    paths = sorted([*root.joinpath('py/algen').glob('*.py'),*root.joinpath('data').rglob('*')])
    h = hashlib.sha256()
    for p in [Path(__file__),*paths]:
        if p.is_file():
            h.update(str(p.relative_to(root)).encode()+b'\0')
            h.update(hashlib.sha256(p.read_bytes()).digest())
    return h.hexdigest()


def arm_parent(parent_pid):
    """Linux: no heavy work after parent death, including the startup race."""
    if parent_pid is None or os.getppid()!=parent_pid:
        raise RuntimeError('planner parent is gone')
    libc = ctypes.CDLL(None,use_errno=True)
    if libc.prctl(1,signal.SIGTERM,0,0,0)!=0:  # PR_SET_PDEATHSIG
        raise OSError(ctypes.get_errno(),'cannot arm parent-death signal')
    if os.getppid()!=parent_pid:
        raise RuntimeError('planner parent died during startup')


def stop_child(proc):
    if proc is not None and proc.poll() is None:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()


def process_identity(pid):
    try:
        rest = Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()
        return dict(state=rest[0],birth=rest[19])
    except (FileNotFoundError,ProcessLookupError):
        return None


def recover_attempts(result):
    for row in result['bases'].values():
        for attempt in row['attempts']:
            if attempt.get('status') not in ('starting','running'):
                continue
            pid = attempt.get('pid')
            identity = process_identity(pid) if pid else None
            if identity and identity['state']!='Z' and identity['birth']==attempt.get('birth'):
                raise RuntimeError('previous planner child still alive; wait for its own deadline before resuming')
            attempt.update(status='interrupted',stop_reason='parent_interrupted_unknown_cost')
            row.update(status='interrupted',complete=False,schemes=None)


def validate(path,expected):
    """CRC/JSON, count, unique IDs and both canonical hashes, streaming rows."""
    plan,raw,seen = hashlib.sha256(b'['),hashlib.sha256(),set()
    with gzip.open(path,'rb') as stream:
        for line in stream:
            item = json.loads(line)
            if (not isinstance(item,list) or len(item)!=2 or not isinstance(item[0],str)
                or not isinstance(item[1],list) or not all(isinstance(t,str) for t in item[1])
                or item[0] in seen or not (item[0]==expected['base'] or item[0].startswith(expected['base']+'-'))):
                raise ValueError('invalid/duplicate scheme')
            data = json.dumps(item,ensure_ascii=False).encode()
            if line!=data+b'\n':
                raise ValueError('noncanonical manifest row')
            plan.update((b', ' if seen else b'')+data)
            raw.update(line)
            seen.add(item[0])
    plan.update(b']')
    if len(seen)!=expected['schemes'] or plan.hexdigest()!=expected['plan_sha256'] or raw.hexdigest()!=expected['jsonl_sha256']:
        raise ValueError('manifest count/hash mismatch')
    return len(seen)


def validate_completed(root,result):
    result.update(complete=False,total_schemes=None)
    for base,row in result['bases'].items():
        if row['status']=='complete':
            try:
                if row.get('base')!=base:
                    raise ValueError('base key/receipt mismatch')
                validate(root/row['directory']/'schemes.jsonl.gz',row)
            except (ValueError,OSError,EOFError) as exc:
                row.setdefault('validation_failures',[]).append(dict(directory=row['directory'],error=str(exc)))
                row.update(status='invalid_or_error',complete=False,schemes=None,error=str(exc))


def child(base,directory,context):
    from algen import table as T
    if inputs()!=context['inputs']:
        raise ValueError('inputs changed before child start')
    start,cpu = time.perf_counter(),time.process_time()
    v = T.Vocab.section('grp')
    universe = T.universe
    stage = {}
    def measured(*args,**kw):
        atomic(directory/'progress.json',dict(stage='universe',elapsed_seconds=time.perf_counter()-start))
        a = time.perf_counter()
        terms = universe(*args,**kw)
        stage.update(universe_seconds=time.perf_counter()-a,universe_terms=len(terms))
        atomic(directory/'progress.json',dict(stage='schemes',elapsed_seconds=time.perf_counter()-start,**stage))
        return terms
    T.universe = measured
    schemes = T.schemes(v,base,3)
    generation = time.perf_counter()-start
    plan,raw = hashlib.sha256(b'['),hashlib.sha256()
    path = directory/'schemes.jsonl.gz'
    with path.open('xb') as output, gzip.GzipFile(filename='',fileobj=output,mode='wb',mtime=0) as stream:
        for i,item in enumerate(schemes):
            data = json.dumps(item,ensure_ascii=False).encode()
            plan.update((b', ' if i else b'')+data)
            raw.update(data+b'\n')
            stream.write(data+b'\n')
            if i%1000==0 and shutil.disk_usage(directory).free<32*1024**2:
                raise OSError('disk reserve32MiB exhausted')
    plan.update(b']')
    result = dict(base=base,complete=True,schemes=len(schemes),plan_sha256=plan.hexdigest(),jsonl_sha256=raw.hexdigest(),
        generation_seconds=generation,wall_seconds=time.perf_counter()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,**stage)
    atomic(directory/'result.json',result)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',required=True)
    p.add_argument('--bases',nargs='+')
    p.add_argument('--seconds',type=float,default=30)
    p.add_argument('--rss-mib',type=float,default=1536)
    p.add_argument('--address-mib',type=float,default=3072)
    p.add_argument('--legacy',action='store_true')
    p.add_argument('--child')
    p.add_argument('--parent-pid',type=int)
    a = p.parse_args()
    os.environ.update(ALGEN_SIZE='2',ALGEN_FAST='1',ALGEN_TYPED_UNIVERSE='0' if a.legacy else '1',OPENBLAS_NUM_THREADS='1')
    if a.child:
        arm_parent(a.parent_pid)
        limit = int(a.address_mib*1024**2)
        resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
        def expired(*_):
            raise TimeoutError('child wall budget')
        signal.signal(signal.SIGALRM,expired)
        signal.setitimer(signal.ITIMER_REAL,a.seconds)
    from algen import table as T
    if T.CLASS:
        p.error('this inventory is the unqualified k<=3/s<=2 class')
    root = Path(a.out).resolve()
    if a.child:
        context = json.loads((root.parent.parent/'manifest.json').read_text())['context']
        child(a.child,root,context)
        return
    selected = a.bases or list(T.BASES)
    if len(set(selected))!=len(selected) or set(selected)-set(T.BASES) or min(a.seconds,a.rss_mib,a.address_mib)<=0:
        p.error('invalid bases or budgets')
    root.mkdir(parents=True,exist_ok=True)
    lock = (root/'manifest.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    context = dict(inputs=inputs(),size=2,k=3,qualified_class='',typed_universe=not a.legacy,all_bases=list(T.BASES))
    path = root/'manifest.json'
    if path.exists():
        result = json.loads(path.read_text())
        if result['context']!=context or set(result['bases'])!=set(T.BASES):
            p.error('context changed; preserve this directory and choose a new one')
    else:
        result = dict(version=1,scope='exact scheme inventory only; no task enumeration or24h forecast',context=context,
            bases={b:dict(status='not_attempted',schemes=None,attempts=[]) for b in T.BASES},complete=False,total_schemes=None)
    result.update(complete=False,total_schemes=None,stop_reason=None)
    atomic(path,result)  # invalidate BEFORE rechecking or changing any result
    recover_attempts(result)
    validate_completed(root,result)
    atomic(path,result)
    for base in selected:
        row = result['bases'][base]
        if row['status']=='complete':
            print(base,'reused',row['schemes'],flush=True)
            continue
        if shutil.disk_usage(root).free<40*1024**2:
            result['stop_reason']='disk_reserve40MiB'
            break
        directory = root/base/uuid.uuid4().hex[:12]
        directory.mkdir(parents=True)
        command = [sys.executable,'-B','-m','tools.build_scheme_manifest','--out',str(directory),'--child',base,
                   '--seconds',str(a.seconds),'--address-mib',str(a.address_mib),'--parent-pid',str(os.getpid())]
        if a.legacy:
            command.append('--legacy')
        start = time.perf_counter()
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        peak,reason = 0,None
        attempt = dict(status='starting',directory=str(directory.relative_to(root)),pid=None,birth=None,
            started_unix=time.time(),returncode=None,parent_wall_seconds=None,child_cpu_seconds=None,
            limit_seconds=a.seconds,limit_rss_mib=a.rss_mib,child_address_limit_mib=a.address_mib)
        row['attempts'].append(attempt)
        row.update(status='running',complete=False,schemes=None)
        atomic(path,result)  # registered BEFORE Popen; unknown costs are null
        with (directory/'log.txt').open('x') as log:
            proc = None
            try:
                proc = subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,env=os.environ,cwd=Path(__file__).resolve().parents[1])
                identity = process_identity(proc.pid)
                attempt.update(status='running',pid=proc.pid,birth=identity['birth'] if identity else None)
                atomic(path,result)
                while proc.poll() is None:
                    try:
                        lines = Path(f'/proc/{proc.pid}/status').read_text().splitlines()
                        rss = next((int(s.split()[1]) for s in lines if s.startswith('VmRSS:')),0)
                        peak = max(peak,rss)
                    except (FileNotFoundError,ProcessLookupError):
                        pass
                    if peak>a.rss_mib*1024:
                        reason='rss_budget'
                    elif time.perf_counter()-start>a.seconds:
                        reason='time_budget'
                    if reason:
                        break
                    time.sleep(.05)
            except BaseException as exc:
                reason='parent_interrupted'
                attempt.update(status='interrupted',error=type(exc).__name__)
                row.update(status='interrupted',complete=False,schemes=None)
                atomic(path,result)
                raise
            finally:
                stop_child(proc)
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        if not reason:
            reason={124:'time_budget',125:'address_space_budget'}.get(proc.returncode)
        attempt.update(status='finished',returncode=proc.returncode,stop_reason=reason,
            parent_wall_seconds=time.perf_counter()-start,child_cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
            sampled_peak_rss_kib=peak)
        try:
            if reason or proc.returncode!=0:
                raise ValueError(reason or 'child_error')
            done = json.loads((directory/'result.json').read_text())
            if done['base']!=base or done.get('complete') is not True:
                raise ValueError('wrong/incomplete child receipt')
            validate(directory/'schemes.jsonl.gz',done)
            row.update(done,status='complete',directory=attempt['directory'])
            row.pop('error',None)
        except (ValueError,OSError,EOFError) as exc:
            attempt['error']=str(exc)
            row.update(status=reason or 'invalid_or_error',complete=False,schemes=None,error=str(exc))
        atomic(path,result)
        print(base,row['status'],row['schemes'],flush=True)
    if inputs()!=context['inputs']:
        raise ValueError('inputs changed during inventory; do not declare complete')
    validate_completed(root,result)
    result['complete']=all(r['status']=='complete' for r in result['bases'].values())
    result['total_schemes']=sum(r['schemes'] for r in result['bases'].values()) if result['complete'] else None
    result['completed_bases']=sum(r['status']=='complete' for r in result['bases'].values())
    atomic(path,result)
    print(json.dumps({k:result[k] for k in ('complete','completed_bases','total_schemes')}),flush=True)


if __name__=='__main__':
    try:
        main()
    except TimeoutError:
        print('child_time_budget',file=sys.stderr)
        raise SystemExit(124)
    except MemoryError:
        print('child_address_space_budget',file=sys.stderr)
        raise SystemExit(125)
