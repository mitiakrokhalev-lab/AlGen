"""Bounded exact value classification, independent of Theory/SAT verdicts.

C=0, A=1, B=2, R=3 (a current Library refutation). Positive pair columns
expand into signed primitive columns; duplicates collapse. Negated pairs and
contradictory forbidden conjunctions fail explicitly. Events are ordered by
condition, then Library row; sparse counters include only conditions of kind A.
No production report/Archive integration and no CAP/KEEP approximation.
"""

import ctypes as C
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import sysconfig
import tempfile

import numpy as np


KINDS = ('C','A','B','R')
_library = None


class ValueBudgetExceeded(RuntimeError):
    """The bounded batch did not complete; no partial classification is valid."""


def library():
    global _library
    if _library is not None:
        return _library
    compiler = shutil.which('g++')
    header = Path(sysconfig.get_path('include'))
    if sys.byteorder!='little' or not sys.platform.startswith('linux') or compiler is None or not (header/'Python.h').is_file():
        raise RuntimeError('native values require Linux, a C++ compiler and Python headers')
    source = Path(__file__).with_name('native_values.cpp')
    flags = ['-std=c++17','-O3','-shared','-fPIC']
    version = subprocess.check_output([compiler,'--version'],text=True,timeout=10).splitlines()[0]
    source_hash = hashlib.sha256(source.read_bytes()+repr((sysconfig.get_config_var('SOABI'),version,flags)).encode()).hexdigest()
    cache = Path(tempfile.gettempdir())/('algen-values-'+str(os.getuid()))
    cache.mkdir(mode=0o700,exist_ok=True)
    info = cache.stat()
    if info.st_uid!=os.getuid() or info.st_mode & 0o022:
        raise OSError('unsafe native values cache permissions')
    target = cache/(source_hash[:24]+'.so')
    if not target.exists():
        with tempfile.TemporaryDirectory(prefix='build-',dir=cache) as tmp:
            output = Path(tmp)/'values.so'
            subprocess.run([compiler,*flags,'-I'+str(header),str(source),'-o',str(output)],
                           check=True,capture_output=True,timeout=55)
            os.replace(output,target)
    lib = C.PyDLL(str(target))
    lib.algen_values.restype = C.c_int
    lib.algen_values.argtypes = [C.c_int,C.c_size_t,C.c_void_p,C.c_int,C.c_int,C.c_int,
        C.c_void_p,C.c_size_t,C.c_void_p,C.c_size_t,C.c_void_p,C.c_void_p,C.c_size_t,C.POINTER(C.c_void_p)]
    lib.algen_values_size.argtypes = [C.c_void_p,C.c_int]
    lib.algen_values_size.restype = C.c_size_t
    lib.algen_values_data.argtypes = [C.c_void_p,C.c_int]
    lib.algen_values_data.restype = C.c_void_p
    lib.algen_values_free.argtypes = [C.c_void_p]
    lib.algen_values_free.restype = None
    lib.source_hash = source_hash
    _library = lib
    return lib


def primitive_expansions(form):
    atoms = tuple(form.atoms)
    index = {a:i for i,a in enumerate(atoms)}
    if len(index)!=len(atoms):
        raise ValueError('duplicate atom descriptors')
    pairs = getattr(form,'pair_atoms',{}) or {}
    if set(pairs)!={i for i,a in enumerate(atoms) if a[0]=='pair'}:
        raise ValueError('pair metadata does not match atoms')
    out = []
    for i,a in enumerate(atoms):
        if a[0]=='pair':
            if len(a)!=5 or type(a[4]) is not bool:
                raise ValueError('invalid pair descriptor')
            _,prop,x,y,pol = a
            try:
                components = (index[('p',prop,x)],index[('p',prop,y)])
            except KeyError as exc:
                raise ValueError('missing primitive pair components') from exc
            if set(components)!=set(pairs[i]):
                raise ValueError('pair components do not match descriptor')
            out.extend((tuple(2*c+(0 if pol else 1) for c in components),()))
        elif a[0] in ('p','r'):
            out.extend(((2*i,),(2*i+1,)))
        else:
            raise ValueError('unsupported atom descriptor')
    return tuple(out)


@dataclass
class ValueBatch:
    depth: int
    width: int
    start: int
    keys: np.ndarray
    kinds: np.ndarray
    single: np.ndarray
    multi: np.ndarray
    refuting: np.ndarray
    offsets: np.ndarray
    rows: np.ndarray
    columns: np.ndarray
    sparse_keys: np.ndarray
    sparse_counts: np.ndarray
    context_sha256: str
    engine_sha256: str

    @property
    def nbytes(self):
        return sum(a.nbytes for a in (self.keys,self.kinds,self.single,self.multi,self.refuting,
            self.offsets,self.rows,self.columns,self.sparse_keys,self.sparse_counts))


class PreparedValues:
    """Immutable packed Library projection + literal expansions for many batches.

    This context hash names the projection, fixed facts and primitive mappings.
    Cross-scheme identities/Archive persistence are a separate integration step.
    """
    def __init__(self,form):
        self.nrows,self.ncols = map(int,form.m.shape)
        if not 0<self.ncols<2**31 or self.ncols%2 or self.nrows<0 or self.nrows>(2**64-1)//self.ncols:
            raise ValueError('invalid Library dimensions')
        self.expansions = primitive_expansions(form)
        if len(self.expansions)!=self.ncols:
            raise ValueError('atom/matrix width mismatch')
        fixed = list(form.fixed)
        if any(type(j) not in (int,np.int32,np.int64) or not 0<=j<self.ncols for j in fixed):
            raise ValueError('invalid fixed column')
        self.fixed = np.array(fixed,dtype=np.int32)
        words = max(1,(self.nrows+63)//64)
        # Form._bits caches by matrix identity. Repack a fresh snapshot so an
        # in-place Library correction cannot silently reuse stale bit values.
        packed = np.packbits(form.m,axis=0,bitorder='little')
        self.P = np.zeros((self.ncols,words),dtype=np.uint64)
        self.P.view(np.uint8)[:,:len(packed)] = packed.T
        self.P[:,-1] &= np.uint64((1<<(self.nrows%64))-1 if self.nrows%64 else (2**64-1 if self.nrows else 0))
        primitives = [2*i for i,a in enumerate(form.atoms) if a[0]!='pair']
        for j in primitives:
            if np.any(self.P[j]&self.P[j+1]):
                raise ValueError('contradictory primitive Library values')
        offsets,values = [0],[]
        for columns in self.expansions:
            values.extend(columns)
            offsets.append(len(values))
        if len(values)>=2**31:
            raise ValueError('literal expansion too large')
        self.offsets = np.array(offsets,dtype=np.int32)
        self.values = np.array(values,dtype=np.int32)
        digest = hashlib.sha256(json.dumps([self.nrows,self.ncols,self.expansions,fixed],sort_keys=True).encode())
        digest.update(memoryview(self.P))
        self.context_sha256 = digest.hexdigest()
        for a in (self.P,self.fixed,self.offsets,self.values):
            a.setflags(write=False)
        self.budget_retries = 0

    def classify(self,keys,depth,width,max_events=262144,start=0):
        if type(depth) is not int or not 0<=depth<=3 or type(width) is not int or not 0<width<32:
            raise ValueError('invalid packed condition dimensions')
        if width*(depth+1)+1>64 or self.ncols>1<<width:
            raise ValueError('packed condition width is insufficient')
        if type(max_events) is not int or not 0<=max_events<2**63:
            raise ValueError('invalid value-event budget')
        keys = np.asarray(keys)
        if keys.ndim!=1 or keys.dtype.kind!='u' or keys.dtype.itemsize not in (1,2,4,8):
            raise ValueError('keys need a one-dimensional unsigned array')
        keys = np.ascontiguousarray(keys,dtype=keys.dtype.newbyteorder('='))
        lib = library()
        handle = C.c_void_p()
        arrays = []
        try:
            try:
                status = lib.algen_values(self.ncols,self.nrows,self.P.ctypes.data,width,depth,keys.dtype.itemsize,
                    keys.ctypes.data,len(keys),self.fixed.ctypes.data,len(self.fixed),
                    self.offsets.ctypes.data,self.values.ctypes.data,max_events,C.byref(handle))
            except OverflowError as exc:
                raise ValueBudgetExceeded(str(exc)) from exc
            if status!=0 or not handle.value:
                raise RuntimeError('native value classification returned no result')
            for kind,dtype in enumerate(('u1','u8','u8','u8','u8','u8','i4','u8','u8')):
                size = lib.algen_values_size(handle,kind)
                if size:
                    item = np.dtype(dtype).itemsize
                    ptr = lib.algen_values_data(handle,kind)
                    raw = (C.c_ubyte*(size*item)).from_address(ptr)
                    arrays.append(np.frombuffer(raw,dtype=dtype).copy())
                else:
                    arrays.append(np.empty(0,dtype=dtype))
        finally:
            if handle.value:
                lib.algen_values_free(handle)
        if (any(len(a)!=len(keys) for a in arrays[:4]) or len(arrays[4])!=len(keys)+1
                or arrays[4][-1]!=len(arrays[5]) or len(arrays[5])!=len(arrays[6])
                or len(arrays[7])!=len(arrays[8])):
            raise RuntimeError('native values output dimensions differ')
        return ValueBatch(depth,width,start,keys.copy(),*arrays,self.context_sha256,lib.source_hash)

    def iter_batches(self,conditions,batch_size=4096,max_events=262144):
        if type(batch_size) is not int or batch_size<1 or conditions.literals!=self.ncols:
            raise ValueError('invalid batch size or condition vocabulary')
        for depth,(codes,supports) in conditions.blocks.items():
            keys = np.asarray(codes)
            start = 0
            while start<len(keys):
                size = min(batch_size,len(keys)-start)
                while True:
                    try:
                        result = self.classify(keys[start:start+size],depth,conditions.width,max_events,start)
                        break
                    except ValueBudgetExceeded:
                        self.budget_retries += 1
                        if size==1:
                            raise
                        size = max(1,size//2)
                yield result
                start += size
