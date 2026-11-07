"""Compiled numeric enumeration, with an unchanged Python fallback.

No changes to vocabulary/Library fingerprints. A PyDLL call holds the GIL;
the kernel polls PyErr_CheckSignals so existing Python scheme timeouts work.
"""

from array import array
import ctypes as C
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import sysconfig
import tempfile

import numpy as np

_library = None
_unavailable = None


def library():
    global _library, _unavailable
    if _library is not None:
        return _library
    if _unavailable is not None:
        return None
    compiler = shutil.which("g++")
    header = Path(sysconfig.get_path("include"))
    if (not sys.platform.startswith("linux") or sys.byteorder != "little"
            or compiler is None or not (header / "Python.h").is_file()):
        _unavailable = "Linux C++ compiler/Python headers unavailable"
        return None
    source = Path(__file__).with_suffix(".cpp")
    flags = ["-std=c++17", "-O3", "-shared", "-fPIC"]
    try:
        version = subprocess.check_output([compiler, "--version"], text=True, timeout=10).splitlines()[0]
        key = hashlib.sha256(source.read_bytes() + repr((sysconfig.get_config_var("SOABI"), version, flags)).encode()).hexdigest()[:24]
        cache = Path(tempfile.gettempdir()) / ("algen-native-" + str(os.getuid()))
        cache.mkdir(mode=0o700, exist_ok=True)
        info = cache.stat()
        if info.st_uid != os.getuid() or info.st_mode & 0o022:
            raise OSError("unsafe native cache permissions")
        target = cache / (key + ".so")
        if not target.exists():
            with tempfile.TemporaryDirectory(prefix="build-", dir=cache) as tmp:
                output = Path(tmp) / "enum.so"
                subprocess.run([compiler, *flags, "-I" + str(header), str(source), "-o", str(output)],
                               check=True, capture_output=True, timeout=55)
                os.replace(output, target)
        lib = C.PyDLL(str(target))
        lib.algen_enum.restype = C.c_void_p
        lib.algen_enum.argtypes = [C.c_int, C.c_int, C.c_int, C.c_uint64, C.c_int, C.c_int,
                                  C.c_void_p, C.c_size_t, C.c_void_p, C.c_size_t] + [C.c_void_p] * 10
        lib.algen_count.argtypes = [C.c_void_p]
        lib.algen_count.restype = C.c_uint64
        lib.algen_size.argtypes = [C.c_void_p, C.c_int, C.c_int]
        lib.algen_size.restype = C.c_size_t
        lib.algen_data.argtypes = [C.c_void_p, C.c_int, C.c_int]
        lib.algen_data.restype = C.POINTER(C.c_uint64)
        lib.algen_free.argtypes = [C.c_void_p]
        lib.algen_free.restype = None
        lib.algen_minimal.restype = C.c_void_p
        lib.algen_minimal.argtypes = [C.c_int, C.c_int, C.c_void_p, C.c_void_p, C.c_void_p]
        lib.source_hash = key
        _library = lib
    except (OSError, subprocess.SubprocessError) as e:
        _unavailable = str(e)
    return _library


def enumerate_numeric(alive, P0, pall, selected, goal_mask, skip, have0,
                      req, reqcols, clash, coverage, full, prune, relations, props_from):
    """Return (packed alive, list empty, count), or None before starting native.

    Bounds are checked before C++. Numerical arrays remain live for the call;
    native output is copied into independent arrays before its handle is freed.
    """
    n, k = alive.literals, alive.max_premises
    if (not 0 < n < 2**31 or n % 2 or not 0 <= k <= 3
            or alive.width * (k + 1) + 1 > 64 or not 0 <= full < 2**63
            or not -(2**31) <= props_from < 2**31):
        return None
    if any(not 0 <= a < n//2 or any(not 0 <= j < n for j in values) for a, values in req.items()):
        return None
    if any(not 0 <= a < n//2 or any(not 0 <= b < n//2 for b in others) for a, others in clash.items()):
        return None
    lib = library()
    if lib is None:
        return None
    offsets, values, clash_offsets, clash_values = [0], [], [0], []
    for a in range(n//2):
        values.extend(sorted(req.get(a, ())))
        offsets.append(len(values))
        clash_values.extend(sorted(clash.get(a, ())))
        clash_offsets.append(len(clash_values))
    if max(len(values), len(clash_values)) >= 2**31:
        return None
    arrays = [np.ascontiguousarray(pall, dtype=np.uint64), np.ascontiguousarray(P0, dtype=np.uint64),
              np.ascontiguousarray(coverage, dtype=np.uint64), np.ascontiguousarray(goal_mask, dtype=np.uint8),
              np.ascontiguousarray(skip, dtype=np.uint8), np.ascontiguousarray(have0, dtype=np.uint8),
              np.ascontiguousarray(reqcols, dtype=np.uint8), np.ascontiguousarray(relations, dtype=np.uint8),
              np.array(offsets, dtype=np.int32), np.array(values, dtype=np.int32),
              np.array(clash_offsets, dtype=np.int32), np.array(clash_values, dtype=np.int32)]
    nr = alive.max_support
    if (arrays[0].shape != (n, max(1, (nr+63)//64))
            or arrays[1].shape != (n, max(1, (selected+63)//64))
            or any(a.size != n for a in arrays[2:7])
            or arrays[7].size != n//2):
        raise ValueError("native enumeration input shape")
    handle = lib.algen_enum(n, k, alive.width, full, int(prune), props_from,
                            arrays[0].ctypes.data, nr, arrays[1].ctypes.data, selected,
                            *[a.ctypes.data for a in arrays[2:]])
    if not handle:
        raise RuntimeError("native enumeration returned no result")
    return _result(lib, handle, alive, range(1, k+1), True)


def _result(lib, handle, alive, order, include_empty):
    try:
        empty = []
        for depth in order:
            block = []
            for kind, code in ((0, alive.key_type), (1, alive.support_type)):
                size = lib.algen_size(handle, depth, kind)
                ptr = lib.algen_data(handle, depth, kind)
                data = np.ctypeslib.as_array(ptr, shape=(size,)) if size else np.empty(0, dtype=np.uint64)
                if size and int(data.max()) > np.iinfo(np.dtype(code)).max:
                    raise OverflowError("native packed output overflow")
                out = array(code)
                out.frombytes(data.astype(np.dtype(code), copy=False).tobytes())
                block.append(out)
            if len(block[0]) != len(block[1]):
                raise ValueError("native keys/supports length mismatch")
            if block[0]:
                alive.blocks[depth] = tuple(block)
                alive.size += len(block[0])
            size = lib.algen_size(handle, depth, 2) if include_empty else 0
            ptr = lib.algen_data(handle, depth, 2)
            for i in range(size):
                value = ptr[i]
                prem = []
                for _ in range(depth):
                    prem.append(value & alive.mask)
                    value >>= alive.width
                empty.append(tuple(reversed(prem)))
        return alive, empty, int(lib.algen_count(handle)), lib.source_hash
    finally:
        lib.algen_free(handle)


def minimal_packed(alive):
    """The public minimal operation, including arbitrary nonminimal/duplicate keys."""
    if alive.width * (alive.max_premises+1) + 1 > 64:
        return None
    lib = library()
    if lib is None:
        return None
    keys, values = [], []
    sizes = (C.c_size_t * (alive.max_premises+1))()
    key_ptr = (C.c_void_p * (alive.max_premises+1))()
    val_ptr = (C.c_void_p * (alive.max_premises+1))()
    for depth, (kk, vv) in alive.blocks.items():
        ka = np.asarray(kk, dtype=np.uint64)
        va = np.asarray(vv, dtype=np.uint64)
        keys.append(ka); values.append(va)
        sizes[depth] = len(ka)
        key_ptr[depth], val_ptr[depth] = ka.ctypes.data, va.ctypes.data
    out = alive.empty_like()
    order = list(alive.blocks)
    handle = lib.algen_minimal(alive.max_premises, alive.width, key_ptr, val_ptr, sizes)
    if not handle:
        raise RuntimeError("native minimal returned no result")
    out, _, _, _ = _result(lib, handle, out, order, False)
    return out
