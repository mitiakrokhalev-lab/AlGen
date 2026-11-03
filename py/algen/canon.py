"""Отпечаток каркаса базы: атомы и клаузы теории без учёта порядка (для сверки
ускорений заземления со старым кодом). python3 -m algen.canon G"""
import sys, hashlib, time
from algen import table as t, logic as L
vocab = t.Vocab.section("grp")
lib = t.built_library(vocab)
t0 = time.time()
f = t.skeleton(lib, vocab, sys.argv[1])
T = f.sc.T
A = [str(a) for a in T.atoms]
cl = sorted(tuple(sorted((A[abs(l) - 1], l > 0) for l in c)) for c in T.clauses)
print(sys.argv[1], round(time.time() - t0), "с", len(A), hashlib.sha256(repr(sorted(A)).encode()).hexdigest()[:12],
      len(cl), hashlib.sha256(repr(cl).encode()).hexdigest()[:12], flush=True)
import resource; print("память", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024, "МБ")
