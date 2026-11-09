"""Отпечаток каркаса базы: атомы и клаузы теории без учёта порядка (для сверки
ускорений заземления со старым кодом). python3 -m algen.canon G

Память — как у самого каркаса: клауза сворачивается в 8-байтный хеш сразу,
без списка строковых кортежей (на G их десятки миллионов)."""
import hashlib
import resource
import sys
import time

import numpy as np

from algen import table as t

vocab = t.Vocab.section("grp")
lib = t.built_library(vocab)
t0 = time.time()
f = t.skeleton(lib, vocab, sys.argv[1])
dt = time.time() - t0
T = f.sc.T
A = [str(a) for a in T.atoms]
M = (1 << 64) - 1
ha = [int.from_bytes(hashlib.blake2b(s.encode(), digest_size=8).digest(), "little") for s in A]
neg = [(h * 0x9E3779B97F4A7C15 + 1) & M for h in ha]
# клауза — сумма хешей литералов по модулю 2⁶⁴ (у отрицания свой хеш), затем перемешивание
hc = np.fromiter((((sum(ha[l - 1] if l > 0 else neg[-l - 1] for l in c) & M) * 0xBF58476D1CE4E5B9) & M
                  for c in T.clauses), dtype=np.uint64, count=len(T.clauses))
hc.sort()
ha = np.sort(np.array(ha, dtype=np.uint64))
print(sys.argv[1], round(dt), "с", len(A), hashlib.sha256(ha.tobytes()).hexdigest()[:12],
      len(hc), hashlib.sha256(hc.tobytes()).hexdigest()[:12], flush=True)
print("память", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024, "МБ")
