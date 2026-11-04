"""Замер сжатия на схеме: E.run с банком моделей (как table перебор) и
ALGEN_COMPRESS; после сжатия — verify на выборке и regress до/после.

    ALGEN_FAST=1 ALGEN_COMPRESS=1 python3 -m algen.compress_run 3 "∀ G : Grp" "center(G); commutator(G)"
"""
import os
import sys
import time
from collections import Counter

from algen import compress as C, enumerate as E, fast
from algen.library import built_library
from algen.logic import Vocab

os.environ.setdefault("ALGEN_COMPRESS", "1")
k = int(sys.argv[1])
t0 = time.time()
v = Vocab.section("grp")
lib = built_library(v)
form = E.SchemeForm(lib, v, sys.argv[2], [x for x in sys.argv[3].split(";") if x.strip()])
print(f"форма {time.time() - t0:.0f} с, матрица {form.m.shape}", flush=True)
fast.install()
cap = {}
orig = C.compress
SAMPLE = int(os.environ.get("VERIFY_SAMPLE", "1000"))


def wrap(f, report, **kw):
    before = [C.digest(r) for r in report]  # отпечатки, а не копии: отчёт ≈ 7 ГБ
    t = time.time()
    orig(f, report, **kw)
    cap["t"] = time.time() - t
    t = time.time()
    cap["bad"] = C.verify(f, report, sample=SAMPLE)
    cap["tv"] = time.time() - t
    cap["reg"] = C.regress(before, report)
    return report


C.compress = wrap
t = time.time()
form, alive, empty, report = E.run(k, form=form)
print(f"run {time.time() - t:.0f} с (в т. ч. сжатие {cap['t']:.1f} с); verify {cap['tv']:.1f} с на {SAMPLE}", flush=True)
cl = {}
for r in report:
    cl.setdefault((r["класс"], r["вердикт"]), r)
cnt = Counter((r["вердикт"], "свёрнута" if r.get("свёрнута") else "оставлена", "экземпляр" if r.get("экземпляр") else "")
              for r in cl.values())
for key, n in sorted(cnt.items()):
    print("  ", *key, n)
print("нарушений verify:", len(cap["bad"]), cap["bad"][:10])
print("нарушений regress:", len(cap["reg"]), cap["reg"][:10])
print("ОШИБКА сжатия:", sum("ОШИБКА сжатия" in r for r in report))
deps = Counter(len(r["следует из"]) for r in cl.values() if r.get("свёрнута") and not r.get("экземпляр"))
print("размер «следует из»:", sorted(deps.items())[:15], "…, max", max(deps) if deps else 0)
sys.exit(1 if cap["bad"] or cap["reg"] else 0)
