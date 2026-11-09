"""Сверка перебора схемы со старым кодом: время E.run по фазам (с банком моделей,
как в table перебор) и отпечаток выдачи — хеш всех строк отчёта.

    python3 -m algen.ident 3 "∀ G : Grp" "center(G); commutator(G)" [файл хешей строк]
"""
import sys, time, pickle, os
from collections import Counter, defaultdict
from algen import enumerate as E, fast
from algen.library import built_library
from algen.logic import Vocab
from pysat.solvers import Solver
import json, hashlib

k = int(sys.argv[1])
t0 = time.time()
v = Vocab.section("grp")
lib = built_library(v)
form = E.SchemeForm(lib, v, sys.argv[2], [x for x in sys.argv[3].split(";") if x.strip()])
print(f"форма {time.time() - t0:.0f} с, матрица {form.m.shape}", flush=True)
fast.install()
T = defaultdict(float); N = Counter()


def timed(name, f):
    def w(*a, **kw):
        t = time.perf_counter()
        try:
            return f(*a, **kw)
        finally:
            T[name] += time.perf_counter() - t; N[name] += 1
    return w


for name in ("enumerate_form", "minimal", "pair_minimal", "generic_filter", "decide", "questions", "cover", "klass", "symmetries"):
    setattr(E, name, timed(name, getattr(E, name)))
for name in ("refuters", "one_unknown", "unknown_goal", "deciding", "where", "value_name"):
    if hasattr(form, name):
        setattr(form, name, timed(name, getattr(form, name)))
orig_q = E.questions


def q(form_, report, limit=None):
    for r in report:
        r["_c"] = list(r["_cols"])
    return orig_q(form_, report, limit)


E.questions = q
t = time.time()
form, alive, empty, report = E.run(k, form=form)
tot = time.time() - t
print(f"run {tot:.0f} с; минимальных {len(alive)}, в отчёте {len(report)}", flush=True)
for name, s in sorted(T.items(), key=lambda x: -x[1]):
    print(f"  {name:16s} {s:8.1f} с  {N[name]:9d} вызовов")
print("банк:", fast.STATS, flush=True)
digs = [hashlib.sha1(json.dumps({kk: vv for kk, vv in r.items() if kk != "_c"}, sort_keys=True, ensure_ascii=False, default=str).encode()).hexdigest()[:16] for r in report]
print("отпечаток выдачи", hashlib.sha1("".join(digs).encode()).hexdigest()[:16], len(digs), flush=True)
with open(sys.argv[4] if len(sys.argv) > 4 else "/dev/null", "wb") as f:
    pickle.dump(digs, f)
