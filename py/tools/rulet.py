"""Профиль каркаса базы по правилам: время, клаузы и пик памяти каждого правила.

    cd py && RSS_MAX=12 ALGEN_SIZE=2 ALGEN_FAST=1 ALGEN_SKEL=… python3 tools/rulet.py GE отчёт.txt

RSS_MAX (ГБ) — при превышении отчёт пишется и процесс выходит (код 3)."""
import sys, time, collections, threading
from algen import table as t, enumerate as E, logic as L
vocab = t.Vocab.section("grp")
lib = t.built_library(vocab)
cur = {"k": ("старт",)}
samples = collections.Counter()
clauses = collections.Counter()
import os
mem = {}
def rss():
    return int(open("/proc/self/statm").read().split()[1]) * 4096 / 2**30
def sampler():
    while True:
        time.sleep(0.5)
        samples[cur["k"]] += 0.5
        r = rss()
        mem[cur["k"]] = max(mem.get(cur["k"], 0), r)
        if r > float(os.environ.get("RSS_MAX", "9")):
            dump(); os._exit(3)
def dumper():
    while True:
        time.sleep(60)
        dump()
def dump():
    tot = sum(samples.values())
    with open(sys.argv[2], "w") as fh:
        fh.write(f"всего {tot:.0f} с\n")
        for k, v in samples.most_common(60):
            fh.write(f"{v:8.1f} с  клауз {clauses.get(k, 0):>9}  {' | '.join(map(str, k))}\n")
threading.Thread(target=sampler, daemon=True).start()
threading.Thread(target=dumper, daemon=True).start()
og, oap, oc, oeq = L.Theory._ground_rule, L.Theory._all_patterns, L.Theory._clause, L.Theory._equality_axioms
def ground(self, r, limit, grow=True):
    k = ("заземление", r["id"], len(r["scene"]))
    cur["k"] = k
    for x in og(self, r, limit, grow):
        cur["k"] = k
        yield x
_sm = isinstance(L.Theory.__dict__["_all_patterns"], staticmethod)
def allp(*a):
    r = a[-1]
    cur["k"] = ("достройка", r["id"], len(r["scene"]))
    return oap(r) if _sm else oap(*a)
def clause(self, parts, origin):
    clauses[cur["k"]] += 1
    return oc(self, parts, origin)
def eq(self):
    cur["k"] = ("аксиомы равенства",)
    return oeq(self)
L.Theory._ground_rule, L.Theory._clause, L.Theory._equality_axioms = ground, clause, eq
L.Theory._all_patterns = staticmethod(allp) if _sm else allp
t0 = time.time()
f = t.skeleton(lib, vocab, sys.argv[1])
cur["k"] = ("после",)
dump()
print("готово", round(time.time() - t0))
