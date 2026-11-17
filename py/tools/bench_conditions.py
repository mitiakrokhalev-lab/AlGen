"""Замер памяти хранения условий в отдельном процессе на каждый путь.

    python3 -B tools/bench_conditions.py dict 1000000
    python3 -B tools/bench_conditions.py packed 1000000

Отпечаток и число строк должны совпасть. RSS — прирост максимума процесса,
это замер хранения синтетических условий, не всей схемы и не каркаса.
"""

import hashlib
from itertools import combinations
import json
from pathlib import Path
import resource
import struct
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from algen.conditions import PackedConditions

mode = sys.argv[1]
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
if mode not in ("dict", "packed"):
    raise SystemExit("mode: dict | packed")
rss0 = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
store = {} if mode == "dict" else PackedConditions(1024, 3, 30_753)
t0 = time.perf_counter()
n = 0
for prem in combinations(range(100), 3):
    for g in range(300, 350):
        store[prem, g] = 1000 + g % 17
        n += 1
        if n == limit:
            break
    if n == limit:
        break
build = time.perf_counter() - t0
rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
h = hashlib.sha256()
for (prem, goal), support in store.items():
    h.update(struct.pack("<5I", *prem, goal, support))
print(json.dumps({"mode": mode, "rows": len(store), "sha256": h.hexdigest(),
                  "build_seconds": round(build, 3), "rss_increment_KiB": rss - rss0,
                  "array_bytes": getattr(store, "nbytes", None)}))
