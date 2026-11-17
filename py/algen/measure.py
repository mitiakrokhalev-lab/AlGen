"""Замеры для ускорения перебора (A9): сколько различных строк таблицы остаётся
на столбцах одной схемы и где тратится время.

    python3 -m algen.measure строки G --каталог ../tab --выборка 50
    python3 -m algen.measure профиль prof.json        # свод профиля py-spy (speedscope)
"""

import argparse
import collections
import json
import sys
import time

import numpy as np


def rows(base, tdir, sample):
    from . import table as T
    vocab = T.Vocab.section("grp")
    lib = T.built_library(vocab)
    t = time.time()
    f = T.load(lib, vocab, base, tdir)
    print(f"{base}: таблица {f.e.shape}, {round(time.time() - t)} с", flush=True)
    full = np.concatenate([f.m, f.s, f.e], axis=1)
    print(f"различных строк на всех столбцах: {len(np.unique(np.packbits(full, axis=1), axis=0))}", flush=True)
    out = []
    for sid, terms in T.schemes(vocab, base)[::sample]:
        v = T.view(f, terms)
        x = np.packbits(np.concatenate([v.m, v.s, v.e], axis=1), axis=1)
        u = len(np.unique(x, axis=0))
        out.append((sid, v.e.shape[1], v.e.shape[0], u))
        print(f"{sid}: литералов {v.e.shape[1]}, строк {v.e.shape[0]}, различных {u} ({v.e.shape[0] / max(u, 1):.0f}×)", flush=True)
    if out:
        r = np.array([o[2] / max(o[3], 1) for o in out])
        print(f"схем {len(out)}: сжатие строк — медиана {np.median(r):.0f}×, минимум {r.min():.0f}×, максимум {r.max():.0f}×")


def profile(path, top=30):
    d = json.load(open(path))
    fr = d["shared"]["frames"]
    inc, own = collections.Counter(), collections.Counter()
    total = 0
    for p in d["profiles"]:
        w = p.get("weights") or [1] * len(p["samples"])
        for s, wt in zip(p["samples"], w):
            total += wt
            seen = set()
            for i in s:
                k = f"{fr[i]['name']} ({fr[i].get('file', '').split('/')[-1]}:{fr[i].get('line', '')})"
                kk = k.rsplit(":", 1)[0]
                if kk not in seen:
                    inc[kk] += wt
                    seen.add(kk)
            if s:
                top_f = fr[s[-1]]
                own[f"{top_f['name']} ({top_f.get('file', '').split('/')[-1]}:{top_f.get('line', '')})"] += wt
    print(f"отсчётов {total}")
    print("== включая вызванное ==")
    for k, v in inc.most_common(top):
        print(f"{v / total:6.1%}  {k}")
    print("== собственное время ==")
    for k, v in own.most_common(top):
        print(f"{v / total:6.1%}  {k}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("строки")
    s.add_argument("base")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--выборка", dest="sample", type=int, default=50)
    s = sub.add_parser("профиль")
    s.add_argument("path")
    a = ap.parse_args()
    if a.cmd == "строки":
        rows(a.base, a.dir, a.sample)
    else:
        profile(a.path)


if __name__ == "__main__":
    sys.exit(main())
