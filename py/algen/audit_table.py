"""Аудит таблицы базы: где значения неизвестны.

    python3 -m algen.audit_table G --каталог ../tab --выход ../out/none

По каждому атому — доля строк (объектов библиотеки), где значение известно
(m: записано или выведено). Сводки: по свойству, по внешней конструкции терма
(sym, cayley, rank, …), по паре «свойство × конструкция»; атомы, неизвестные во
всех строках; строки, противоречащие базе. Неизвестное значение = вопрос,
который ничто не опровергает (и не подтверждает) — источник ложных вопросов в
фоне сжатия (5.11: φ(rank G), pushout, sym, cayley, …)."""

import argparse
import json
import os
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np


def head(t):
    """Внешняя конструкция терма: имя операции (App.op) или имя переменной."""
    op = getattr(t, "op", None)
    return str(op) if op is not None else str(t)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--каталог", dest="dir", required=True)
    ap.add_argument("--выход", dest="out", required=True)
    a = ap.parse_args()
    os.environ.setdefault("ALGEN_SIZE", "2")
    from algen import table as TB
    from algen import enumerate as E
    from algen.library import built_library
    from algen.logic import App, Var, Vocab
    t0 = time.time()
    v = Vocab.section("grp")
    lib = built_library(v)
    f = TB.load(lib, v, a.base, a.dir)
    rows = f.m.shape[0] if hasattr(f.m, "shape") else len(f.envs)
    atoms = f.atoms
    print(f"таблица {a.base}: строк {rows}, атомов {len(atoms)}, {time.time() - t0:.0f} с", flush=True)
    known = np.zeros(len(atoms), dtype=np.int64)
    true_ = np.zeros(len(atoms), dtype=np.int64)
    step = 2000
    for i in range(0, len(atoms), step):
        idx = list(range(2 * i, 2 * min(len(atoms), i + step)))
        cols = f.m.cols(idx) if hasattr(f.m, "cols") else np.asarray(f.m)[:, idx]
        t, fl = cols[:, 0::2], cols[:, 1::2]
        known[i:i + t.shape[1]] = (t | fl).sum(axis=0)
        true_[i:i + t.shape[1]] = t.sum(axis=0)
    by_prop = defaultdict(lambda: [0, 0, 0])   # атомов, известно (сумма), атомов без значений
    by_head = defaultdict(lambda: [0, 0, 0])
    by_pair = defaultdict(lambda: [0, 0, 0])
    dead = []
    for j, at in enumerate(atoms):
        if at[0] == "pair":
            continue
        prop = str(at[1])
        terms = [x for x in at[2:] if isinstance(x, (App, Var))]
        hd = "/".join(sorted({head(x) for x in terms})) or "—"
        for d, k in ((by_prop, prop), (by_head, hd), (by_pair, (prop, hd))):
            d[k][0] += 1
            d[k][1] += int(known[j])
            d[k][2] += int(known[j] == 0)
        if known[j] == 0:
            dead.append(E.lit_name(at, True))

    def table(d, n=None):
        out = []
        for k, (na, kn, z) in d.items():
            out.append({"ключ": k if isinstance(k, str) else " × ".join(k), "атомов": na,
                        "известно %": round(100 * kn / (na * rows), 2) if na and rows else 0,
                        "атомов без значений": z})
        out.sort(key=lambda r: (r["известно %"], -r["атомов"]))
        return out[:n] if n else out
    rep = {"база": a.base, "строк": rows, "атомов": len(atoms),
           "известно % всего": round(100 * int(known.sum()) / (len(atoms) * rows), 2) if rows else 0,
           "атомов без значений": len(dead),
           "строк противоречат базе": len(getattr(f, "skipped", []) or []),
           "по свойству": table(by_prop), "по конструкции": table(by_head),
           "по паре": table(by_pair, 3000), "без значений (первые 5000)": dead[:5000]}
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / f"аудит-{a.base}.json").write_text(json.dumps(rep, ensure_ascii=False, indent=1), encoding="utf-8")
    lines = [f"# Аудит таблицы {a.base}", "",
             f"Строк {rows}, атомов {len(atoms)}; известно {rep['известно % всего']} % значений; "
             f"атомов без значений {len(dead)}; строк противоречат базе {rep['строк противоречат базе']}.", "",
             "## Конструкции, хуже всего известные", "", "| конструкция | атомов | известно % | без значений |", "|---|---|---|---|"]
    lines += [f"| {r['ключ']} | {r['атомов']} | {r['известно %']} | {r['атомов без значений']} |" for r in rep["по конструкции"][:80]]
    lines += ["", "## Свойства, хуже всего известные", "", "| свойство | атомов | известно % | без значений |", "|---|---|---|---|"]
    lines += [f"| {r['ключ']} | {r['атомов']} | {r['известно %']} | {r['атомов без значений']} |" for r in rep["по свойству"][:120]]
    (out / f"аудит-{a.base}.txt").write_text("\n".join(lines), encoding="utf-8")
    print("\n".join(lines[:60]), flush=True)
    print(f"готово за {time.time() - t0:.0f} с", flush=True)


if __name__ == "__main__":
    sys.exit(main())
