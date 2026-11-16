"""Кандидаты в тождества термов: атомы-вырождения, верные во всех строках таблицы, где известны.

    python3 -B -m tools.identity_candidates G --каталог ../tab --выход ../out [--порог 200]

Вырождение терма — iso(t, s), eq-sub(t, s), le в обе стороны, trivial(t), whole(t): если оно
верно для всех групп, все условия о t — повтор условий о s (или константа), и схемы с t верхним
термом схлопываются (так 13.11 выродились pullback(Кэли, Кэли) ≅ G, pullback/pushout(id, id) ≅ G,
G/C_G(Z(G)) = 1). Атом, верный во всех ⩾ порога строках с известным значением и ни в одной не
ложный, — кандидат в правило; доказательство и ревью — отдельно, библиотека конечна.
Теоремы теории в строках не записываются (константы перебора), поэтому сюда почти не попадают.
"""
import argparse
import json
import os
import time
from pathlib import Path

import numpy as np

RELS = {"iso", "eq-sub", "le", "embeds", "conj-sub"}
PROPS = {"trivial", "whole"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--каталог", dest="dir", required=True)
    ap.add_argument("--выход", dest="out", required=True)
    ap.add_argument("--порог", dest="least", type=int, default=200)
    a = ap.parse_args()
    os.environ.setdefault("ALGEN_SIZE", "2")
    from algen import table as TB
    from algen import enumerate as E
    from algen.library import built_library
    from algen.logic import Vocab
    t0 = time.time()
    v = Vocab.section("grp")
    lib = built_library(v)
    f = TB.load(lib, v, a.base, a.dir)
    atoms = f.atoms
    rows = f.m.shape[0]
    synth = np.array([bool(f.synthetic(r)) for r in range(rows)]) if hasattr(f, "synthetic") else np.zeros(rows, bool)
    want = [j for j, at in enumerate(atoms)
            if (at[0] == "r" and at[1] in RELS) or (at[0] == "p" and at[1] in PROPS)]
    print(f"таблица {a.base}: строк {rows}, атомов {len(atoms)}, вырождений-кандидатов к проверке {len(want)}, "
          f"{time.time() - t0:.0f} с", flush=True)
    out, step = [], 1000
    for i in range(0, len(want), step):
        part = want[i:i + step]
        idx = [x for j in part for x in (2 * j, 2 * j + 1)]
        cols = f.m.cols(idx) if hasattr(f.m, "cols") else np.asarray(f.m)[:, idx]
        t, fl = cols[:, 0::2], cols[:, 1::2]
        for k, j in enumerate(part):
            tk, fk = t[:, k], fl[:, k]
            known = int((tk | fk).sum())
            if fk.any() or known < a.least:
                continue
            out.append({"атом": E.lit_name(atoms[j], True), "известно строк": known,
                        "из них настоящих": int(((tk | fk) & ~synth).sum()), "верно": int(tk.sum())})
    out.sort(key=lambda r: -r["из них настоящих"])
    Path(a.out).mkdir(parents=True, exist_ok=True)
    Path(a.out, f"тождества-{a.base}.json").write_text(json.dumps(
        {"база": a.base, "строк": rows, "порог": a.least, "кандидатов": len(out), "кандидаты": out},
        ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"кандидатов {len(out)}; первые 40:", flush=True)
    for r in out[:40]:
        print(f"  {r['атом']}: известно {r['известно строк']} (настоящих {r['из них настоящих']})", flush=True)
    print(f"готово за {time.time() - t0:.0f} с", flush=True)


if __name__ == "__main__":
    main()
