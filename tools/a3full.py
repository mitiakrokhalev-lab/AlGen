"""A3: перебор k ⩽ 2 по всей таблице базы без схем + фильтр выводимости.

Перебор: столбцы литералов — битовые множества строк (различных строк таблицы);
для каждой посылки p — произведение матриц по строкам с p даёт все пары (q, цель),
у которых нет строки «p, q верны, цель ложна». Минимальность: p ⇒ g и q ⇒ g
опровергнуты. Выводимость: единичное распространение теории по (p, q) — одно на
пару; остаток по выборке пар проверяется решателем с отсевом по моделям.

Запуск: ALGEN_PY=<каталог py> python3 a3full.py БАЗА КАТАЛОГ_ТАБЛИЦ ВЫХОД [НИТЕЙ] [ДОЛЯ_SAT]
Код algen берётся из ALGEN_PY — тот, которым построены таблицы (иначе отпечаток не сойдётся)."""
import json
import os
import random
import sys
import time
import multiprocessing as mp

import numpy as np

sys.path.insert(0, os.environ.get("ALGEN_PY", os.path.join(os.path.dirname(__file__), "..", "py")))
from algen import table as TB  # noqa: E402
from algen.logic import Vocab  # noqa: E402
from algen.library import built_library  # noqa: E402

base, tdir, out = sys.argv[1], sys.argv[2], sys.argv[3]
THREADS = int(sys.argv[4]) if len(sys.argv) > 4 else 4
SAT_FRAC = float(sys.argv[5]) if len(sys.argv) > 5 else 0.002

G = {}


def setup():
    t0 = time.time()
    from algen import enumerate as E
    E.SKIP.update(x for x in os.environ.get("SKIP", "").split(",") if x)  # как --без у построения таблиц
    vocab = Vocab.section("grp")
    lib = built_library(vocab)
    f = TB.load(lib, vocab, base, tdir)
    T = f.sc.T
    L = f.e.shape[1]
    sat = []
    for j in range(L):
        x = T.lit(*f.lit(j))
        sat.append(x if type(x) is int else None)
    fixed = [x for x in (T.lit(*f.lit(j)) for j in f.fixed) if type(x) is int]
    rows = np.unique(np.packbits(f.e, axis=1), axis=0)
    A = np.unpackbits(rows, axis=1, count=L).astype(np.float32)
    neg = np.arange(L) ^ 1
    atom = np.arange(L) // 2
    C1 = A.T @ A
    cnt = np.diag(C1).copy()
    const = cnt[neg] == 0
    useful = (cnt > 0) & ~const & np.array([s is not None for s in sat])
    ref1 = C1[:, neg] > 0
    ok_g = ~const & (cnt[neg] > 0) & np.array([s is not None for s in sat])
    nv = len(T.atoms) + 1
    litpos = np.array([x if x is not None else 0 for x in sat], dtype=np.int64)
    G.update(nv=nv, litpos=litpos, mark=np.zeros(2 * nv + 1, dtype=bool))
    G.update(f=f, T=T, sat=sat, fixed=fixed, A=A, neg=neg, atom=atom, cnt=cnt, const=const,
             useful=useful, ref1=ref1, ok_g=ok_g, R=f.e.shape[0], L=L, t_setup=time.time() - t0)


def work(ps):
    from pysat.solvers import Solver
    f, T = G["f"], G["T"]
    s = Solver(name="g4", bootstrap_with=T.clauses)
    A, neg, atom, ref1, ok_g, useful = G["A"], G["neg"], G["atom"], G["ref1"], G["ok_g"], G["useful"]
    sat, fixed, L = G["sat"], G["fixed"], G["L"]
    rnd = random.Random(ps[0])
    st = dict(alive=0, pairs=0, empty=0, contra=0, der_prop=0, rest=0, t_enum=0.0, t_prop=0.0,
              sat_pairs=0, sat_cand=0, sat_der=0, sat_calls=0, t_sat=0.0)
    samples = []
    idx = np.arange(L)
    for p in ps:
        ta = time.time()
        sub = A[A[:, p] > 0]
        Cp = sub.T @ sub
        diag = np.diag(Cp)
        q_ok = useful & (idx > p) & (atom != atom[p])
        st["empty"] += int((q_ok & (diag == 0)).sum())
        q_ok &= diag > 0
        alive = (Cp[:, neg] == 0) & q_ok[:, None] & ok_g[None, :] & ref1[p][None, :] & ref1
        alive &= (atom[None, :] != atom[:, None]) & (atom[None, :] != atom[p])
        st["t_enum"] += time.time() - ta
        ta = time.time()
        for q in np.flatnonzero(alive.any(axis=1)):
            gs = np.flatnonzero(alive[q])
            st["alive"] += len(gs)
            st["pairs"] += 1
            ok, imp = s.propagate(assumptions=fixed + [sat[p], sat[int(q)]])
            if not ok:
                st["contra"] += len(gs)
                continue
            mark = G["mark"]
            mark[:] = False
            mark[np.asarray(imp, dtype=np.int64) + G["nv"]] = True
            rest = [int(g) for g in gs[~mark[G["litpos"][gs] + G["nv"]]]]
            st["der_prop"] += len(gs) - len(rest)
            st["rest"] += len(rest)
            if rest and rnd.random() < SAT_FRAC:
                tb = time.time()
                cand, der = set(rest), []
                st["sat_pairs"] += 1
                st["sat_cand"] += len(cand)
                while cand:
                    g = cand.pop()
                    st["sat_calls"] += 1
                    if not s.solve(assumptions=fixed + [sat[p], sat[int(q)], -sat[g]]):
                        der.append(g)
                        continue
                    model = set(s.get_model())
                    cand = {h for h in cand if -sat[h] not in model}
                st["sat_der"] += len(der)
                st["t_sat"] += time.time() - tb
                if len(samples) < 20:
                    nm = lambda j: ("¬" if j % 2 else "") + str(f.atoms[j // 2])  # noqa: E731
                    samples.append({"посылки": [nm(p), nm(int(q))],
                                    "остаток": [nm(g) for g in rest if g not in der][:10],
                                    "выводится SAT": [nm(g) for g in der][:10]})
        st["t_prop"] += time.time() - ta
    s.delete()
    return st, samples


def main():
    setup()
    t0 = time.time()
    useful = G["useful"]
    k1 = (~G["ref1"]) & useful[:, None] & G["ok_g"][None, :] & (G["atom"][:, None] != G["atom"][None, :])
    ps = [int(p) for p in np.flatnonzero(useful)]
    random.Random(1).shuffle(ps)
    chunks = [ps[i::THREADS * 8] for i in range(THREADS * 8)]
    tot, samples = {}, []
    with mp.get_context("fork").Pool(THREADS) as pool:
        for st, sm in pool.imap_unordered(work, chunks):
            for k, v in st.items():
                tot[k] = tot.get(k, 0) + v
            samples += sm
            print(json.dumps({k: (round(v) if isinstance(v, float) else v) for k, v in tot.items()}), flush=True)
    wall = time.time() - t0
    rest_frac_sat = tot["sat_der"] / max(tot["sat_cand"], 1)
    res = {
        "база": base, "строк": G["R"], "различных строк": int(G["A"].shape[0]), "литералов": G["L"],
        "k=0 (верно во всех строках)": int(G["const"].sum()), "k=1 неопровергнутых": int(k1.sum()),
        "k=2 минимальных неопровергнутых": tot["alive"], "пар посылок": tot["pairs"],
        "пустых пар (посылки несовместны в библиотеке)": tot["empty"],
        "посылки противоречат теории": tot["contra"], "выводится распространением": tot["der_prop"],
        "остаток после распространения": tot["rest"],
        "выборка SAT: пар": tot["sat_pairs"], "кандидатов": tot["sat_cand"], "выводится": tot["sat_der"],
        "вызовов SAT": tot["sat_calls"], "оценка: выводится SAT во всём остатке": round(tot["rest"] * rest_frac_sat),
        "оценка: неизвестно (вопросы до склейки)": round(tot["rest"] * (1 - rest_frac_sat)),
        "время": {"подготовка, с": round(G["t_setup"]), "стена, с": round(wall),
                  "перебор, нить·с": round(tot["t_enum"]), "распространение, нить·с": round(tot["t_prop"] - tot["t_sat"]),
                  "SAT по выборке, нить·с": round(tot["t_sat"]),
                  "SAT на весь остаток (оценка), нить·ч": round(tot["t_sat"] / max(tot["sat_cand"], 1) * tot["rest"] / 3600, 1)},
        "примеры": samples[:20],
    }
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, f"a3-{base}.json"), "w", encoding="utf-8") as fh:
        json.dump(res, fh, ensure_ascii=False, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "примеры"}, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
