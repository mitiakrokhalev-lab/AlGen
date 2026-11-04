"""Сжатие между схемами базы: оставленные вопросы всех схем базы (поле
«оставленные вопросы» сводки схемы, ALGEN_COMPRESS) сворачиваются тем же
жадным базисом относительно теории базы (каркас — общая теория всех схем
базы: виды схем делят form.sc). Правила те же, что у compress:

* порядок — по интересности (короче запрет, больше примеров), потом жадно;
* фон — теория базы, гипотезы базы и уже оставленные вопросы (под
  селекторами); значения таблицы не входят;
* решатель не ответил — вопрос остаётся;
* свёрнутый вопрос хранит «следует из схема:№ …» и возвращается при
  опровержении источника; один и тот же класс в разных схемах — один вопрос;
* литерал, которого нет в каркасе, — вопрос остаётся и в фон не идёт.

    python3 -m algen.compress_base G каталог-сводок [--класс finite] [--выход файл.json]
"""
import argparse
import json
import random
import sys
import time
from pathlib import Path

from algen import compress as C


def key(q):
    return (len(q["запрет"]), -q["примеров"] if isinstance(q.get("примеров"), int) else 0, q["id"])


def fold_across(T, name2lit, fixed, questions, budget=None):
    """questions: [{"id": "схема:№", "№", "запрет": [имена], "примеров"}].
    Возвращает (оставленные id, {id: [id источников]}, {id: причина})."""
    from pysat.solvers import Solver  # noqa: F401 — решатель теории T.solver()

    def lits(q):
        out = []
        for n in q["запрет"]:
            if n not in name2lit:
                return None
            a, v = name2lit[n]
            l = T.lit(a, v)
            if l is None:
                continue
            if l is False:
                return False
            out.append(l)
        return out

    qs = sorted(questions, key=key)
    enc = {q["id"]: lits(q) for q in qs}
    fx = [l for a, v in fixed if type(l := T.lit(a, v)) is int]
    nv = max([C._nvars(T)] + [abs(l) + 1 for F in enc.values() if F for l in F] + [abs(l) + 1 for l in fx])
    s = T.solver()
    sels, kept, folded, why, first = {}, [], {}, {}, {}
    try:
        for q in qs:
            F = enc[q["id"]]
            if q["№"] in first:
                folded[q["id"]] = [first[q["№"]]]
                why[q["id"]] = "тот же класс"
                continue
            first[q["№"]] = q["id"]
            if not F:  # None — литерала нет в каркасе; False — запрет тождественно ложен
                kept.append(q["id"])
                why[q["id"]] = "нет литерала в каркасе" if F is None else "запрет ложен"
                continue
            ans = C._solve(s, fx + F + list(sels))
            if ans is False:
                core = set(s.get_core() or [])
                deps = sorted(sels[x] for x in sels if x in core)
                if deps:
                    folded[q["id"]] = deps
                    continue
                why[q["id"]] = "ОШИБКА: следует из одной теории"
            nv += 1
            s.add_clause([-nv] + [-l for l in F])
            sels[nv] = q["id"]
            kept.append(q["id"])
    finally:
        s.delete()
    return kept, folded, why, enc, fx


def verify_across(T, enc, fx, kept, folded, sample=1000, rng=None):
    """Новый решатель на выборке: каждый свёрнутый следует из теории и своих
    источников; источники оставлены."""
    ks = set(kept)
    items = list(folded.items())
    if len(items) > sample:
        items = (rng or random.Random(0)).sample(items, sample)
    bad = []
    for qid, deps in items:
        if any(d not in ks for d in deps):
            bad.append((qid, "источник не оставлен"))
            continue
        if enc.get(qid) is None or any(enc.get(d) is None for d in deps):
            bad.append((qid, "нет кодировки"))
            continue
        s = T.solver()
        try:
            for d in deps:
                s.add_clause([-l for l in enc[d]])
            if s.solve(assumptions=fx + enc[qid]):
                if not (len(deps) == 1 and sorted(enc[deps[0]]) == sorted(enc[qid])):
                    bad.append((qid, "не следует из источников"))
        finally:
            s.delete()
    return bad


def load_questions(paths):
    qs = []
    for p in paths:
        d = json.loads(Path(p).read_text(encoding="utf-8"))
        sid = d.get("id") or Path(p).stem
        for q in d.get("оставленные вопросы") or []:
            qs.append(dict(q, id=f"{sid}:{q['№']}"))
    return qs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("dir")
    ap.add_argument("--класс", dest="cls", default="")
    ap.add_argument("--выход", dest="out", default="")
    a = ap.parse_args()
    from algen import enumerate as E
    from algen.library import built_library
    from algen.logic import Var, Vocab
    from algen.table import skeleton
    t0 = time.time()
    qs = load_questions(sorted(Path(a.dir).glob("*.json")))
    print(f"схем {len({q['id'].split(':')[0] for q in qs})}, оставленных вопросов в схемах {len(qs)}", flush=True)
    v = Vocab.section("grp")
    lib = built_library(v)
    f = skeleton(lib, v, a.base)
    print(f"каркас {time.time() - t0:.0f} с, атомов {len(f.atoms)}", flush=True)
    T = f.sc.T
    name2lit = {}
    for at in f.atoms:
        if at[0] == "pair":
            continue
        for val in (True, False):
            name2lit.setdefault(E.lit_name(at, val), (at, val))
    fixed = list(getattr(f, "fixed_lits", []))
    if a.cls:
        X = next(t for t in f.own if isinstance(t, Var) and f.g.terms[t].sort == "Grp.obj")
        fixed.append((("p", a.cls, X), True))
    t = time.time()
    kept, folded, why, enc, fx = fold_across(T, name2lit, fixed, qs)
    print(f"сжатие между схемами {time.time() - t:.0f} с: оставлено {len(kept)}, свёрнуто {len(folded)} "
          f"(тот же класс {sum(1 for x in folded if why.get(x) == 'тот же класс')})", flush=True)
    from collections import Counter
    print("особые:", Counter(w for x, w in why.items() if w != "тот же класс"))
    bad = verify_across(T, enc, fx, kept, folded)
    print("нарушений verify:", len(bad), bad[:10])
    if a.out:
        Path(a.out).write_text(json.dumps({"база": a.base, "класс": a.cls, "оставлено": kept, "свёрнуто": folded,
                                           "особые": {x: w for x, w in why.items() if w != "тот же класс"}},
                                          ensure_ascii=False), encoding="utf-8")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
