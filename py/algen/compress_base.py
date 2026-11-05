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


def fold_across(T, name2lit, fixed, questions, budget=None, no_back=None):
    """questions: [{"id": "схема:№", "№", "запрет": [имена], "примеров"}].
    Возвращает (оставленные id, {id: [id источников]}, {id: причина}).
    no_back(q) — вопрос остаётся, но в фон не входит (сворачивать им другие нельзя)."""
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
    back = None
    if C.PRECHECK and hasattr(T, "atoms"):  # фон + локальная теория (термы всех вопросов) — «невыполнимо» без каркаса
        from . import fast
        from .logic import App, Var
        inv = {}
        need = {abs(l) for F in enc.values() if F for l in F}
        for a in T.atoms:
            v = T.var.get(a)
            if v in need:
                inv[v] = a
        terms = {x for a in inv.values() for x in a[2:] if isinstance(x, (App, Var))}
        back = C._Back(fast.Local(T, terms))
    model = None  # последняя модель теории с фоном: свидетель совместности без решателя
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
            pre = back.unsat(fx, F, list(sels)) if back is not None else None
            ans = False if pre is not None else C._solve(s, fx + F + list(sels))
            if ans is False:
                core = set(pre) if pre is not None else set(s.get_core() or [])
                deps = sorted(sels[x] for x in sels if x in core)
                if deps:
                    folded[q["id"]] = deps
                    continue
                why[q["id"]] = "ОШИБКА: следует из одной теории"
            nv += 1
            s.add_clause([-nv] + [-l for l in F])
            kept.append(q["id"])
            if no_back is not None and no_back(q):
                s.add_clause([-nv])
                why.setdefault(q["id"], "вне фона: по выбору (no_back)")
                continue
            # в фон — только если фон с вопросом совместен (иначе из фона следует всё; 5.11)
            if model is not None and any(model.get(abs(l)) is not None and model[abs(l)] != (l > 0) for l in F):
                ok = True  # модель теории с фоном, где запрет ложен — свидетель совместности
            else:
                ok = C._solve(s, fx + list(sels) + [nv])
                if ok:
                    m = s.get_model() or []
                    model = {abs(x): x > 0 for x in m}
            if ok:
                sels[nv] = q["id"]
                if back is not None:
                    back.add(nv, F)
            else:
                s.add_clause([-nv])
                if q["id"] not in why:
                    if ok is False:
                        core = set(s.get_core() or [])
                        why[q["id"]] = "вне фона: противоречит " + ", ".join(sorted(sels[x] for x in sels if x in core))
                    else:
                        why[q["id"]] = "вне фона: решатель не ответил"
    finally:
        s.delete()
        if back is not None:
            back.loc.delete()
            back.delete()
    return kept, folded, why, enc, fx


def verify_across(T, enc, fx, kept, folded, sample=1000, rng=None, chunk=100, log=None, outside=None):
    """Решатель на выборке: каждый свёрнутый следует из теории и своих
    источников; источники оставлены. Решатель свой на каждые chunk образцов
    (загрузка теории каркаса — секунды), внутри — селекторы: условие образца
    включено только при его селекторе, после образца селектор гасится."""
    ks = set(kept)
    items = list(folded.items())
    if len(items) > sample:
        items = (rng or random.Random(0)).sample(items, sample)
    nv0 = max([C._nvars(T)] + [abs(l) + 1 for F in enc.values() if F for l in F] + [abs(l) + 1 for l in fx])
    bad, s, nv, t0 = [], None, nv0, time.time()
    back = [q for q in kept if q not in (outside or ()) and enc.get(q)]
    if back:  # фон совместен: иначе из него следует всё
        s0 = T.solver()
        try:
            for q in back:
                s0.add_clause([-l for l in enc[q]])
            if s0.solve(assumptions=fx) is False:
                bad.append(("фон", "оставленные вопросы вместе противоречивы"))
        finally:
            s0.delete()
    for qid, deps in items:
        if any(d in (outside or ()) for d in deps):
            bad.append((qid, "источник вне фона"))
    try:
        for i, (qid, deps) in enumerate(items):
            if any(d not in ks for d in deps):
                bad.append((qid, "источник не оставлен"))
                continue
            if enc.get(qid) is None or any(enc.get(d) is None for d in deps):
                bad.append((qid, "нет кодировки"))
                continue
            if i % chunk == 0:
                if s is not None:
                    s.delete()
                s, nv = T.solver(), nv0
                if log:
                    log(f"verify {i}/{len(items)}, {time.time() - t0:.0f} с, нарушений {len(bad)}")
            nv += 1
            for d in deps:
                s.add_clause([-nv] + [-l for l in enc[d]])
            if s.solve(assumptions=[nv] + fx + enc[qid]):
                if not (len(deps) == 1 and sorted(enc[deps[0]]) == sorted(enc[qid])):
                    bad.append((qid, "не следует из источников"))
            s.add_clause([-nv])
    finally:
        if s is not None:
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
    ap.add_argument("--фон-без-всегда", dest="no_always", type=int, default=0,
                    help="вопросы без посылок (запрет — один литерал) с ≥ N примеров — не в фон")
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
    nb = None
    if a.no_always:
        nb = lambda q: len(q["запрет"]) == 1 and isinstance(q.get("примеров"), int) and q["примеров"] >= a.no_always
    kept, folded, why, enc, fx = fold_across(T, name2lit, fixed, qs, no_back=nb)
    print(f"сжатие между схемами {time.time() - t:.0f} с: оставлено {len(kept)}, свёрнуто {len(folded)} "
          f"(тот же класс {sum(1 for x in folded if why.get(x) == 'тот же класс')})", flush=True)
    from collections import Counter
    print("особые:", Counter(w.split(":")[0] for x, w in why.items() if w != "тот же класс"))
    real = [x for x in kept if not why.get(x, "").startswith("ОШИБКА")]
    print(f"вопросов (без выводимых из одной теории): {len(real)}, из них вне фона: "
          f"{sum(1 for x in real if why.get(x, '').startswith('вне фона'))}", flush=True)
    out = {"база": a.base, "класс": a.cls, "оставлено": kept, "свёрнуто": folded,
           "особые": {x: w for x, w in why.items() if w != "тот же класс"}}
    if a.out:  # до verify: долгая проверка не должна терять сжатие
        Path(a.out).write_text(json.dumps(out, ensure_ascii=False), encoding="utf-8")
    t = time.time()
    outside = {x for x, w in why.items() if w.startswith("вне фона")}
    bad = verify_across(T, enc, fx, kept, folded, log=lambda m: print(m, flush=True), outside=outside)
    print(f"нарушений verify: {len(bad)} за {time.time() - t:.0f} с", bad[:10], flush=True)
    if a.out:
        out["verify"] = {"нарушений": len(bad), "первые": bad[:50]}
        Path(a.out).write_text(json.dumps(out, ensure_ascii=False), encoding="utf-8")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
