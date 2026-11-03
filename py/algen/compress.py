"""Сжатие выдачи перебора: базис относительно теории с графом «следует из».

Вход — report из enumerate.run (строки ещё с "_cols"), выход — тот же report,
в котором ни одна строка не удалена и ни одно прежнее поле не изменено.
Добавляются поля:
    "№"           — устойчивый номер строки (по классу запрета);
    "свёрнута"    — True, если строка следует из оставленных строк выдачи;
    "следует из"  — номера оставленных строк, на которых держится вывод
                    (пусто у несвёрнутых);
    "сжатие"      — версия этого модуля.

Правила (docs/класс-перебора.md, «Сжатие выдачи: правила»):
1. Сначала порядок по интересности (interest_key), потом жадный базис: строка
   сворачивается только через строки, стоящие раньше и оставленные. Граф
   поэтому ацикличен.
2. Вопросы («неизвестно») — гипотезы. Фон для вопроса — теория (клаузы T и
   гипотезы базы form.fixed_lits) и оставленные вопросы, каждый под своим
   селектором; зависимость — селекторы из ядра решателя. Значения таблицы в
   фон не входят никогда.
3. Факты («выводится») доказаны теорией, поэтому их базис строится без
   теории: факт сворачивается, если следует из оставленных фактов одной
   логикой высказываний (иначе теория свернула бы все факты).
4. Решатель с бюджетом: если он не ответил (бюджет, ошибка), строка не
   сворачивается. Неполного вывода (только распространение) здесь нет —
   вызывается полный SAT; «не вывелось» без ответа решателя ≠ «не следует».
5. Прочие вердикты (опровергается, противоречие, трудный контрпример,
   короткий довод, ОШИБКА…) не сворачиваются и в фон не входят.
6. Экземпляры (instances): строка только об одном построенном терме t
   (например, Z(G)) у базы с одной переменной G — экземпляр R0 = R[t ↦ G].
   Она сворачивается со ссылкой «экземпляр: <запрет R0>», только если
   (а) сорт t равен сорту G; (б) каждая гипотеза базы (fixed_lits) и каждое
   условие существования t (graph.requires) выводятся теорией для t;
   (в) R0 не опровергнут ни одной строкой библиотеки (матрица m, со всеми
   помеченными значениями); (г) все атомы R0 есть в форме. R0 проверяется
   заново при каждом прогоне; опровергнут R0 — строка не сворачивается.
   Экземпляры не входят в фон базиса (осторожно: меньше сжатия, без дыр).
7. reopen: если вопрос опровергнут, все строки, которые держались на нём
   (транзитивно), разворачиваются. Повторный compress с refuted пересобирает
   базис без опровергнутых.
"""
import hashlib

VERSION = 1
# Бюджет конфликтов на один вызов решателя; None — без ограничения.
CONF_BUDGET = 100_000


def row_id(r):
    return hashlib.sha1(repr(r["класс"]).encode()).hexdigest()[:10]


def interest_key(r):
    """Интереснее — раньше: короче запрет (сильнее утверждение), больше
    примеров библиотеки за ним, затем класс для устойчивости порядка."""
    n = r.get("примеров")
    return (len(r.get("_cols") or r.get("запрет") or ()), -n if isinstance(n, int) else 0, repr(r["класс"]))


class _Unencodable(Exception):
    pass


def forbid_lits(form, r):
    """Запрет строки (посылки ∧ ¬цель) как список литералов решателя.
    None — запрет ложен тождественно (литерал False)."""
    T = form.sc.T
    out = []
    for j in r["_cols"]:
        a = form.atoms[j // 2] if hasattr(form, "atoms") else None
        if a is not None and a[0] == "pair" and j % 2:
            raise _Unencodable()  # ¬(P(A) ∧ P(B)) — дизъюнкция, не конъюнкция
        for at, v in form.lits(j):
            l = T.lit(at, v)
            if l is None:
                continue
            if l is False:
                return None
            out.append(l)
    return out


def _safe_forbid(form, r):
    try:
        return forbid_lits(form, r)
    except _Unencodable:
        return None


def _fixed(form):
    T = form.sc.T
    out = []
    for a, v in getattr(form, "fixed_lits", []):
        l = T.lit(a, v)
        if type(l) is int:
            out.append(l)
    return out


def _solve(s, assumptions):
    """True / False / None (решатель не ответил)."""
    if CONF_BUDGET is None:
        return s.solve(assumptions=assumptions)
    s.conf_budget(CONF_BUDGET)
    return s.solve_limited(assumptions=assumptions)


def _nvars(T):
    return max((abs(c) for cl in T.clauses for c in cl), default=0) + 1


def _subst(x, t, G):
    if x == t:
        return G
    return x


def _row_terms(form, r):
    out = set()
    for j in r["_cols"]:
        for a, _ in form.lits(j):
            out |= {x for x in a[2:] if not isinstance(x, (str, int))}
    return out


def _admissible(form, t, G, cache):
    """Терм t можно подставить вместо переменной базы G: сорт, гипотезы базы
    и условия существования t выводятся теорией (свой решатель, form.sc.s
    не трогаем)."""
    if t in cache:
        return cache[t]
    from algen.logic import decide
    T, g = form.sc.T, form.sc.T.g
    # подгруппа — тоже группа: свойства подгрупп, которых нет у G (normal и т. п.),
    # отсеются ниже — у R0 не найдётся атома
    sorts = {g.terms[G].sort} | ({"Grp.sub"} if g.terms[G].sort == "Grp.obj" else set())
    ok = t in g.terms and g.terms[t].sort in sorts
    if ok:
        fixed = list(getattr(form, "fixed_lits", []))
        need = [(tuple(_subst(x, G, t) for x in a), v) for a, v in fixed if G in a[2:]]
        need += [(("p", p, u), True) for p, u in g.requires(t)]
        s = T.solver()
        try:
            ok = all(decide(T, fixed, goal, s).kind == "выводится" for goal in need)
        finally:
            s.delete()
    cache[t] = ok
    return ok


def instances(form, report):
    """Сворачивает строки-экземпляры φ(t) по φ(G) (правило 6). Возвращает
    число свёрнутых."""
    from algen.logic import Var
    import numpy as np

    g = getattr(form.sc.T, "g", None)
    if g is None:
        return 0
    if getattr(form, "generic", None) is not None:
        return _instances_generic(form, report, g)
    vars_ = [x for x in g.terms if isinstance(x, Var)]
    m = getattr(form, "m", None)
    if len(vars_) != 1 or m is None or not hasattr(form, "index"):
        return 0
    G = vars_[0]
    base = m[:, form.fixed].all(axis=1) if getattr(form, "fixed", None) else np.ones(m.shape[0], dtype=bool)
    cache, n = {}, 0
    for r in report:
        if "_cols" not in r or r.get("свёрнута") or r["вердикт"] != "неизвестно":
            continue
        ts = _row_terms(form, r)
        if len(ts) != 1:
            continue
        (t,) = ts
        if t == G or not _admissible(form, t, G, cache):
            continue
        cols, names = [], []
        try:
            for j in r["_cols"]:
                if form.atoms[j // 2][0] == "pair":
                    raise KeyError
                a, v = form.lit(j)
                a0 = tuple(_subst(x, t, G) for x in a)
                cols.append(2 * form.index[a0] + (0 if v else 1))
                names.append(("" if v else "¬") + str(a0[1]) + "(" + ", ".join(map(str, a0[2:])) + ")")
        except KeyError:
            continue
        if (base & m[:, cols].all(axis=1)).any():
            continue  # R0 опровергнут библиотекой: φ(t) от него не следует
        r["свёрнута"] = True
        r["следует из"] = ["экземпляр: " + " & ".join(sorted(names))]
        r["экземпляр"] = {"терм": str(t), "вместо": str(G)}
        n += 1
    return n


def _instances_generic(form, report, g):
    """Экземпляры по таблице базы G (form.generic = (матрица, {свойство: атом})),
    у любой базы: строка только о свойствах одного построенного терма t.
    R0 — то же о произвольной группе G базы G с классом ALGEN_CLASS. Гипотезы:
    t — группа (сорт Grp.obj или Grp.sub), условия существования t и класс
    для t выводятся теорией; R0 не опровергнут строками базы G этого класса."""
    import os
    from algen.logic import Var, decide

    gm, gcol = form.generic
    cls = os.environ.get("ALGEN_CLASS", "")
    if cls and cls not in gcol:
        return 0
    rows_ok = gm[:, 2 * gcol[cls]] if cls else None
    T = form.sc.T
    fixed = list(getattr(form, "fixed_lits", []))
    cache, n = {}, 0
    for r in report:
        if "_cols" not in r or r.get("свёрнута") or r["вердикт"] != "неизвестно":
            continue
        lits = [l for j in r["_cols"] for l in form.lits(j)]
        ts = {a[2] if len(a) > 2 else None for a, _ in lits}
        if len(ts) != 1 or any(a[0] != "p" or a[1] not in gcol for a, _ in lits):
            continue
        if any(form.atoms[j // 2][0] == "pair" for j in r["_cols"]):
            continue
        (t,) = ts
        if isinstance(t, Var) or t not in g.terms:
            continue
        if t not in cache:
            ok = g.terms[t].sort in ("Grp.obj", "Grp.sub")
            if ok:
                need = [(("p", p, u), True) for p, u in g.requires(t)]
                if cls:
                    need.append((("p", cls, t), True))
                sv = T.solver()
                try:
                    ok = all(decide(T, fixed, goal, sv).kind == "выводится" for goal in need)
                finally:
                    sv.delete()
            cache[t] = ok
        if not cache[t]:
            continue
        cols = [2 * gcol[a[1]] + (0 if v else 1) for a, v in lits]
        hit = gm[:, cols].all(axis=1)
        if rows_ok is not None:
            hit &= rows_ok
        if hit.any():
            continue
        names = sorted(("" if v else "¬") + f"{a[1]}(G)" for a, v in lits)
        r["свёрнута"] = True
        r["следует из"] = ["экземпляр: " + " & ".join(names)]
        r["экземпляр"] = {"терм": str(t), "вместо": "G" + (f", класс {cls}" if cls else "")}
        n += 1
    return n


def compress(form, report, refuted=(), key=interest_key, use_instances=True):
    """Жадный базис. refuted — номера опровергнутых вопросов: они не входят в
    фон, их строка остаётся несвёрнутой с полем "опровергнут"."""
    from pysat.solvers import Solver

    refuted = set(refuted)
    T = form.sc.T
    fixed = _fixed(form)
    seen = {}
    for r in report:
        r["№"] = row_id(r)
        r["свёрнута"] = False
        r["следует из"] = []
        r["сжатие"] = VERSION
        if r["№"] in refuted:
            r["опровергнут"] = True
    if use_instances:
        instances(form, report)
    rows = sorted([r for r in report if "_cols" in r and not r.get("экземпляр")], key=key)

    # вопросы: теория + оставленные вопросы под селекторами
    sq = T.solver()
    # селекторы — номера выше всех переменных теории, гипотез и запретов
    # (T.lit заводит переменные лениво, поэтому смотрим и на сами запреты)
    nv = max([_nvars(T)] + [abs(l) + 1 for l in fixed]
             + [abs(l) + 1 for r in rows for l in (_safe_forbid(form, r) or [])])
    # факты: только оставленные факты
    sf = Solver(name="g4")
    nf = nv
    sel_q, sel_f = {}, {}
    copies = []
    try:
        for r in rows:
            kind = r["вердикт"]
            if kind not in ("неизвестно", "выводится") or r["№"] in refuted:
                continue
            if r["№"] in seen:  # копия класса (контрапозиция): статус — как у представителя
                copies.append(r)
                continue
            seen[r["№"]] = r
            try:
                F = forbid_lits(form, r)
            except _Unencodable:
                continue
            if F is None:
                continue
            s, sels = (sq, sel_q) if kind == "неизвестно" else (sf, sel_f)
            ans = _solve(s, fixed + F + list(sels))
            if ans is False:
                core = set(s.get_core() or [])
                deps = sorted(sels[x] for x in sels if x in core)
                if kind == "неизвестно" and not deps:
                    # следует из одной теории — значит, вердикт «неизвестно»
                    # неверен; не сворачиваем, а помечаем
                    r["ОШИБКА сжатия"] = "запрет следует из теории без вопросов"
                    continue
                if deps:
                    r["свёрнута"], r["следует из"] = True, deps
                    continue
            # ans True или None: строка остаётся и входит в фон
            if kind == "неизвестно":
                nv += 1
                sq.add_clause([-nv] + [-l for l in F])
                sel_q[nv] = r["№"]
            else:
                nf += 1
                sf.add_clause([-nf] + [-l for l in F])
                sel_f[nf] = r["№"]
    finally:
        sq.delete()
        sf.delete()
    for r in copies:
        rep = seen[r["№"]]
        r["свёрнута"], r["следует из"] = rep["свёрнута"], list(rep["следует из"])
    return report


def reopen(report, refuted):
    """Номера строк, которые надо развернуть, если вопросы refuted опровергнуты
    (все, кто держится на них, транзитивно). Сами строки помечаются."""
    by = {}
    for r in report:
        for d in r.get("следует из", []):
            by.setdefault(d, []).append(r)
    out, done, stack = set(), set(), list(refuted)
    while stack:
        x = stack.pop()
        for r in by.get(x, []):
            if id(r) in done:
                continue
            done.add(id(r))
            r["свёрнута"] = False
            r["вернулась"] = sorted(set(r.get("вернулась", [])) | {x})
            if r["№"] not in out:
                out.add(r["№"])
                stack.append(r["№"])
    return out


def verify(form, report, sample=None, rng=None):
    """Независимая проверка графа на выборке свёрнутых строк: новый решатель,
    в фоне только строки из "следует из" (и теория для вопросов). Возвращает
    список нарушений; пустой — граф верен."""
    from pysat.solvers import Solver

    T = form.sc.T
    fixed = _fixed(form)
    by = {}
    for r in report:
        if not r.get("свёрнута"):
            by.setdefault(r["№"], r)
    folded = [r for r in report if r.get("свёрнута") and not r.get("экземпляр")]
    if sample is not None and len(folded) > sample:
        import random
        folded = (rng or random.Random(0)).sample(folded, sample)
    bad = []
    inst = [r for r in report if r.get("экземпляр")]
    if inst:  # экземпляры: пересчитать заново на копиях и сравнить
        import copy
        cp = [copy.copy(r) for r in inst]
        for r in cp:
            r["свёрнута"] = False
        instances(form, cp)
        bad += [(r["№"], "экземпляр не подтверждается") for r in cp if not r.get("экземпляр") or not r["свёрнута"]]
    for r in folded:
        deps = [by.get(d) for d in r["следует из"]]
        if any(d is None for d in deps):
            bad.append((r["№"], "источник свёрнут или потерян"))
            continue
        if any(d["№"] != r["№"] and interest_key(d) >= interest_key(r) for d in deps):
            bad.append((r["№"], "источник стоит не раньше"))
            continue
        if any(d["вердикт"] != r["вердикт"] for d in deps):
            bad.append((r["№"], "источник другого вида"))
            continue
        s = T.solver() if r["вердикт"] == "неизвестно" else Solver(name="g4")
        try:
            for d in deps:
                s.add_clause([-l for l in forbid_lits(form, d)])
            if s.solve(assumptions=fixed + forbid_lits(form, r)):
                bad.append((r["№"], "не следует из источников"))
        finally:
            s.delete()
    return bad
