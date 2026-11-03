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
6. reopen: если вопрос опровергнут, все строки, которые держались на нём
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


def compress(form, report, refuted=(), key=interest_key):
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
    rows = sorted([r for r in report if "_cols" in r], key=key)

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
    try:
        for r in rows:
            kind = r["вердикт"]
            if kind not in ("неизвестно", "выводится") or r["№"] in refuted:
                continue
            if r["№"] in seen:  # та же строка класса уже есть: держится на ней
                r["свёрнута"], r["следует из"] = True, [seen[r["№"]]]
                continue
            seen[r["№"]] = r["№"]
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
    return report


def reopen(report, refuted):
    """Номера строк, которые надо развернуть, если вопросы refuted опровергнуты
    (все, кто держится на них, транзитивно). Сами строки помечаются."""
    by = {}
    for r in report:
        for d in r.get("следует из", []):
            by.setdefault(d, []).append(r)
    out, stack = set(), list(refuted)
    while stack:
        x = stack.pop()
        for r in by.get(x, []):
            if r["№"] not in out:
                out.add(r["№"])
                r["свёрнута"] = False
                r["вернулась"] = sorted(set(r.get("вернулась", [])) | {x})
                stack.append(r["№"])
    return out


def verify(form, report, sample=None, rng=None):
    """Независимая проверка графа на выборке свёрнутых строк: новый решатель,
    в фоне только строки из "следует из" (и теория для вопросов). Возвращает
    список нарушений; пустой — граф верен."""
    from pysat.solvers import Solver

    T = form.sc.T
    fixed = _fixed(form)
    by = {r["№"]: r for r in report if not r.get("свёрнута")}
    folded = [r for r in report if r.get("свёрнута")]
    if sample is not None and len(folded) > sample:
        import random
        folded = (rng or random.Random(0)).sample(folded, sample)
    bad = []
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
