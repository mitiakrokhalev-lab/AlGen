"""Цели-формулы карточек: ¬, ∧, ∨, ⇒, ⇔ и ∃ со свидетелями.

Формула приводится к КНФ. Каждая клауза — обычное условие генератора:
посылки карточки и отрицания всех литералов клаузы, кроме одного, ⇒ этот
литерал. Карточка выводится, если выводится каждая клауза; опровергается,
если библиотека опровергает хотя бы одну.

∃ y : S | ψ(y) — литерал клаузы особого вида. Он выводится, если ψ(t)
выводится для какого-то терма t сорта S: конструкции словаря, применённой к
термам условия (в том числе конструкции-свидетели вроде free-cover(G) или
cayley(G)), — или если библиотека даёт пример (для ∃ без свободных
переменных, например «существует к. п. группа с неразрешимой проблемой слов»).

    формула: «abelian(G) ∨ ¬cyclic(H)», «free(F) ∧ surjective(π)»,
             «∃ F : Grp | free(F) ∧ ∃ π : Mor(F, G) | surjective(π)»
"""

import re

from .etalon import SORTS, Unsupported, literal, split_top


def _strip(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")") and _balanced(s[1:-1]):
        s = s[1:-1].strip()
    return s


def _balanced(s):
    d = 0
    for ch in s:
        d += ch == "("
        d -= ch == ")"
        if d < 0:
            return False
    return d == 0


def _split(s, op):
    """Разбить по связке op вне скобок; ∃ поглощает всё справа от «|»."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(s):
        if s.startswith("∃", i) and depth == 0 and op != "∃":
            # квантор до конца строки: связки внутри него — его тело
            cur += s[i:]
            break
        ch = s[i]
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0 and s.startswith(op, i):
            out.append(cur)
            cur = ""
            i += len(op)
            continue
        cur += ch
        i += 1
    return [x.strip() for x in out + [cur]]


def parse(s):
    """Строка → дерево: ("lit", s), ("not", x), ("and", [..]), ("or", [..]),
    ("ex", имя, сорт, родители, тело)."""
    s = _strip(s)
    if s.startswith("∃"):
        head, body = _split(s[1:], "|")[0], "|".join(_split(s[1:], "|")[1:])
        m = re.fullmatch(r"\s*(\w+)\s*:\s*(\w+)(?:\((.*)\))?\s*", head, re.S)
        if not m or not body:
            raise Unsupported(f"квантор {s!r}")
        name, sort, parents = m.groups()
        return ("ex", name, sort, split_top(parents or "", ","), parse(body))
    for op, tag in (("⇔", "iff"), ("⇒", "imp"), ("∨", "or"), ("∧", "and")):
        parts = _split(s, op)
        if len(parts) > 1:
            if tag == "iff":
                a, b = parse(parts[0]), parse(op.join(parts[1:]))
                return ("and", [("or", [("not", a), b]), ("or", [("not", b), a])])
            if tag == "imp":
                return ("or", [("not", parse(parts[0])), parse(op.join(parts[1:]))])
            return (tag, [parse(p) for p in parts])
    if s.startswith("¬") and not re.fullmatch(r"¬\s*[\w-]+\(.*\)", s):
        return ("not", parse(s[1:]))
    return ("lit", s)


def _nnf(t, neg=False):
    tag = t[0]
    if tag == "lit":
        if not neg:
            return t
        s = t[1]
        return ("lit", s[1:].strip() if s.startswith("¬") else "¬" + s)
    if tag == "not":
        return _nnf(t[1], not neg)
    if tag in ("and", "or"):
        flip = {"and": "or", "or": "and"}[tag] if neg else tag
        return (flip, [_nnf(x, neg) for x in t[1]])
    if tag == "ex":
        if neg:
            raise Unsupported("¬∃ (∀ в цели) не поддерживается")
        return ("ex", t[1], t[2], t[3], _nnf(t[4]))
    raise Unsupported(f"узел {tag}")


def cnf(t):
    """КНФ: список клауз, клауза — список узлов («lit» или «ex»)."""
    t = _nnf(t)

    def go(t):
        if t[0] in ("lit", "ex"):
            return [[t]]
        if t[0] == "and":
            return [c for x in t[1] for c in go(x)]
        out = [[]]
        for x in t[1]:
            out = [a + b for a in out for b in go(x)]
        return out
    return go(t)


def literals_of(g, names, clause):
    """Литералы клаузы без ∃: [(атом, значение)]."""
    return [literal(g, x[1], names, "grp") for x in clause if x[0] == "lit"]


def witnesses(g, names, sort, parents):
    """Кандидаты в свидетели ∃ y : sort(parents): термы условия этого сорта и
    конструкции словаря глубины 1 над переменными и термами условия."""
    s, link = SORTS["grp"][sort]
    keys = link if isinstance(link, tuple) else ((link,) if link else ())
    from .etalon import term
    want = {k: (names[p] if p in names else term(g, p, dict(names), "grp"))
            for k, p in zip(keys, parents)} if parents else {}
    # аргументы — переменные, термы условия (глубина 0) и уже выбранные свидетели
    base = list(dict.fromkeys([t for t in g.terms if g.terms[t].depth == 0] + list(names.values())))
    out = [t for t in base if g.terms[t].sort == s]
    from itertools import product as cart
    for op, c in g.v.cons.items():
        n = len(c["in"])
        o = c["out"] if isinstance(c["out"], dict) else {"sort": c["out"]}
        if n > 2 or not g.v.fits(o["sort"], s):
            continue
        for args in cart(base, repeat=n):
            t = g.make(op, list(args))
            if t is not None and g.terms[t].sort == s and t not in out:
                out.append(t)
    return [t for t in out if all(g.terms[t].links.get(k) == v for k, v in want.items())]


def is_formula(s):
    """Цель — формула, а не один литерал."""
    s = s or ""
    return any(ch in s for ch in "∧∨⇒⇔∃") or s.strip().startswith("¬(")


def expand(g, names, ex):
    """Варианты ∃-литерала: списки литералов тела после подстановки свидетелей
    (вложенные ∃ раскрываются так же). Тело — конъюнкция литералов и ∃."""
    _, name, sort, parents, body = ex
    out = []
    for t in witnesses(g, names, sort, parents):
        nm = {**names, name: t}
        parts = body[1] if body[0] == "and" else [body]
        lits, nested = [], []
        try:
            for x in parts:
                if x[0] == "lit":
                    lits.append(literal(g, x[1], nm, "grp"))
                elif x[0] == "ex":
                    nested.append(x)
                else:
                    raise Unsupported("в теле ∃ — только ∧ литералов и ∃")
        except Unsupported:
            continue
        if not nested:
            out.append(lits)
            continue
        alts = [lits]
        for y in nested:
            alts = [a + b for a in alts for b in expand(g, nm, y)]
        out += alts
    return out


def library_example(vocab, lib, ex):
    """∃ без свободных переменных (цепочка ∃ x : Grp | … ∧ ∃ y : Grp | …, не больше
    двух групп): пример из библиотеки, где тело верно по записям или выводится из них."""
    from .library import Search
    from .logic import Graph, Theory, decide
    g, names, parts = Graph(vocab), {}, []

    def walk(x):
        _, name, sort, parents, body = x
        if parents or sort != "Grp":
            raise Unsupported("пример ∃: только группы без параметров")
        s, _ = SORTS["grp"][sort]
        names[name] = g.var(name, s)
        for y in (body[1] if body[0] == "and" else [body]):
            if y[0] == "lit":
                parts.append(y)
            elif y[0] == "ex":
                walk(y)
            else:
                raise Unsupported("в теле ∃ — только ∧ литералов и ∃")
    try:
        walk(ex)
    except Unsupported:
        return None
    if len(names) > 2:
        return None
    lits = [literal(g, x[1], names, "grp") for x in parts]
    T = Theory(g, grow=1, extra=[a for a, _ in lits if a[0] == "r"])
    S = Search(g, T, lib)
    s = T.solver()
    fallback = None
    try:
        for env in S._assign(0, {}):
            facts, hard = S.facts(env)
            if any(facts.get(a) == (not val) for a, val in lits):
                continue
            known = [(a, x) for a, x in facts.items() if a not in hard]
            name = ", ".join(f"{t} = {S._name(im)}" for t, im in env.items())
            if all(facts.get(a) == val and a not in hard
                   or decide(T, known, (a, val), s).kind == "выводится" for a, val in lits):
                return name
            # пример держится на трудных (литературных) фактах записи — запасной
            if fallback is None:
                every = list(facts.items())
                used = [a for a, val in lits if a in hard and facts.get(a) == val]
                if all(facts.get(a) == val or decide(T, every, (a, val), s).kind == "выводится"
                       for a, val in lits):
                    fallback = name + " (опирается на литературные факты записи" + (": " + ", ".join(a[1] for a in used) if used else "") + ")"
    finally:
        s.delete()
    return fallback
