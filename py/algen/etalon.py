"""Прогон эталона data/etalon/эталон.jsonl через вывод на SAT.

Эталон — мерило генератора (docs/ПЕРЕДЕЛКА.md): факты с известным ответом.
Для каждого факта вывод (algen.logic) даёт вердикт, и он сравнивается с
ответом:

* «верно» должно выводиться, «ложно» — опровергаться;
* «открыто» не должно ни выводиться, ни опровергаться;
* вывод верного или опровержение ложного — ОШИБКА базы, а не промах.

Вывод сам по себе опровергает только то, что противоречит правилам. Если он
ответа не дал, ищется контрпример в библиотеке (algen.library): пара (G, N),
где посылки верны, а цель ложна. «Ложно → неизвестно» считается промахом, а
не ошибкой.

    cd py && python3 -m algen.etalon
"""

import argparse
import json
import re
import sys
from collections import Counter

from .library import Library, Search
from .logic import DATA, Graph, Theory, Vocab, decide

ETALON = DATA / "etalon" / "эталон.jsonl"
SORTS = {"grp": {"Grp": ("Grp.obj", None), "Sub": ("Grp.sub", "ambient"), "Fam": ("Grp.fam", None),
                 "Mor": ("Grp.mor", ("dom", "cod")),
                 "GSet": ("Grp.gset", "ambient"), "Pt": ("Grp.pt", "ambient"),
                 "Elt": ("Grp.elt", "ambient"), "Diag": ("Grp.diag", None), "Num": ("Grp.num", None), "Pres": ("Grp.pres", None),
                 # натуральные и простые числа — сорт Num (у простых — посылка num-prime)
                 "ℕ": ("Grp.num", None), "Prime": ("Grp.num", None),
                 "Act": ("Grp.act", ("dom", "cod"))}}
# Короткие обозначения конструкций в записи эталона.
OPS = {"grp": {"Z": "center", "Φ": "frattini", "Inn": "inn", "Aut": "aut", "ab": "ab", "∏": "prod-fam", "⊕": "sum-fam",
               "ker": "ker", "im": "im", "commutator": "commutator", "center": "center",
               "A": "alt", "S": "sym-n", "C": "cyc", "fact": "num-fact",
               "gcd": "num-gcd", "phi": "num-phi", "n_p": "num-sylow", "D": "dih"}}
INFIX = {"grp": {"×": "prod", "∗": "freeprod", "≀": "wreath", "/": "quotient"}}


class Unsupported(Exception):
    pass


def split_top(s, sep):
    """Разбить по sep вне скобок."""
    out, depth, cur = [], 0, ""
    for ch in s:
        depth += ch == "("
        depth -= ch == ")"
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return [x.strip() for x in out + [cur] if x.strip()]


def _amb(g, t):
    return g.terms[t].links.get("ambient")


def _num(g, s, names, section):
    """Числовые термы: |G|, |H|, |G : H|, |x|, |HK| (H, K — имена подгрупп), a · b."""
    parts = split_top(s, "·")
    if len(parts) > 1:
        t = _num(g, parts[0], names, section)
        for p in parts[1:]:
            t = g.given(g.make("num-mul", [t, _num(g, p, names, section)]))
        return t
    s = s.strip()
    if not (s.startswith("|") and s.endswith("|")):
        return None
    inner = s[1:-1].strip()
    if ":" in inner:
        a, b = (term(g, x, names, section) for x in inner.split(":", 1))
        return g.given(g.make("index", [a, b]))
    for i in range(1, len(inner)):
        a, b = inner[:i].strip(), inner[i:].strip()
        if a in names and b in names and g.terms[names[a]].sort == "Grp.sub":
            return g.given(g.make("prod-card", [_amb(g, names[a]), names[a], names[b]]))
    t = term(g, inner, names, section)
    if g.terms[t].sort == "Grp.elt":
        return g.given(g.make("eltord", [_amb(g, t), t]))
    return g.given(g.make("ord", [t]))


def _num_const(g, n):
    """Числовая константа n — нульместная конструкция «num:n» сорта Num."""
    op = f"num:{n}"
    if op not in g.v.cons:
        g.v.cons[op] = {"id": op, "in": [], "out": {"sort": "Grp.num"}, "gives": None, "commutative": False}
    return g.given(g.make(op, []))


_ARITH = re.compile(r"\s*(\d+|[A-Za-z_][\w-]*\s*\((?:[^()]|\([^()]*\))*\)|[A-Za-z_]\w*|\|[^|]*\||[-+^·()])")


def _arith(g, s, names, section):
    """Арифметика чисел: a + b, a − b, aᵇ (a^b), произведение подряд (2p, p q, p^2 q^2)."""
    toks, i = [], 0
    s = s.replace("−", "-")
    while i < len(s):
        m = _ARITH.match(s, i)
        if not m:
            if s[i:].strip() == "":
                break
            raise Unsupported(f"терм {s!r}")
        toks.append(m.group(1).strip())
        i = m.end()
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def atom():
        nonlocal pos
        t = peek()
        if t is None:
            raise Unsupported(f"терм {s!r}")
        pos += 1
        if t == "(":
            x = expr()
            if peek() != ")":
                raise Unsupported(f"терм {s!r}")
            pos += 1
            return x
        if t.isdigit():
            return _num_const(g, int(t))
        if t == s.strip():
            raise Unsupported(f"терм {s!r}")
        return term(g, t, names, section)

    def factor():
        nonlocal pos
        x = atom()
        if peek() == "^":
            pos += 1
            x = g.given(g.make("num-pow", [x, atom()]))
        return x

    def prod():
        nonlocal pos
        x = factor()
        while peek() is not None and peek() not in ("+", "-", ")"):
            if peek() == "·":
                pos += 1
            x = g.given(g.make("num-mul", [x, factor()]))
        return x

    def expr():
        nonlocal pos
        x = prod()
        while peek() in ("+", "-"):
            op = "num-add" if peek() == "+" else "num-sub"
            pos += 1
            x = g.given(g.make(op, [x, prod()]))
        return x

    t = expr()
    if pos != len(toks) or t is None or g.terms[t].sort != "Grp.num":
        raise Unsupported(f"терм {s!r}")
    return t


def term(g, s, names, section):
    try:
        return _term(g, s, names, section)
    except Unsupported:
        if not re.search(r"[\d+\-−^ ]", s.strip()):
            raise
        try:
            return _arith(g, s.strip(), names, section)
        except (Unsupported, AttributeError, KeyError):
            pass
        raise


def _term(g, s, names, section):
    s = s.strip()
    if s in names:
        return names[s]
    m = re.fullmatch(r"Out\s*\((.*)\)", s)
    if m:  # Out(X) = Aut(X) / Inn(X)
        return _term(g, f"Aut({m.group(1)}) / Inn({m.group(1)})", names, section)
    m = re.fullmatch(r"(?:num:)?(\d+)(?:\(\))?", s)
    if m and "Grp.num" in str(SORTS.get(section, "")):
        return _num_const(g, int(m.group(1)))
    if s.startswith("|") or "·" in s:
        t = _num(g, s, names, section)
        if t is not None:
            return t
    for sym, op in (("∩", "meet"),):
        parts = split_top(s, sym)
        if len(parts) == 2:
            a, b = (term(g, x, names, section) for x in parts)
            return g.given(g.make(op, [_amb(g, a), a, b]))
    for sym, op in INFIX[section].items():
        parts = split_top(s, sym)
        if len(parts) == 2:
            t = g.make(op, [term(g, p, names, section) for p in parts])
            break
    else:
        m = re.fullmatch(r"(\w[\w-]*|∏|⊕)\s*\((.*)\)", s) or re.fullmatch(r"(∏|⊕)\s*(\w+)", s)
        op = m and (OPS[section].get(m.group(1)) or (m.group(1) if m.group(1) in g.v.cons else None))
        if not op:
            raise Unsupported(f"терм {s!r}")
        t = g.make(op, [term(g, a, names, section) for a in split_top(m.group(2), ",")])
    if t is None:
        raise Unsupported(f"терм {s!r} не строится")
    return g.given(t)


REL_INFIX = (("⩽", "le", False), ("≤", "le", False), ("⩾", "le", True), ("≥", "le", True),
         ("≅", "iso", False), ("↪", "embeds", False), ("=", "=", False),
         # строгие и «≠» — отрицания: a < b ⇔ ¬(b ⩽ a), a > b ⇔ ¬(a ⩽ b), a ≠ b ⇔ ¬(a = b)
         ("<", "le", "¬flip"), (">", "le", "¬"), ("≠", "=", "¬"), ("∤", "num-divides", "¬"))
# «=» и ⩽ по сорту левой части: числа — num-eq / num-le, элементы — eq-elt, подгруппы — eq-sub
BY_SORT = {("=", "Grp.num"): "num-eq", ("=", "Grp.elt"): "eq-elt", ("=", "Grp.sub"): "eq-sub",
           ("le", "Grp.num"): "num-le"}


def _infix(s):
    """Инфиксная запись отношения вне скобок: «A ⩽ B», «X ≅ Y», «H ↪ G»."""
    depth = 0
    for i, ch in enumerate(s):
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            for sym, rel, flip in REL_INFIX:
                if s.startswith(sym, i):
                    a, b = s[:i].strip(), s[i + len(sym):].strip()
                    neg = isinstance(flip, str) and flip.startswith("¬")
                    if isinstance(flip, str):
                        flip = flip.endswith("flip")
                    return ((rel, b, a) if flip else (rel, a, b)) + (neg,)
    return None


def literal(g, s, names, section):
    s = s.strip()
    value = not s.startswith("¬")
    body = s.lstrip("¬").strip()
    if body.startswith("(") and body.endswith(")") and _infix(body[1:-1]):
        body = body[1:-1].strip()
    inf = _infix(body)
    if inf:
        rel, a, b, neg = inf
        value = value != neg
        ta, tb = term(g, a, names, section), term(g, b, names, section)
        rel = BY_SORT.get((rel, g.terms[ta].sort), rel)
        if rel not in g.v.rels:
            raise Unsupported(f"нет в словаре: {rel}")
        return ("r", rel, ta, tb), value
    m = re.fullmatch(r"([\w-]+)\((.*)\)", body)
    if not m:
        raise Unsupported(f"литерал {s!r}")
    args = [term(g, a, names, section) for a in split_top(m.group(2), ",")]
    if m.group(1) == "prime" and len(args) == 1 and g.terms[args[0]].sort == "Grp.num":
        return ("p", "num-prime", args[0]), value
    if m.group(1) in g.v.props and len(args) == 1:
        return ("p", m.group(1), args[0]), value
    if m.group(1) in g.v.rels:
        return ("r", m.group(1), *args), value
    raise Unsupported(f"нет в словаре: {m.group(1)}")


def scheme(vocab, fact):
    """Запись эталона → граф, посылки, цель."""
    section = fact["раздел"]
    if section not in SORTS:
        raise Unsupported(f"раздел {section}")
    g, names, prem = Graph(vocab), {}, []
    for decl in fact["условие"].split(";"):
        head, _, lits = decl.partition("|")
        m = re.fullmatch(r"\s*∀\s*(\w+(?:\s*,\s*\w+)*)\s*:\s*(\w+)(?:\((.+)\))?\s*", head)
        if not m:
            raise Unsupported(f"объявление {head!r}")
        many, sort, parents = m.groups()
        if sort not in SORTS[section]:
            raise Unsupported(f"сорт {sort}")
        s, link = SORTS[section][sort]
        links = {}
        if parents:
            ps = split_top(parents, ",")
            keys = link if isinstance(link, tuple) else (link,)
            if len(ps) != len(keys):
                raise Unsupported(f"объявление {head!r}")
            # родитель — переменная или терм: «∀ H : Sub(A ∗ B)»
            links = {k: names[x] if x in names else term(g, x, names, section) for k, x in zip(keys, ps)}
        # «∀ H, K : Sub(G) | …» — несколько переменных одного сорта, посылки после всех
        for name in (x.strip() for x in many.split(",")):
            names[name] = g.var(name, s, **links)
            if s == "Grp.gset":  # G-множество непусто: точка x_A для правил о стабилизаторах
                g.var(f"x_{name}", "Grp.pt", ambient=names[name])
            if sort == "Prime":
                prem.append((("p", "num-prime", names[name]), True))
        prem += [literal(g, x, names, section) for x in split_top(lits, ",")]
    goal = literal(g, fact["цель"], names, section) if fact.get("цель") else None
    return g, prem, goal


EXPECT = {"верно": "выводится", "ложно": "опровергается", "открыто": "неизвестно"}
WRONG = {"верно": {"опровергается", "противоречие"}, "ложно": {"выводится", "противоречие"},
         "открыто": {"выводится", "опровергается", "противоречие"}}


def judge(answer, kind):
    if kind == EXPECT[answer]:
        return "закрыто верно" if answer != "открыто" else "дошло до остатка"
    if kind in WRONG[answer]:
        return "ОШИБКА"
    return "промах"


def run(facts, grow=1, search=True):
    vocabs, report = {}, []
    lib = None
    for f in facts:
        row = {"id": f["id"], "ответ": f["ответ"]}
        try:
            v = vocabs.get(f["раздел"]) or vocabs.setdefault(f["раздел"], Vocab.section(f["раздел"]))
            g, prem, goal = scheme(v, f)
        except (Unsupported, FileNotFoundError) as e:
            report.append({**row, "итог": "не разбирается", "почему": str(e)})
            continue
        theory = Theory(g, grow=grow)
        verdict = decide(theory, prem, goal)
        kind, core = verdict.kind, verdict.core
        if kind == "неизвестно" and search and f["раздел"] == "grp":
            lib = lib or Library()
            found = Search(g, theory, lib).witnesses(prem, goal)
            if found:
                kind = "опровергается"
                row["контрпример"] = [", ".join(f"{k} = {v}" for k, v in w["подстановка"].items())
                                      for w in found]
        row.update(итог=judge(f["ответ"], kind), вердикт=kind,
                   ядро=[f"{'' if val else '¬'}{a[1]}({', '.join(map(str, a[2:]))})"
                         for a, val in core or []])
        if verdict.kind == "выводится" and len(verdict.core) < len(prem):
            row["лишние посылки"] = len(prem) - len(verdict.core)
        report.append(row)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--эталон", dest="etalon", default=str(ETALON))
    ap.add_argument("--достройка", dest="grow", type=int, default=1)
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    with open(a.etalon, encoding="utf-8") as f:
        facts = [json.loads(line) for line in f if line.strip()]
    report = run(facts, a.grow)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    for r in report:
        extra = r.get("почему") or (f"{r['вердикт']}; " + (
            f"контрпример: {r['контрпример'][0]}" if "контрпример" in r
            else f"ядро: {', '.join(r['ядро']) or '—'}"))
        print(f"{r['id']:10} {r['ответ']:8} {r['итог']:17} {extra}")
    print("\n" + ", ".join(f"{k} {v}" for k, v in Counter(r["итог"] for r in report).most_common()))


if __name__ == "__main__":
    main()
