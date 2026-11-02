"""Покрытие: ложится ли каждая известная задача на какую-нибудь схему перебора.

Задачи — карточки архива (data/archive/<раздел>/*.jsonl) с машинной записью
«условие» и «цель». Задача покрыта списком схем, если есть схема, у которой
после переименования переменных

* те же переменные (сорта и связи: подгруппа чего, гомоморфизм откуда куда);
* есть все термы задачи;
* все литералы задачи — свойства или отношения ⩽, =, ≅;
* литералов (посылки + цель) не больше k + 1, где k — число посылок перебора.

Остальные задачи — красные флаги списка схем с причиной.

    cd py && python3 -m algen.coverage --посылок 2 --подробно
"""

import argparse
import json
from collections import Counter, defaultdict
from itertools import permutations
from pathlib import Path

from .batch import read_schemes
from .etalon import Unsupported, scheme, term
from .logic import DATA, App, Var, Vocab


def shape(vocab, decl, terms=(), lits=()):
    """(переменные [(имя, сорт, связи)], множество термов-строк, литералы)."""
    g, prem, goal = scheme(vocab, {"раздел": "grp", "условие": decl, "цель": None})
    names = {str(t): t for t in g.terms}
    for x in terms:
        term(g, x, names, "grp")
    vs = [(t.name, g.terms[t].sort, {k: str(v) for k, v in g.terms[t].links.items()})
          for t in g.terms if isinstance(t, Var)]
    apps = {t for t in g.terms if isinstance(t, App)}
    return g, vs, apps, prem


def _rename(t, ren):
    if isinstance(t, str):
        return t
    if isinstance(t, Var):
        return ren.get(t.name, t.name)
    return f"{t.op}(" + ", ".join(_rename(a, ren) for a in t.args) + ")"


class Schemes:
    """Схемы из таблиц баз (algen.table): база + замкнутый набор термов её вселенной."""

    def __init__(self, vocab, path=None):
        from . import table as TB
        self.items = []
        for b, decl in TB.BASES.items():
            g, vs, apps, _ = shape(vocab, decl, TB.universe(vocab, b))
            self.items.append((b, vs, {_rename(t, {}) for t in apps}))

    def find(self, vs, terms):
        """База, во вселенной которой есть термы terms (строки с именами задачи)."""
        for sid, svs, sterms in self.items:
            if len(svs) != len(vs):
                continue
            for perm in permutations(range(len(svs))):
                ren = {vs[i][0]: svs[perm[i]][0] for i in range(len(vs))}
                ok = all(vs[i][1] == svs[perm[i]][1] and
                         {k: ren.get(v, v) for k, v in vs[i][2].items()} == svs[perm[i]][2]
                         for i in range(len(vs)))
                if ok and all(_rename(t, ren) in sterms for t in terms):
                    return sid
        return None


class _Named(str):
    """Терм, уже записанный строкой (для find: _rename строки — она сама)."""


def _sub(t):
    out = {t}
    if isinstance(t, App):
        for a in t.args:
            out |= _sub(a)
    return out


def cards(root):
    for p in sorted(Path(root).glob("*.jsonl")):
        for line in p.read_text(encoding="utf-8").splitlines():
            if line.strip():
                yield p.stem, json.loads(line)


def _split_top(s, sep):
    out, d, cur = [], 0, ""
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in "([":
            d += 1
        elif ch in ")]":
            d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(cur.strip()); cur = ""; i += len(sep); continue
        cur += ch; i += 1
    out.append(cur.strip())
    return out


def _neg(x):
    x = x.strip()
    if x.startswith("(") and x.endswith(")"):
        x = x[1:-1].strip()
    return x[1:].strip() if x.startswith("¬") else "¬" + x


def _add_prem(cond, lit):
    head, bar, lits = cond.rpartition("|")
    if not bar or _split_top(lits, ";")[-1].strip().startswith("∀"):
        return f"{cond} | {lit}"
    return f"{head}| {lits.strip()}, {lit}" if lits.strip() else f"{head}| {lit}"


def _exists(goal):
    """«∃ G : Grp | A ∧ ∃ H : Grp | B ∧ C» → («∀ G : Grp; ∀ H : Grp», [A, B, C]) или None."""
    decls, lits, todo = [], [], [goal.strip()]
    while todo:
        x = todo.pop(0).strip()
        if x.startswith("∃"):
            parts = _split_top(x[1:], "|")
            if len(parts) < 2:
                return None
            decls.append("∀ " + parts[0].strip())
            todo = [y for y in _split_top("|".join(parts[1:]), "∧")] + todo
        else:
            lits.append(x)
    return ("; ".join(decls), lits) if decls and lits else None


# Свидетели существования (конструкции словаря с заметкой «свидетель»):
# «∃ H … » в цели заменяется термом-свидетелем.
WITNESS = [
    (r"∃ (\w+) : Grp \| two-generated\(\1\) ∧ embeds\((\w+), \1\)",
     lambda m: f"two-generated(hnn-hull({m[2]})) ∧ embeds({m[2]}, hnn-hull({m[2]}))"),
    (r"∃ (\w+) : Grp \| fin-pres\(\1\) ∧ embeds\((\w+), \1\)",
     lambda m: f"fin-pres(higman-hull({m[2]})) ∧ embeds({m[2]}, higman-hull({m[2]}))"),
    (r"∃ (\w+) : Mor\((\w+), sym\(\2\)\) \| injective\(\1\)",
     lambda m: f"injective(cayley({m[2]}))"),
    (r"∃ (\w+) : Grp \| free\(\1\) ∧ ∃ (\w+) : Mor\(\1, (\w+)\) \| surjective\(\2\)",
     lambda m: f"free(free-cover({m[3]})) ∧ surjective(free-cover-map({m[3]}))"),
]


def _witness(goal):
    import re
    for pat, rep in WITNESS:
        m = re.fullmatch(pat, goal.strip())
        if m:
            return rep(m)
    return None


def variants(card):
    """Карточка с целью «L ⇔ R» или «A ∨ B» — несколько карточек с одной целью:
    L ⇒ R и R ⇒ L; ¬A ⇒ B. Остальные — как есть."""
    goal, cond = card.get("цель"), card.get("условие")
    w = cond and goal and _witness(goal)
    if w:
        return variants({**card, "цель": w})
    if goal and not cond and goal.strip().startswith("∃"):
        # пример: набор литералов, который реализует группа библиотеки,
        # — опровергнутый запрет «l₁, …, lₙ₋₁ ⇒ ¬lₙ»
        ex = _exists(goal)
        if ex:
            decl, lits = ex
            c = decl + (" | " + ", ".join(lits[:-1]) if len(lits) > 1 else "")
            return [{**card, "условие": c, "цель": _neg(lits[-1])}]
    if not goal or not cond:
        return [card]
    parts = _split_top(goal, "⇔")
    if len(parts) == 2:
        L, R = (x[1:-1].strip() if x.startswith("(") and x.endswith(")") else x for x in parts)
        out = []
        for a, b in ((L, R), (R, L)):
            # посылка-дизъюнкция «A ∨ B ⇒ R» — карточки «A ⇒ R», «B ⇒ R»
            for x in _split_top(a, "∨"):
                x = x[1:-1].strip() if x.startswith("(") and x.endswith(")") else x
                out += variants({**card, "условие": _add_prem(cond, x), "цель": b})
        return out
    parts = _split_top(goal, "∧")
    if len(parts) < 2:
        parts = _split_top(goal, ",")
    if len(parts) >= 2 and not goal.strip().startswith("∃"):
        out = []
        for x in parts:
            x = x[1:-1].strip() if x.startswith("(") and x.endswith(")") else x
            out += variants({**card, "цель": x})
        return out
    parts = _split_top(goal, "∨")
    if len(parts) >= 2:
        c = cond
        for x in parts[:-1]:
            c = _add_prem(c, _neg(x))
        return [{**card, "условие": c, "цель": parts[-1]}]
    return [card]


def check(vocab, sch, card, k):
    if card.get("тождество"):
        return "покрыта", "тождества"  # algen.identities: относительно свободные группы
    if not card.get("условие") or not card.get("цель"):
        return "не записана машинно", None
    try:
        g, prem, goal = scheme(vocab, {"раздел": "grp", "условие": card["условие"], "цель": card["цель"]})
    except Unsupported as e:
        return f"не записывается: {e}", None
    lits = prem + [goal]
    if any(a[0] == "r" and a[1] not in ("le", "eq-sub", "iso", "embeds", "conj-sub", "permutes", "commute", "conjugate", "eq-elt",
                                                     "num-eq", "num-le", "num-divides", "num-coprime") for a, _ in lits):
        return "нужны отношения сверх ⩽, =, ≅", None
    ks = [int(x) for x in str(k).split(",")]
    tops = {x for a, _ in lits for x in a[2:] if isinstance(x, App)}
    tops -= {y for x in tops for y in _sub(x) if y != x}
    kk = ks[min(len(tops), len(ks) - 1)]
    if len(lits) > kk + 1:
        return f"литералов {len(lits)} > {kk + 1}", None
    vs = [(t.name, g.terms[t].sort, {kk: str(v) for kk, v in g.terms[t].links.items()})
          for t in g.terms if isinstance(t, Var)]
    used = set()
    for a, _ in lits:
        for x in a[2:]:
            if isinstance(x, App):
                used |= {y for y in _sub(x) if isinstance(y, App)}
    sid = sch.find(vs, used)
    pts = [v for v in vs if v[1] == "Grp.pt" and not v[0].startswith("x_")]
    if sid is None and len(pts) == 1:
        # одна точка G-множества — скрытая точка x_A базы GX
        p, A = pts[0][0], pts[0][2].get("ambient", "A")
        ren = {p: f"x_{A}"}
        sid = sch.find([v for v in vs if v is not pts[0]],
                       {_Named(_rename(t, ren)) for t in used})
    if sid is None:
        return "нет базы с такими переменными и термами во вселенной", None
    return "покрыта", sid


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("schemes", nargs="?", help="не нужен: схемы — из таблиц баз (algen.table)")
    ap.add_argument("--посылок", dest="k", default="2",
                    help="k или «k0,k1,k2» — посылок для задач с 0, 1, ⩾ 2 верхними термами")
    ap.add_argument("--карточки", dest="root", default=str(DATA / "archive" / "grp"))
    ap.add_argument("--подробно", dest="verbose", action="store_true")
    ap.add_argument("--вердикты", dest="verdicts", default=None,
                    help="вывод проверки архива (algen.archive): карточки, закрытые вычислением, "
                         "библиотекой, проверкой на примерах, — отдельной строкой")
    a = ap.parse_args()
    closed = {}
    if a.verdicts:
        import re
        for line in Path(a.verdicts).read_text(encoding="utf-8").splitlines():
            m = re.match(r"^(\S+-[\w.′()]+)\s+(.+?)\s{2,}(.+?)\s{2,}(.*)$", line.rstrip())
            if m:
                st = m.group(3).strip() or m.group(4).split(";")[0].strip()
                closed[m.group(1)] = st
    vocab = Vocab.section("grp")
    sch = Schemes(vocab, a.schemes)
    tally, by_file, misses = Counter(), defaultdict(Counter), []
    for f, c in cards(a.root):
        vs_ = variants(c)
        rs = [check(vocab, sch, x, a.k) for x in vs_]
        bad_ = [r for r in rs if r[0] != "покрыта"]
        why, sid = bad_[0] if bad_ else rs[0]
        if why != "покрыта" and c["id"] in closed and closed[c["id"]] != "КРАСНЫЙ ФЛАГ":
            why = f"вне схем, но {closed[c['id']]}"
        key = why.split(":")[0]
        tally[key] += 1
        by_file[f][key] += 1
        if why != "покрыта":
            misses.append((f, c["id"], why, c.get("условие", ""), c.get("цель", "")))
    total = sum(tally.values())
    print(f"карточек {total}: " + ", ".join(f"{k} {v}" for k, v in tally.most_common()))
    for f, t in sorted(by_file.items()):
        print(f"  {f}: " + ", ".join(f"{k} {v}" for k, v in t.most_common()))
    if a.verbose:
        for m in misses:
            print(" | ".join(m))


if __name__ == "__main__":
    main()
