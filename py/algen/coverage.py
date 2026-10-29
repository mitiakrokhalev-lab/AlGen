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


def check(vocab, sch, card, k):
    if not card.get("условие") or not card.get("цель"):
        return "не записана машинно", None
    try:
        g, prem, goal = scheme(vocab, {"раздел": "grp", "условие": card["условие"], "цель": card["цель"]})
    except Unsupported as e:
        return f"не записывается: {e}", None
    lits = prem + [goal]
    if any(a[0] == "r" and a[1] not in ("le", "eq-sub", "iso") for a, _ in lits):
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
    a = ap.parse_args()
    vocab = Vocab.section("grp")
    sch = Schemes(vocab, a.schemes)
    tally, by_file, misses = Counter(), defaultdict(Counter), []
    for f, c in cards(a.root):
        why, sid = check(vocab, sch, c, a.k)
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
