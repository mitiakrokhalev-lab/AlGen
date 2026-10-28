"""Библиотека групп: конечные из GAP и бесконечные из data/infinite/grp.json.

Конечные группы вычислены (algen.finite), их значения — истина. Бесконечные
записаны рукой, и каждое их значение проверяется выводом: на сцену «G, N ⩽ G,
G/N» ставятся все записанные значения группы, подгруппы и фактора, и
SAT-решатель ищет противоречие с базой правил. Противоречие — ошибка либо в
записи, либо в правиле, и ядро решателя показывает, какие значения вместе
невозможны. Значения, которых в записи нет, но которые следуют из записанных,
решатель выводит, и библиотека отдаёт их как выведенные.

Эта же сцена служит поиском контрпримеров: подставляем каждую пару (G, N)
из библиотеки и смотрим, верны ли посылки и ложна ли цель.

    cd py && python3 -m algen.library              # сверка бесконечных групп
    python3 -m algen.library --конечные 200        # сверка движка на конечных
"""

import argparse
import json
import random
import sys
from multiprocessing import Pool

from .finite import load as load_finite
from .logic import DATA, Graph, Theory, Vocab

INFINITE = DATA / "infinite" / "grp.json"
SUB_PROPS = ("normal", "characteristic", "maximal", "whole", "central", "finite-index")


class Library:
    def __init__(self, infinite=INFINITE):
        self.obj = {}
        for k, r in load_finite(extra=True).items():
            self.obj[k] = {"key": k, "имя": r["name"], "конечная": True, "свойства": r["props"],
                           "подгруппы": None if r["subs"] is None else [
                               {"id": str(i), "≅": s["group"], "свойства": s["props"],
                                **({"фактор": s["quotient"]} if "quotient" in s else {})}
                               for i, s in enumerate(r["subs"])],
                           "центр": None if r.get("center") is None else str(r["center"]),
                           "коммутант": None if r.get("commutator") is None else str(r["commutator"])}
        with open(infinite, encoding="utf-8") as f:
            for r in json.load(f)["группы"]:
                self.obj[r["id"]] = {"key": r["id"], "конечная": False, **r}
        for o in self.obj.values():
            for s in o["подгруппы"] or []:
                for k in (s["≅"], s.get("фактор")):
                    if k is not None and k not in self.obj:
                        raise KeyError(f"{o['key']}/{s['id']}: нет группы {k}")

    def infinite(self):
        return [k for k, o in self.obj.items() if not o["конечная"]]


# --- сцена G, N, G/N -----------------------------------------------------------


class Scene:
    """Граф «G, N ⩽ G, G/N» и его теория; собирается один раз на процесс."""

    def __init__(self, vocab):
        g = Graph(vocab)
        self.G = g.var("G", "Grp.obj")
        self.N = g.var("N", "Grp.sub", ambient=self.G)
        self.Q = g.given(g.make("quotient", [self.G, self.N]))
        self.Z = g.make("center", [self.G])
        self.C = g.make("commutator", [self.G])
        self.v = vocab
        self.T = Theory(g, grow=1)
        self.s = self.T.solver()

    def facts(self, lib, key, sub):
        """Записанные значения пары (G, N): {атом: (значение, откуда)}."""
        o, out = lib.obj[key], {}

        def put(prop, t, props, where):
            if prop in props:
                out[("p", prop, t)] = (props[prop], where)

        for p in GROUP_PROPS:
            put(p, self.G, o["свойства"], key)
        if sub is None:
            return out
        s = o["подгруппы"][sub]
        n = lib.obj[s["≅"]]
        for p in SUB_PROPS:
            put(p, self.N, s["свойства"], f"{key}/{s['id']}")
        for p in GROUP_PROPS:
            put(p, self.N, n["свойства"], f"{key}/{s['id']} ≅ {s['≅']}")
        if s.get("фактор"):
            q = lib.obj[s["фактор"]]
            for p in GROUP_PROPS:
                put(p, self.Q, q["свойства"], f"{key}/{s['id']}: фактор ≅ {s['фактор']}")
        for name, t in (("центр", self.Z), ("коммутант", self.C)):
            if o.get(name) is not None:
                out[("r", "eq-sub", *sorted((self.N, t), key=str))] = (
                    o[name] == s["id"], f"{key}: {name} — {o[name]}")
        return out

    def check(self, facts):
        """None, если записи совместны с базой, иначе ядро противоречия."""
        lits = {}
        for a, (v, where) in facts.items():
            l = self.T.lit(a, v)
            if l is False:
                return [(a, v, where)]
            if l is not None:
                lits[l] = (a, v, where)
        if self.s.solve(assumptions=list(lits)):
            return None
        return [lits[l] for l in self.s.get_core() or [] if l in lits]

    def derive(self, facts, atoms):
        """Значения атомов, которые следуют из записей: {атом: значение}."""
        assume = [l for a, (v, _) in facts.items()
                  if (l := self.T.lit(a, v)) not in (None, False)]
        out = {}
        for a in atoms:
            if a in facts:
                continue
            l = self.T.lit(a)
            if not self.s.solve(assumptions=assume + [-l]):
                out[a] = True
            elif not self.s.solve(assumptions=assume + [l]):
                out[a] = False
        return out

    def values(self, lib, key, sub, need=None):
        """Значения атомов пары (G, N): записанные и выведенные из них.
        need — какие атомы нужны; выводятся только недостающие из них."""
        facts = self.facts(lib, key, sub)
        vals = {a: v for a, (v, _) in facts.items()}
        missing = [a for a in (need or self.atoms()) if a not in vals]
        if missing:
            vals.update(self.derive(facts, missing))
        return vals

    def witnesses(self, lib, premises, goal, limit=3):
        """Пары (G, N) библиотеки, где посылки верны, а цель ложна.

        premises, goal — (атом, значение) над термами сцены G, N, G/N."""
        need = [a for a, _ in premises] + [goal[0]]
        out = []
        for key, sub in jobs(lib, lib.obj):
            o = lib.obj[key]
            if sub is None:
                continue
            facts = self.facts(lib, key, sub)
            quick = {a: v for a, (v, _) in facts.items()}
            if any(quick.get(a, v) != v for a, v in premises) or quick.get(goal[0]) == goal[1]:
                continue  # уже по записям не подходит
            vals = self.values(lib, key, sub, need)
            if all(vals.get(a) == v for a, v in premises) and vals.get(goal[0]) == (not goal[1]):
                s = o["подгруппы"][sub]
                out.append({"G": key, "имя G": o.get("имя"), "N": s["id"],
                            "имя N": s.get("имя", lib.obj[s["≅"]].get("имя"))})
                if len(out) >= limit:
                    break
        return out

    def atoms(self):
        return ([("p", p, t) for t in (self.G, self.N, self.Q) for p in GROUP_PROPS]
                + [("p", p, self.N) for p in SUB_PROPS])


GROUP_PROPS = ("trivial", "abelian", "cyclic", "finite", "fin-gen", "free", "simple", "solvable",
               "nilpotent", "perfect", "torsion-free", "periodic", "divisible", "centerless",
               "residually-finite", "indecomposable")

_LIB = _SCENE = None


def _init():
    global _LIB, _SCENE
    _LIB = Library()
    _SCENE = Scene(Vocab.section("grp"))


def _audit(job):
    key, sub = job
    facts = _SCENE.facts(_LIB, key, sub)
    core = _SCENE.check(facts)
    if core is not None:
        return {"группа": key, "подгруппа": sub, "противоречие": [
            (f"{'' if v else '¬'}{a[1]}({', '.join(map(str, a[2:]))})", where) for a, v, where in core]}
    atoms = [a for a in _SCENE.atoms() if sub is not None or a[2] == _SCENE.G]
    derived = _SCENE.derive(facts, atoms)
    return {"группа": key, "подгруппа": sub, "выведено": {
        f"{a[1]}({', '.join(map(str, a[2:]))})": v for a, v in derived.items()}}


def jobs(lib, keys):
    for k in keys:
        yield k, None
        for i in range(len(lib.obj[k]["подгруппы"] or [])):
            yield k, i


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--конечные", dest="finite", type=int, default=0,
                    help="вместо бесконечных сверить столько случайных пар (G, N) из конечных")
    ap.add_argument("--нитей", dest="jobs", type=int, default=None)
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    lib = Library()
    if a.finite:
        pairs = [j for j in jobs(lib, [k for k, o in lib.obj.items() if o["конечная"]])]
        work = random.Random(0).sample(pairs, a.finite)
    else:
        work = list(jobs(lib, lib.infinite()))
    with Pool(a.jobs, initializer=_init) as pool:
        report = pool.map(_audit, work, chunksize=1)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    bad = [r for r in report if "противоречие" in r]
    print(f"сцен {len(report)}, противоречий {len(bad)}, выведено значений "
          f"{sum(len(r.get('выведено', {})) for r in report)}")
    for r in bad:
        sub = "" if r["подгруппа"] is None else f", N = {lib.obj[r['группа']]['подгруппы'][r['подгруппа']]['id']}"
        print(f"\n{r['группа']}{sub}:")
        for lit, where in r["противоречие"]:
            print(f"    {lit:40} ← {where}")


if __name__ == "__main__":
    main()
