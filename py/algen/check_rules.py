"""Проверка правил базы на конечных группах, посчитанных GAP.

Правило базы — утверждение «для всякой привязки ролей сцены: посылки ⇒
вывод». Здесь каждое правило раздела групп подставляется во ВСЕ привязки, какие
даёт таблица data/finite/grp-small.jsonl: роль-группа пробегает все группы,
роль-подгруппа — представителей всех классов сопряжённых подгрупп. Привязка, на
которой посылки верны, а вывод ложен, — контрпример к правилу, то есть ошибка
в базе.

Проверка односторонняя: отсутствие контрпримера среди конечных групп не
доказывает правило. Но всякое найденное нарушение — настоящее, потому что
каждое значение здесь посчитано GAP, а не записано рукой.

    node tools/dump-rules.mjs grp > /tmp/grp-rules.json
    python3 -m algen.check_rules /tmp/grp-rules.json
"""

import argparse
import itertools
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

from .finite import OUT, PRODUCTS, load, load_products

UNDEF = object()  # терм не определён (фактор по ненормальной подгруппе)


class Skip(Exception):
    """Атом или терм не вычисляется по таблице."""


class Grp:
    __slots__ = ("key",)

    def __init__(self, key):
        self.key = key


class Sub:
    """Подгруппа: объемлющая группа, номер класса и точность.

    exact = False значит, что известен только класс сопряжённости, а не сама
    подгруппа (нормализатор ненормальной подгруппы и т. п.). Свойства от этого не
    зависят, а включения и равенства — зависят, и такие атомы не считаются.
    """

    __slots__ = ("amb", "idx", "exact")

    def __init__(self, amb, idx, exact):
        self.amb, self.idx, self.exact = amb, idx, exact


class Num:
    __slots__ = ("n",)

    def __init__(self, n):
        self.n = n


SUPPORTED = {
    "quotient", "center", "commutator", "torsion", "trivial-sub", "whole-sub",
    "normalizer", "centralizer", "normal-closure", "ab", "index", "ord", "prod",
}


class Table:
    def __init__(self, groups, products=None):
        self.g = groups
        self.products = products or {}

    def rec(self, key):
        return self.g[key]

    def sub(self, amb, idx):
        return self.g[amb]["subs"][idx]

    def canon(self, amb, idx):
        normal = self.sub(amb, idx)["class_size"] == 1
        return Sub(amb, idx, normal)

    def find(self, amb, pred):
        for i, s in enumerate(self.g[amb]["subs"]):
            if pred(s):
                return i
        raise KeyError(amb)

    # --- термы ---------------------------------------------------------------

    def term(self, t, env):
        if isinstance(t, str):
            if t not in env:
                raise Skip(f"роль {t}")
            return env[t]
        op, args = t["op"], [self.term(a, env) for a in t.get("args", [])]
        if any(a is UNDEF for a in args):
            return UNDEF
        if op not in SUPPORTED:
            raise Skip(op)
        X = args[0]
        if not isinstance(X, Grp):
            raise Skip(f"{op} от не-группы")
        r = self.rec(X.key)
        if r["subs"] is None and op not in ("ord", "prod"):
            raise Skip("подгруппы группы не посчитаны")
        if op == "center":
            return self.canon(X.key, r["center"])
        if op == "commutator":
            return self.canon(X.key, r["commutator"])
        if op in ("torsion", "whole-sub"):
            return self.canon(X.key, self.find(X.key, lambda s: s["index"] == 1))
        if op == "trivial-sub":
            return self.canon(X.key, self.find(X.key, lambda s: s["group"] == "1:1"))
        if op == "ab":
            return Grp(self.sub(X.key, r["commutator"])["quotient"])
        if op == "ord":
            return Num(r["order"])
        if op == "prod":
            Y = args[1]
            if not isinstance(Y, Grp):
                raise Skip("prod от не-группы")
            key = self.products.get((X.key, Y.key))
            if key is None:
                raise Skip("произведение вне таблицы")
            return Grp(key)
        N = args[1]
        if not isinstance(N, Sub) or N.amb != X.key:
            raise Skip(f"{op}: подгруппа не той группы")
        s = self.sub(X.key, N.idx)
        if op == "quotient":
            return Grp(s["quotient"]) if s["props"]["normal"] else UNDEF
        if op == "index":
            return Num(s["index"])
        if op in ("normalizer", "centralizer", "normal-closure"):
            if not N.exact:
                raise Skip(f"{op} от подгруппы, известной до сопряжения")
            field = {"normal-closure": "normal_closure"}.get(op, op)
            return self.canon(X.key, s[field])
        raise Skip(op)

    # --- атомы ---------------------------------------------------------------

    def atom(self, a, env):
        """True / False, UNDEF — терм не определён, Skip — не вычисляется."""
        if "rel" in a:
            return self.rel(a["rel"], [self.term(x, env) for x in a["args"]])
        v = self.term(a["t"], env)
        if v is UNDEF:
            return UNDEF
        val = self.prop(a["p"], v)
        return val if a.get("значение", True) else not val

    def prop(self, p, v):
        if isinstance(v, Num):
            n = v.n
            table = {"num-finite": True, "num-one": n == 1, "num-two": n == 2,
                     "num-even": n % 2 == 0,
                     "num-prime": n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))}
            if p in table:
                return table[p]
            raise Skip(p)
        if isinstance(v, Sub):
            s = self.sub(v.amb, v.idx)
            if p in s["props"]:
                return s["props"][p]
            v = Grp(s["group"])
        props = self.rec(v.key)["props"]
        if p not in props:
            raise Skip(p)
        return props[p]

    def rel(self, r, args):
        if any(a is UNDEF for a in args):
            return UNDEF
        A, B = args
        if r == "iso":
            ka = self.sub(A.amb, A.idx)["group"] if isinstance(A, Sub) else A.key
            kb = self.sub(B.amb, B.idx)["group"] if isinstance(B, Sub) else B.key
            return ka == kb
        if r in ("le", "eq-sub"):
            if not (isinstance(A, Sub) and isinstance(B, Sub)) or A.amb != B.amb:
                raise Skip(r)
            if not (A.exact and B.exact):
                raise Skip(f"{r} между подгруппами, известными до сопряжения")
            if r == "eq-sub":
                return A.idx == B.idx
            return B.idx in self.sub(A.amb, A.idx)["le"]
        if r in ("num-eq", "num-divides", "num-coprime"):
            a, b = A.n, B.n
            from math import gcd
            return {"num-eq": a == b, "num-divides": a != 0 and b % a == 0,
                    "num-coprime": gcd(a, b) == 1}[r]
        raise Skip(r)

    # --- привязки ------------------------------------------------------------

    def bindings(self, scene, pair_limit, subpair_limit=40):
        """Все привязки ролей сцены к группам и представителям подгрупп."""
        objs = [r for r in scene if r["sort"] == "Grp.obj"]
        subs = [r for r in scene if r["sort"] == "Grp.sub"]
        other = [r for r in scene if r["sort"] not in ("Grp.obj", "Grp.sub")]
        if other:
            raise Skip(f"сорт {other[0]['sort']}")
        if any(s.get("ambient") not in {o["name"] for o in objs} for s in subs):
            raise Skip("объемлющая не роль сцены")
        keys = list(self.g)
        if len(objs) > 1:
            keys = [k for k in keys if self.g[k]["order"] <= pair_limit]
        if len(subs) > 1:
            # Пары подгрупп растут как квадрат числа классов (у групп порядка 64
            # их сотни), поэтому пары берутся только у групп с небольшим
            # числом классов. Это сужает проверку, но не делает её неверной.
            keys = [k for k in keys if len(self.g[k]["subs"] or []) <= subpair_limit]
        for gs in itertools.product(keys, repeat=len(objs)):
            env = {o["name"]: Grp(k) for o, k in zip(objs, gs)}
            ranges = [range(len(self.g[env[s["ambient"]].key]["subs"] or [])) for s in subs]
            for idxs in itertools.product(*ranges):
                e = dict(env)
                for s, i in zip(subs, idxs):
                    e[s["name"]] = Sub(env[s["ambient"]].key, i, True)
                yield e


def describe(table, env):
    parts = []
    for name, v in env.items():
        if isinstance(v, Grp):
            r = table.rec(v.key)
            parts.append(f"{name} = {r['name']} [SmallGroup({v.key.replace(':', ',')})]")
        elif isinstance(v, Sub):
            s = table.sub(v.amb, v.idx)
            parts.append(f"{name} ≅ {table.rec(s['group'])['name']} индекса {s['index']}")
    return ", ".join(parts)


def gives_rules(gives):
    """«gives» конструкции — правило без посылок про её выход."""
    out = []
    for c in gives:
        scene = [{"name": s["role"], "sort": s["sort"], **({"ambient": s["ambient"]} if "ambient" in s else {})}
                 for s in c["in"]]
        t = {"op": c["op"], "args": [s["role"] for s in c["in"]]}
        for p, v in c["gives"].items():
            out.append({"id": f"{c['op']}:даёт:{p}", "scene": scene, "if": [],
                        "then": {"p": p, "t": t, "значение": v}})
    return out


def check(rule, table, pair_limit, subpair_limit=40):
    res = Counter()
    first = None
    for env in table.bindings(rule["scene"], pair_limit, subpair_limit):
        try:
            prem = [table.atom(a, env) for a in rule["if"]]
            if any(p is UNDEF for p in prem):
                res["посылка не определена"] += 1
                continue
            if not all(prem):
                res["посылки ложны"] += 1
                continue
            outs = rule["then"]["или"] if "или" in rule["then"] else [rule["then"]]
            vals = [table.atom(a, env) for a in outs]
            concl = UNDEF if all(v is UNDEF for v in vals) else any(v is True for v in vals)
        except Skip as e:
            res[f"не считается: {e}"] += 1
            continue
        if concl is UNDEF:
            # Терм вывода не существует (фактор по ненормальной подгруппе):
            # правило на такой привязке не говорит ничего, как и в выводе.
            res["вывод не определён"] += 1
        elif concl:
            res["верно"] += 1
        else:
            res["НАРУШЕНО"] += 1
            if first is None or first[0] != "НАРУШЕНО":
                first = ("НАРУШЕНО", env)
    return res, first


# Таблица одна на все правила; дочерние процессы получают её при fork.
_TABLE = None
_ARGS = None


def _one(r):
    try:
        res, first = check(r, _TABLE, *_ARGS)
    except Skip as e:
        return {"id": r["id"], "итог": "не проверяется", "почему": str(e)}
    if res["НАРУШЕНО"]:
        verdict = "НАРУШЕНО"
    elif res["верно"]:
        verdict = "подтверждено"
    elif any(k.startswith("не считается") for k in res):
        verdict = "не проверяется"
    else:
        verdict = "не применилось"
    item = {"id": r["id"], "итог": verdict, "счёт": dict(res)}
    if first:
        item["пример"] = f"{first[0]}: {describe(_TABLE, first[1])}"
    if verdict == "не проверяется":
        item["почему"] = next(k for k in res if k.startswith("не считается"))[len("не считается: "):]
    return item


def main():
    global _TABLE, _ARGS
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("rules")
    ap.add_argument("--таблица", dest="table", default=str(OUT))
    ap.add_argument("--произведения", dest="products", default=str(PRODUCTS))
    ap.add_argument("--пары-до", dest="pair_limit", type=int, default=32,
                    help="для сцен с двумя группами брать группы порядка не выше")
    ap.add_argument("--классов-для-пар", dest="subpair_limit", type=int, default=40,
                    help="для сцен с двумя подгруппами брать группы с не большим числом классов")
    ap.add_argument("--нитей", dest="jobs", type=int, default=os.cpu_count())
    ap.add_argument("--поправки", dest="patch", default=str(OUT.parents[1] / "new" / "grp.json"),
                    help="data/new/<раздел>.json: снятые и добавленные правила; пусто — без поправок")
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    d = json.load(open(a.rules))
    _TABLE = Table(load(a.table), load_products(a.products))
    _ARGS = (a.pair_limit, a.subpair_limit)
    rules = d["rules"] + gives_rules(d.get("gives", []))
    if a.patch:
        from .logic import Vocab
        patch = json.load(open(a.patch, encoding="utf-8"))
        v = Vocab({**d, "gives": []})
        v.apply(patch)
        drop = {x["id"] for x in patch.get("снять", [])}
        new = {x["id"] for x in patch.get("добавить", [])}
        rules = [r for r in rules if r["id"] not in drop] + [r for r in v.rules if r["id"] in new]
    # сцена записи базы может быть словарём {"N": {"sort": …, "ambient": "X"}}
    rules = [{**r, "scene": [{"name": k, "sort": v} if isinstance(v, str) else {"name": k, **v}
                             for k, v in r["scene"].items()]} if isinstance(r["scene"], dict) else r
             for r in rules]
    with Pool(a.jobs) as pool:
        report = pool.map(_one, rules, chunksize=1)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    tally = Counter(x["итог"] for x in report)
    print(f"правил {len(report)}: " + ", ".join(f"{k} {v}" for k, v in tally.most_common()))
    for x in report:
        if x["итог"] == "НАРУШЕНО":
            print(f"\n[НАРУШЕНО] {x['id']}\n    {x['пример']}\n    {x['счёт']}")


if __name__ == "__main__":
    main()
