"""Сверка рукописной библиотеки пространств старого генератора с π-Base.

Старые пространства (data/top-infinite.json) записывались рукой. Те из них,
что есть в π-Base, сверяются здесь по каждому свойству. Расхождение значит,
что ошибся либо старый файл, либо перевод свойства (у старого словаря
свойства определены менее точно, чем у π-Base), и разбирать его надо руками.

    python3 -m algen.audit_top
"""

import json

from .finite import ROOT
from .pibase import load, value

# старое пространство → пространство π-Base
SPACES = {
    "R": "S000025", "Q": "S000027", "I": "S000158", "Sphere1": "S000170",
    "C": "S000026", "N": "S000002", "S": "S000043", "S2": "S000076",
    "Ndiscr": "S000003", "RCF": "S000016", "W1": "S000035", "Ind": "S000194",
    "W1plus": "S000036", "Sine": "S000114", "Plank": "S000079",
    "CoCount": "S000017", "Long": "S000149",
}

# старое свойство → формула над свойствами π-Base: [(uid, значение), ...]
# означает конъюнкцию. Старые T3 и T4 включают T₁ — это и есть T₃, T₄ π-Base.
# «Одноточечно» = непусто и не больше одной точки.
PROPS = {
    "finite": [("P000078", True)], "countable": [("P000057", True)],
    "T0": [("P000001", True)], "T1": [("P000002", True)], "T2": [("P000003", True)],
    "T3": [("P000005", True)], "T4": [("P000007", True)],
    "connected": [("P000036", True)], "path-connected": [("P000037", True)],
    "totally-disconnected": [("P000047", True)], "compact": [("P000016", True)],
    "locally-compact": [("P000130", True)], "discrete": [("P000052", True)],
    "indiscrete": [("P000129", True)], "metrizable": [("P000053", True)],
    "first-countable": [("P000028", True)], "second-countable": [("P000027", True)],
    "separable": [("P000026", True)],
    "point": [("P000125", False), ("P000137", False)],
}


def formula(db, space, lits):
    vals = [value(db, space, p) for p, _ in lits]
    if any(v is not None and v != want for v, (_, want) in zip(vals, lits)):
        return False
    if all(v is not None for v in vals):
        return True
    return None


def audit():
    db = load()
    old = {o["id"]: o for o in json.load(open(ROOT / "data" / "top-infinite.json"))["объекты"]}
    rows = []
    for oid, sid in SPACES.items():
        o = old[oid]
        for p, v in o["props"].items():
            if p not in PROPS:
                continue
            pb = formula(db, sid, PROPS[p])
            if pb is None:
                status = "π-Base не знает"
            elif pb == v:
                status = "совпало"
            else:
                status = "РАСХОЖДЕНИЕ"
            rows.append({"old": oid, "name": o["имя"], "pibase": sid,
                         "pibase_name": db["spaces"][sid]["name"], "prop": p,
                         "old_value": v, "pibase_value": pb, "status": status})
    return rows


if __name__ == "__main__":
    from collections import Counter
    rows = audit()
    print(Counter(r["status"] for r in rows))
    for r in rows:
        if r["status"] != "совпало":
            print(f"{r['status']}: {r['name']} ({r['pibase_name']}), {r['prop']}: "
                  f"старое {r['old_value']}, π-Base {r['pibase_value']}")
