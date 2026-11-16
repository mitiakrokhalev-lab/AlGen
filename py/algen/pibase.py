"""Импорт π-Base: пространства, свойства и теоремы общей топологии.

π-Base (https://topology.pi-base.org, данные на github.com/pi-base/data,
лицензия CC BY 4.0) — курируемая база: у каждого свойства есть определение, у
каждого значения свойства пространства и у каждой теоремы — доказательство или
ссылка. Это ровно то, чего не хватало старой библиотеке, где свойства
записывались рукой.

Берётся ВСЁ: 225 пространств, 247 свойств, 935 теорем на момент импорта.
Значения, не записанные в π-Base явно, выводятся здесь же по теоремам (с
контрапозицией), и у каждого выведенного значения сохраняется цепочка: какая
теорема и из каких значений. Противоречие при выводе означает ошибку импорта
или базы, и импорт тогда падает.

    git clone --depth 1 https://github.com/pi-base/data /tmp/pibase
    python3 -m algen.pibase /tmp/pibase

пишет data/pibase/pibase.json.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "data" / "pibase" / "pibase.json"


def front_matter(path):
    text = path.read_text(encoding="utf-8")
    m = re.match(r"^---\n(.*?)\n---\n?(.*)$", text, re.S)
    if not m:
        raise ValueError(f"нет заголовка YAML: {path}")
    return yaml.safe_load(m.group(1)), m.group(2).strip()


def literals(cond):
    """Условие теоремы π-Base → список (свойство, значение)."""
    if "and" in cond:
        return [lit for c in cond["and"] for lit in literals(c)]
    if "or" in cond:
        raise ValueError("дизъюнкция в теореме не поддержана")
    ((p, v),) = cond.items()
    return [(p, bool(v))]


def read(src):
    src = Path(src)
    props = {}
    for f in sorted((src / "properties").glob("*.md")):
        h, body = front_matter(f)
        props[h["uid"]] = {"name": h["name"], "aliases": h.get("aliases", []),
                           "refs": h.get("refs", []), "definition": body}
    theorems = {}
    for f in sorted((src / "theorems").glob("*.md")):
        h, body = front_matter(f)
        theorems[h["uid"]] = {"if": literals(h["if"]), "then": literals(h["then"]),
                              "refs": h.get("refs", []), "proof": body}
    spaces = {}
    for d in sorted((src / "spaces").iterdir()):
        h, body = front_matter(d / "README.md")
        traits = {}
        for f in sorted((d / "properties").glob("*.md")):
            th, tbody = front_matter(f)
            traits[th["property"]] = {"value": bool(th["value"]), "refs": th.get("refs", []),
                                      "proof": tbody}
        spaces[h["uid"]] = {"name": h["name"], "aliases": h.get("aliases", []),
                            "refs": h.get("refs", []), "description": body, "asserted": traits}
    return props, theorems, spaces


def derive(asserted, theorems):
    """Замыкание значений по теоремам и их контрапозициям.

    Теорема: p₁ ∧ … ∧ pₖ ⇒ q. Прямо: все pᵢ известны и верны — ставим q.
    Контрапозиция: q известно ложным и все pᵢ, кроме одного, верны — ставим
    отрицание оставшегося. Для хорновских теорем это полный вывод значений.
    Возвращает {свойство: (значение, теорема, [использованные свойства])}.
    """
    known = {p: (t["value"], None, []) for p, t in asserted.items()}

    def put(p, v, th, used):
        if p in known:
            if known[p][0] != v:
                raise ValueError(f"противоречие по {p}: теорема {th}, ранее {known[p][1] or 'задано'}")
            return False
        known[p] = (v, th, used)
        return True

    changed = True
    while changed:
        changed = False
        for uid, t in theorems.items():
            prem, (concl,) = t["if"], t["then"]
            state = [known.get(p, (None,))[0] for p, _ in prem]
            ok = [s == v for s, (_, v) in zip(state, prem)]
            if all(ok):
                changed |= put(concl[0], concl[1], uid, [p for p, _ in prem])
                continue
            c = known.get(concl[0])
            if c is not None and c[0] != concl[1]:
                missing = [i for i, o in enumerate(ok) if not o]
                if len(missing) == 1 and state[missing[0]] is None:
                    p, v = prem[missing[0]]
                    others = [q for j, (q, _) in enumerate(prem) if j != missing[0]]
                    changed |= put(p, not v, uid, others + [concl[0]])
    return known


def build(src):
    props, theorems, spaces = read(src)
    for t in theorems.values():
        if len(t["then"]) != 1:
            raise ValueError("теорема с несколькими выводами")
    stats = {"asserted": 0, "derived": 0}
    for uid, s in spaces.items():
        known = derive(s["asserted"], theorems)
        s["traits"] = {p: {"value": v, "by": th, "from": used}
                       for p, (v, th, used) in sorted(known.items()) if th is not None}
        stats["asserted"] += len(s["asserted"])
        stats["derived"] += len(s["traits"])
    try:
        commit = subprocess.run(["git", "-C", str(src), "rev-parse", "HEAD"],
                                capture_output=True, text=True, check=True).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        commit = None
    return {
        "source": "https://github.com/pi-base/data",
        "license": "CC BY 4.0, π-Base contributors",
        "commit": commit,
        "properties": props,
        "theorems": {k: {**v, "if": [list(x) for x in v["if"]], "then": [list(x) for x in v["then"]]}
                     for k, v in theorems.items()},
        "spaces": spaces,
    }, stats


def load(path=OUT):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def value(db, space, prop):
    """True / False / None (π-Base не знает)."""
    s = db["spaces"][space]
    if prop in s["asserted"]:
        return s["asserted"][prop]["value"]
    if prop in s["traits"]:
        return s["traits"][prop]["value"]
    return None


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("src", help="клон github.com/pi-base/data")
    a = ap.parse_args()
    db, stats = build(a.src)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(db, ensure_ascii=False, indent=0), encoding="utf-8")
    n = len(db["spaces"]) * len(db["properties"])
    known = stats["asserted"] + stats["derived"]
    print(f"{OUT}: пространств {len(db['spaces'])}, свойств {len(db['properties'])}, "
          f"теорем {len(db['theorems'])}; значений задано {stats['asserted']}, "
          f"выведено {stats['derived']}, известно {known} из {n} ({known / n:.0%})", file=sys.stderr)
