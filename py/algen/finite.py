"""Таблица конечных групп из библиотеки SmallGroups (GAP).

Каждая запись посчитана GAP, а не написана рукой: свойства группы, все классы
сопряжённых подгрупп со свойствами вложения, факторы по нормальным
подгруппам и канонические подгруппы (центр, коммутант, Фраттини, нормализатор,
централизатор, ядро, нормальное замыкание) как номера классов.

    python3 -m algen.finite --до 100

пишет data/finite/grp-small.jsonl и таблицу прямых произведений
data/finite/grp-small-products.jsonl. Отдельные группы большего порядка,
нужные как примеры, досчитываются в data/finite/grp-extra.jsonl:

    python3 -m algen.finite --добавить 120:5 720:771
 Порядки считаются параллельно кусками,
затем склеиваются по возрастанию порядка.
"""

import argparse
import json
import math
import os
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = Path(__file__).with_name("gap") / "groups.g"
PRODUCTS_SCRIPT = Path(__file__).with_name("gap") / "products.g"
OUT = ROOT / "data" / "finite" / "grp-small.jsonl"
PRODUCTS = ROOT / "data" / "finite" / "grp-small-products.jsonl"
EXTRA = ROOT / "data" / "finite" / "grp-extra.jsonl"
AUT_SCRIPT = Path(__file__).with_name("gap") / "aut.g"
AUT = ROOT / "data" / "finite" / "grp-aut.jsonl"
COMPL_SCRIPT = Path(__file__).with_name("gap") / "compl.g"
COMPL = ROOT / "data" / "finite" / "grp-compl.jsonl"
ENDO_SCRIPT = Path(__file__).with_name("gap") / "endo.g"
ENDO = ROOT / "data" / "finite" / "grp-endo.jsonl"
ELTS_SCRIPT = Path(__file__).with_name("gap") / "elts.g"
ELTS = ROOT / "data" / "finite" / "grp-elts.jsonl"
PRESENT_SCRIPT = Path(__file__).with_name("gap") / "present.g"
PRESENT = ROOT / "data" / "finite" / "grp-present.jsonl"


def _run(lo, hi, path):
    prog = f'LO:={lo};; HI:={hi};; OUT:="{path}";; Read("{SCRIPT}");\n'
    subprocess.run(["gap", "-q", "-o", "4g"], input=prog, text=True, check=True,
                   stdout=subprocess.DEVNULL)


def build(upto, jobs):
    with tempfile.TemporaryDirectory() as tmp:
        parts = [(n, n, os.path.join(tmp, f"{n}.jsonl")) for n in range(1, upto + 1)]
        # Тяжёлые порядки (64, 96, …) идут первыми, чтобы не остаться хвостом.
        heavy = sorted(parts, key=lambda p: -(p[0] & -p[0]) * p[0])
        with ThreadPoolExecutor(jobs) as ex:
            list(ex.map(lambda p: _run(*p), heavy))
        OUT.parent.mkdir(parents=True, exist_ok=True)
        with OUT.open("w") as out:
            for _, _, path in parts:
                with open(path) as f:
                    for line in f:
                        json.loads(line)  # битая строка должна уронить сборку
                        out.write(line)


def _refs(r):
    for sub in r["subs"] or []:
        yield sub["group"]
        if "quotient" in sub:
            yield sub["quotient"]


def build_extra(keys, upto):
    """Группы порядка выше upto, нужные как примеры, вместе со всеми их
    подгруппами и факторами порядка выше upto, чтобы ссылки не висели."""
    have = load(extra=True)
    todo = {k for k in keys if k not in have}
    while todo:
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "extra.jsonl")
            ks = ", ".join(f"[{k.replace(':', ', ')}]" for k in sorted(todo))
            prog = f'KEYS:=[{ks}];; OUT:="{path}";; Read("{SCRIPT}");\n'
            subprocess.run(["gap", "-q", "-o", "4g"], input=prog, text=True, check=True,
                           stdout=subprocess.DEVNULL)
            with open(path) as f:
                new = [json.loads(line) for line in f]
        with EXTRA.open("a") as out:
            for r in new:
                out.write(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n")
                have[r["key"]] = r
        todo = {k for r in new for k in _refs(r) if k not in have and int(k.split(":")[0]) > upto}


def build_products(upto):
    prog = f'HI:={upto};; OUT:="{PRODUCTS}";; Read("{PRODUCTS_SCRIPT}");\n'
    subprocess.run(["gap", "-q", "-o", "4g"], input=prog, text=True, check=True,
                   stdout=subprocess.DEVNULL)


def load_products(path=PRODUCTS):
    """Словарь (key_a, key_b) → key произведения, в обоих порядках."""
    out = {}
    if Path(path).exists():
        with open(path) as f:
            for r in map(json.loads, f):
                out[r["a"], r["b"]] = out[r["b"], r["a"]] = r["prod"]
    return out


# Свойства, добавленные в словарь после сборки таблицы. Для конечной группы
# их значение следует из уже посчитанных: конечная группа хопфова и линейна
# (регулярное представление), полициклическая тогда и только тогда, когда
# разрешима.
FINITE_DERIVED = {
    "hopfian": lambda p: True,
    "linear": lambda p: True,
    "polycyclic": lambda p: p["solvable"],
    "bounded-exponent": lambda p: True,
    "free-abelian": lambda p: p["trivial"],
    "no-finite-quotients": lambda p: p["trivial"],
    "countable": lambda p: True,
    "fin-pres": lambda p: True,
    "rec-pres": lambda p: True,
    "rec-pres-ctbl": lambda p: True,
    "word-problem": lambda p: True,
    "left-orderable": lambda p: p["trivial"],
    "bi-orderable": lambda p: p["trivial"],
    "amenable": lambda p: True,
    "property-t": lambda p: True,
    "residually-nilpotent": lambda p: p["nilpotent"],
}


def build_aut(jobs):
    """Aut(G), Inn(G), Out(G) для всех групп таблицы (gap/aut.g) → grp-aut.jsonl."""
    keys = sorted(load(extra=True), key=lambda k: tuple(map(int, k.split(":"))))
    chunks = [keys[i::jobs * 4] for i in range(jobs * 4)]
    with tempfile.TemporaryDirectory() as tmp:
        def one(i):
            path = os.path.join(tmp, f"{i}.jsonl")
            ks = ", ".join(f"[{k.replace(':', ', ')}]" for k in chunks[i])
            prog = f'KEYS:=[{ks}];; OUT:="{path}";; Read("{AUT_SCRIPT}");\n'
            subprocess.run(["gap", "-q", "-o", "8g"], input=prog, text=True, check=True,
                           stdout=subprocess.DEVNULL)
            return path
        with ThreadPoolExecutor(jobs) as ex:
            paths = list(ex.map(one, range(len(chunks))))
        recs = {}
        for path in paths:
            with open(path) as f:
                for line in f:
                    r = json.loads(line)
                    recs[r["key"]] = r
    with AUT.open("w") as out:
        for k in keys:
            if k in recs:
                out.write(json.dumps(recs[k], ensure_ascii=False, separators=(",", ":")) + "\n")


def build_table(script, target, jobs):
    """Данные по всем группам таблицы скриптом GAP (KEYS, OUT) → target (jsonl)."""
    keys = sorted(load(extra=True), key=lambda k: tuple(map(int, k.split(":"))))
    chunks = [keys[i::jobs * 4] for i in range(jobs * 4)]
    with tempfile.TemporaryDirectory() as tmp:
        def one(i):
            path = os.path.join(tmp, f"{i}.jsonl")
            ks = ", ".join(f"[{k.replace(':', ', ')}]" for k in chunks[i])
            prog = f'KEYS:=[{ks}];; OUT:="{path}";; Read("{script}");\n'
            subprocess.run(["gap", "-q", "-o", "8g"], input=prog, text=True, check=True,
                           stdout=subprocess.DEVNULL)
            return path
        with ThreadPoolExecutor(jobs) as ex:
            paths = list(ex.map(one, range(len(chunks))))
        recs = {}
        for path in paths:
            with open(path) as f:
                for line in f:
                    r = json.loads(line)
                    recs[r["key"]] = r
    with target.open("w") as out:
        for k in keys:
            if k in recs:
                out.write(json.dumps(recs[k], ensure_ascii=False, separators=(",", ":")) + "\n")


def present_tasks():
    """Копредставления из карточек архива: [(id, образующие, соотношения)]."""
    out = []
    for p in sorted((ROOT / "data" / "archive").glob("*/*.jsonl")):
        for line in p.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            c = json.loads(line)
            for i, pr in enumerate(c.get("копредставления", [])):
                out.append((f"{c['id']}#{i}", pr["образующие"], pr["соотношения"]))
    return out


def build_present():
    tasks = present_tasks()
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "p.jsonl")
        ts = ", ".join("[" + json.dumps(i) + ", [" + ", ".join(json.dumps(g) for g in gs) + "], " + json.dumps(r) + "]"
                       for i, gs, r in tasks)
        prog = f'TASKS:=[{ts}];; OUT:="{path}";; Read("{PRESENT_SCRIPT}");\n'
        subprocess.run(["gap", "-q", "-o", "8g"], input=prog, text=True, check=True, stdout=subprocess.DEVNULL)
        PRESENT.write_text(open(path).read())


def load_present(path=PRESENT):
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["id"]: r for r in map(json.loads, f)}


def load_compl(path=COMPL):
    """key → [дополняема ли подгруппа класса i] (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_endo(path=ENDO):
    """key → [вполне инвариантна ли подгруппа класса i] (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_elts(path=ELTS):
    """key → классы сопряжённых элементов (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_aut(path=AUT):
    """key → запись об Aut, Inn, Out (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def _factor(n):
    out, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def arith_props(n):
    """Арифметические свойства конечной группы порядка n."""
    f = _factor(n)
    return {"p-group": len(f) <= 1, "prime-order": len(f) == 1 and sum(f.values()) == 1,
            "order-p2": len(f) == 1 and sum(f.values()) == 2,
            "order-pq": len(f) == 2 and sum(f.values()) == 2,
            "two-primes": len(f) <= 2, "odd-order": n % 2 == 1}


def arith_sub_props(n, m):
    """Свойства вложения подгруппы порядка m в группу порядка n (индекс n/m)."""
    i = n // m
    fi, fn = _factor(i), _factor(n)
    fm = _factor(m)
    return {"index-2": i == 2, "prime-index": len(fi) == 1 and sum(fi.values()) == 1,
            "min-prime-index": n > 1 and i == min(fn),
            "sylow": len(fm) == 1 and math.gcd(m, i) == 1,
            "hall": math.gcd(m, i) == 1}


def load(path=OUT, extra=False):
    """Словарь key → запись группы; extra — с группами из grp-extra.jsonl."""
    with open(path) as f:
        out = {g["key"]: g for g in map(json.loads, f)}
    if extra and EXTRA.exists():
        with EXTRA.open() as f:
            out.update((g["key"], g) for g in map(json.loads, f))
    cyclic = {k: g["props"].get("cyclic") for k, g in out.items()}
    for g in out.values():
        for p, f in FINITE_DERIVED.items():
            g["props"].setdefault(p, f(g["props"]))
        n = int(g["key"].split(":")[0])
        for p, v in arith_props(n).items():
            g["props"].setdefault(p, v)
        if g["subs"] is not None:
            # экспонента 2 (3): все циклические подгруппы порядка 1 или 2 (3)
            cyc = {int(s["group"].split(":")[0]) for s in g["subs"]
                   if cyclic.get(s["group"], s["group"] in ("1:1", "2:1", "3:1"))}
            g["props"].setdefault("exponent-2", cyc <= {1, 2})
            orders = {int(s["group"].split(":")[0]) for s in g["subs"]}
            n0 = int(g["key"].split(":")[0])
            g["props"].setdefault("clt", all(d in orders for d in range(1, n0 + 1) if n0 % d == 0))
            g["props"].setdefault("exponent-3", cyc <= {1, 3})
            g["props"].setdefault("exponent-4", cyc <= {1, 2, 4})
            g["props"].setdefault("exponent-6", cyc <= {1, 2, 3, 6})
            g["props"].setdefault("dedekind", all(x["props"].get("normal") for x in g["subs"]))
        for s in g["subs"] or []:
            m = int(s["group"].split(":")[0])
            for p, v in arith_sub_props(n, m).items():
                s["props"].setdefault(p, v)
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--до", dest="upto", type=int, default=100)
    ap.add_argument("--нитей", dest="jobs", type=int, default=os.cpu_count())
    ap.add_argument("--только-произведения", dest="only_products", action="store_true")
    ap.add_argument("--добавить", dest="extra", nargs="+", metavar="n:i",
                    help="досчитать отдельные группы выше --до в data/finite/grp-extra.jsonl")
    ap.add_argument("--копредставления", dest="present", action="store_true",
                    help="порядок и тип групп по копредставлениям из карточек → data/finite/grp-present.jsonl")
    ap.add_argument("--дополнения", dest="compl", action="store_true",
                    help="дополняемость подгрупп всех групп таблицы в data/finite/grp-compl.jsonl")
    ap.add_argument("--эндоморфизмы", dest="endo", action="store_true",
                    help="вполне инвариантные подгруппы всех групп таблицы в data/finite/grp-endo.jsonl")
    ap.add_argument("--элементы", dest="elts", action="store_true",
                    help="классы сопряжённых элементов всех групп таблицы в data/finite/grp-elts.jsonl")
    ap.add_argument("--авт", dest="aut", action="store_true",
                    help="посчитать Aut, Inn, Out всех групп таблицы в data/finite/grp-aut.jsonl")
    a = ap.parse_args()
    if a.present:
        build_present()
        print(PRESENT, sum(1 for _ in PRESENT.open()))
        raise SystemExit
    if a.compl:
        build_table(COMPL_SCRIPT, COMPL, a.jobs)
        print(COMPL, sum(1 for _ in COMPL.open()))
        raise SystemExit
    if a.elts:
        build_table(ELTS_SCRIPT, ELTS, a.jobs)
        print(ELTS, sum(1 for _ in ELTS.open()))
        raise SystemExit
    if a.endo:
        build_table(ENDO_SCRIPT, ENDO, a.jobs)
        print(ENDO, sum(1 for _ in ENDO.open()))
        raise SystemExit
    if a.aut:
        build_aut(a.jobs)
        print(AUT, sum(1 for _ in AUT.open()))
        raise SystemExit
    if a.extra:
        build_extra(a.extra, a.upto)
        print(EXTRA, sum(1 for _ in EXTRA.open()))
        raise SystemExit
    if not a.only_products:
        build(a.upto, a.jobs)
        print(OUT, sum(1 for _ in OUT.open()))
    build_products(a.upto)
    print(PRODUCTS, sum(1 for _ in PRODUCTS.open()))
