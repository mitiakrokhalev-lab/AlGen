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


def load_aut(path=AUT):
    """key → запись об Aut, Inn, Out (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load(path=OUT, extra=False):
    """Словарь key → запись группы; extra — с группами из grp-extra.jsonl."""
    with open(path) as f:
        out = {g["key"]: g for g in map(json.loads, f)}
    if extra and EXTRA.exists():
        with EXTRA.open() as f:
            out.update((g["key"], g) for g in map(json.loads, f))
    for g in out.values():
        for p, f in FINITE_DERIVED.items():
            g["props"].setdefault(p, f(g["props"]))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--до", dest="upto", type=int, default=100)
    ap.add_argument("--нитей", dest="jobs", type=int, default=os.cpu_count())
    ap.add_argument("--только-произведения", dest="only_products", action="store_true")
    ap.add_argument("--добавить", dest="extra", nargs="+", metavar="n:i",
                    help="досчитать отдельные группы выше --до в data/finite/grp-extra.jsonl")
    ap.add_argument("--авт", dest="aut", action="store_true",
                    help="посчитать Aut, Inn, Out всех групп таблицы в data/finite/grp-aut.jsonl")
    a = ap.parse_args()
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
