"""Таблица конечных групп из библиотеки SmallGroups (GAP).

Каждая запись посчитана GAP, а не написана рукой: свойства группы, все классы
сопряжённых подгрупп со свойствами вложения, факторы по нормальным
подгруппам и канонические подгруппы (центр, коммутант, Фраттини, нормализатор,
централизатор, ядро, нормальное замыкание) как номера классов.

    python3 -m algen.finite --до 100

пишет data/finite/grp-small.jsonl и таблицу прямых произведений
data/finite/grp-small-products.jsonl. Порядки считаются параллельно кусками,
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


def load(path=OUT):
    """Словарь key → запись группы."""
    with open(path) as f:
        return {g["key"]: g for g in map(json.loads, f)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--до", dest="upto", type=int, default=100)
    ap.add_argument("--нитей", dest="jobs", type=int, default=os.cpu_count())
    ap.add_argument("--только-произведения", dest="only_products", action="store_true")
    a = ap.parse_args()
    if not a.only_products:
        build(a.upto, a.jobs)
        print(OUT, sum(1 for _ in OUT.open()))
    build_products(a.upto)
    print(PRODUCTS, sum(1 for _ in PRODUCTS.open()))
