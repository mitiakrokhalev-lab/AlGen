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
PROPS_SCRIPT = Path(__file__).with_name("gap") / "props.g"
PROPS = ROOT / "data" / "finite" / "grp-props.jsonl"
PROPS2_SCRIPT = Path(__file__).with_name("gap") / "props2.g"
PROPS2 = ROOT / "data" / "finite" / "grp-props2.jsonl"
COMPL = ROOT / "data" / "finite" / "grp-compl.jsonl"
ENDO_SCRIPT = Path(__file__).with_name("gap") / "endo.g"
ENDO = ROOT / "data" / "finite" / "grp-endo.jsonl"
ELTS_SCRIPT = Path(__file__).with_name("gap") / "elts.g"
ELTS = ROOT / "data" / "finite" / "grp-elts.jsonl"
HOMS_SCRIPT = Path(__file__).with_name("gap") / "homs.g"
HOMS = ROOT / "data" / "finite" / "grp-homs.jsonl"
HK_SCRIPT = Path(__file__).with_name("gap") / "hk.g"
HK = ROOT / "data" / "finite" / "grp-hk.jsonl"
PERM_SCRIPT = Path(__file__).with_name("gap") / "perm.g"
PERM = ROOT / "data" / "finite" / "grp-perm.jsonl"
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
    "linear-c": lambda p: True,
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


def build_table(script, target, jobs, stall=None, deadline=None, keys=None):
    """Данные по всем группам таблицы скриптом GAP (KEYS, OUT) → target (jsonl).

    stall — сколько секунд ждать строку об очередной группе: группа, на которой GAP
    застрял дольше, пропускается (строка с «"skipped": true»), остаток пачки
    считается заново. deadline — время (time.time()), после которого записывается
    то, что есть (недосчитанные группы просто отсутствуют)."""
    import time
    keys = sorted(keys if keys is not None else load(extra=True), key=lambda k: tuple(map(int, k.split(":"))))
    chunks = [keys[i::jobs * 4] for i in range(jobs * 4)]
    with tempfile.TemporaryDirectory() as tmp:
        def one(i):
            path = os.path.join(tmp, f"{i}.jsonl")
            todo, done, part = list(chunks[i]), [], 0
            while todo and (deadline is None or time.time() < deadline):
                part += 1
                ppath = f"{path}.{part}"
                ks = ", ".join(f"[{k.replace(':', ', ')}]" for k in todo)
                prog = f'KEYS:=[{ks}];; OUT:="{ppath}";; Read("{script}");\n'
                pr = subprocess.Popen(["gap", "-q", "-o", "8g"], stdin=subprocess.PIPE, text=True,
                                      stdout=subprocess.DEVNULL)
                pr.stdin.write(prog); pr.stdin.close()
                seen, last = 0, time.time()
                while pr.poll() is None:
                    time.sleep(2)
                    n = sum(1 for _ in open(ppath)) if os.path.exists(ppath) else 0
                    if n > seen:
                        seen, last = n, time.time()
                    if (stall and time.time() - last > stall) or (deadline and time.time() > deadline):
                        pr.kill(); pr.wait()
                        break
                lines = open(ppath).read().splitlines() if os.path.exists(ppath) else []
                lines = [x for x in lines if x.endswith("}")]
                done += lines
                todo = todo[len(lines):]
                if pr.returncode not in (0, None) and todo and (deadline is None or time.time() < deadline):
                    done.append(json.dumps({"key": todo[0], "skipped": True}))
                    todo = todo[1:]
            with open(path, "w") as f:
                f.write("\n".join(done) + ("\n" if done else ""))
            return path
        with ThreadPoolExecutor(jobs) as ex:
            paths = list(ex.map(one, range(len(chunks))))
        recs = {}
        for path in paths:
            with open(path) as f:
                for line in f:
                    if line.strip():
                        r = json.loads(line)
                        recs[r["key"]] = r
    with target.open("w") as out:
        for k in keys:
            if k in recs:
                out.write(json.dumps(recs[k], ensure_ascii=False, separators=(",", ":")) + "\n")
    skipped = sum(1 for r in recs.values() if r.get("skipped"))
    print(f"групп {len(keys)}, записано {len(recs)}, пропущено (застряли) {skipped}")


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


def load_props(path=PROPS):
    """key → свойства из gap/props.g: metabelian, class-2, dedekind, exponent-2/3,
    prime-orders (по порядкам элементов). Пусто, если таблица не посчитана."""
    if not Path(path).exists():
        return {}
    out = {}
    with open(path) as f:
        for r in map(json.loads, f):
            if r.get("skipped"):
                continue
            ords = r["orders"]
            isp = lambda m: m > 1 and all(m % d for d in range(2, int(m ** 0.5) + 1))
            out[r["key"]] = {"metabelian": r["metabelian"], "class-2": r["class-2"], "dedekind": r["dedekind"],
                             "exponent-2": r["exponent"] <= 2, "exponent-3": r["exponent"] in (1, 3),
                             "prime-orders": all(m == 1 or isp(m) for m in ords)}
    return out


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


def load_hk(path=HK):
    """key → H ∩ K, ⟨H, K⟩, [H, K] для пар представителей классов подгрупп (если посчитано)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_perm(path=PERM):
    """key → неперестановочные пары представителей классов подгрупп (если посчитано)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_homs(path=HOMS):
    """key → представители классов эндоморфизмов (если таблица посчитана)."""
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def load_chars(path=None):
    """key → запись о подгруппах 1, Z, G′, Φ и Aut/Out (grp-chars.jsonl), если посчитано."""
    path = path or Path(__file__).resolve().parents[2] / "data" / "finite" / "grp-chars.jsonl"
    if not Path(path).exists():
        return {}
    with open(path) as f:
        return {r["key"]: r for r in map(json.loads, f)}


def library_finite_keys():
    """Ключи n:i всех конечных групп библиотеки (таблица, Aut/Out, характеристические)."""
    import re
    from .library import built_library
    return [k for k, o in built_library().obj.items()
            if o.get("конечная") and re.fullmatch(r"\d+:\d+", k) and int(k.split(":")[0]) not in (512, 1024, 1536)]


PROPS2X_SCRIPT = Path(__file__).with_name("gap") / "props2x.g"
PROPS2X = ROOT / "data" / "finite" / "grp-props2x.jsonl"


def gap_expr(key):
    """Выражение GAP для построенной конечной группы библиотеки по её ключу:
    «n:i» — SmallGroup; «n:Aut(K)», «n:Out(K)», «n:G′(K)», «n:K/Z», «n:K/Φ»,
    где K — ключ библиотеки. None — ключ не разбирается."""
    import re
    order, _, desc = key.partition(":")
    if not order.isdigit() or not desc:
        return None
    if desc.isdigit():
        return f"SmallGroup({order}, {desc})"
    for pat, fmt in ((r"Aut\((.+)\)", "AutomorphismGroup(AsPc({}))"),
                     (r"Out\((.+)\)", "OutGroup(AutomorphismGroup(AsPc({})))"),
                     (r"G′\((.+)\)", "DerivedSubgroup(AsPc({}))"),
                     (r"(.+)/Z", "QZ(AsPc({}))"), (r"(.+)/Φ", "QF(AsPc({}))")):
        m = re.fullmatch(pat, desc)
        if m:
            inner = gap_expr(m.group(1))
            return None if inner is None else fmt.format(inner)
    return None


def props2x_jobs(max_order=100_000):
    """[(ключ, выражение)] построенных конечных групп библиотеки без props2, порядок ⩽ max_order."""
    import re
    from .library import Library
    lib = Library()
    out = []
    for k, o in lib.obj.items():
        if not o.get("конечная") or re.fullmatch(r"\d+:\d+", k) or o["свойства"].get("two-generated") is not None:
            continue
        if int(k.split(":")[0]) > max_order:
            continue
        e = gap_expr(k)
        if e is not None:
            out.append((k, e))
    return sorted(out, key=lambda x: int(x[0].split(":")[0]))


def build_props2x(jobs, max_order=100_000, chunk=4, seconds=900):
    """props2 построенных групп (gap/props2x.g) → grp-props2x.jsonl. Пачка, не уложившаяся
    в seconds, пропускается (её группы — без записи; повторный запуск досчитает остальное)."""
    todo = props2x_jobs(max_order)
    done = {}
    if PROPS2X.exists():
        done = {r["key"]: r for r in map(json.loads, PROPS2X.open())}
    todo = [j for j in todo if j[0] not in done]
    parts = [todo[i:i + chunk] for i in range(0, len(todo), chunk)]
    with tempfile.TemporaryDirectory() as tmp:
        def one(i):
            path = os.path.join(tmp, f"{i}.jsonl")
            js = ", ".join("[" + json.dumps(k, ensure_ascii=False) + ", " + json.dumps(e) + "]" for k, e in parts[i])
            prog = f'JOBS:=[{js}];; OUT:="{path}";; Read("{PROPS2X_SCRIPT}");\n'
            try:
                subprocess.run(["gap", "-q", "-o", "8g"], input=prog, text=True, timeout=seconds,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except subprocess.TimeoutExpired:
                pass
            return path
        with ThreadPoolExecutor(jobs) as ex:
            paths = list(ex.map(one, range(len(parts))))
        for path in paths:
            if os.path.exists(path):
                for line in open(path):
                    try:
                        r = json.loads(line)
                    except ValueError:
                        continue
                    done[r["key"]] = r
    with PROPS2X.open("w") as out:
        for k in sorted(done, key=lambda k: (int(k.split(":")[0]), k)):
            out.write(json.dumps(done[k], ensure_ascii=False, separators=(",", ":")) + "\n")


def load_props2(path=PROPS2, extra=PROPS2X):
    """key → запись props2.g (если посчитана); плюс построенные группы (props2x.g)."""
    out = {}
    for pth in (path, extra):
        if pth is not None and Path(pth).exists():
            with open(pth) as f:
                for r in map(json.loads, f):
                    if not r.get("skipped"):
                        out[r["key"]] = r
    return out


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
            g["props"].setdefault("prime-orders", all(c == 1 or all(c % q for q in range(2, c)) for c in cyc))
            g["props"].setdefault("exponent-4", cyc <= {1, 2, 4})
            g["props"].setdefault("exponent-6", cyc <= {1, 2, 3, 6})
            g["props"].setdefault("dedekind", all(x["props"].get("normal") for x in g["subs"]))
        for s in g["subs"] or []:
            m = int(s["group"].split(":")[0])
            for p, v in arith_sub_props(n, m).items():
                s["props"].setdefault(p, v)
    return out


CHARS = Path(__file__).resolve().parents[2] / "data" / "finite" / "grp-chars.jsonl"
CHARS_SCRIPT = Path(__file__).resolve().parent / "gap" / "chars.g"


def chars_jobs():
    """Конечные группы библиотеки без таблицы подгрупп: [ключ, n, i, вид]."""
    import re
    from .library import built_library
    from .logic import Vocab
    lib = built_library(Vocab.section("grp"))
    out = []
    for k, o in lib.obj.items():
        if not o["конечная"] or o["подгруппы"] is not None or k == "1:1":
            continue
        m = re.fullmatch(r"(\d+):(\d+)", k)
        if m:
            out.append([k, int(m[1]), int(m[2]), "G"])
            continue
        m = re.fullmatch(r"\d+:(Aut|Out)\((\d+):(\d+)\)", k)
        if m:
            out.append([k, int(m[2]), int(m[3]), m[1]])
    return sorted(out, key=lambda j: int(j[0].split(":")[0]))


def build_chars(jobs, per=300, chunk=4):
    """Характеристические подгруппы и Aut/Out (gap/chars.g) → grp-chars.jsonl.
    Пачка из chunk групп — один процесс GAP не дольше per секунд на группу;
    записанное до остановки сохраняется (GAP пишет построчно)."""
    todo = chars_jobs()
    done = {}
    if CHARS.exists():
        done = {r["key"]: r for r in map(json.loads, CHARS.open())}
    todo = [j for j in todo if j[0] not in done]
    chunks = [todo[i:i + chunk] for i in range(0, len(todo), chunk)]
    with tempfile.TemporaryDirectory() as tmp:
        def one(i):
            path = os.path.join(tmp, f"{i}.jsonl")
            js = ", ".join(f'["{k}", {n}, {m}, "{v}"]' for k, n, m, v in chunks[i])
            prog = f'JOBS:=[{js}];; OUT:="{path}";; Read("{CHARS_SCRIPT}");\n'
            try:
                subprocess.run(["gap", "-q", "-o", "8g"], input=prog, text=True, timeout=per * len(chunks[i]),
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except subprocess.TimeoutExpired:
                pass
            return path
        with ThreadPoolExecutor(jobs) as ex:
            paths = list(ex.map(one, range(len(chunks))))
        for path in paths:
            if os.path.exists(path):
                for line in open(path):
                    try:
                        r = json.loads(line)
                    except ValueError:
                        continue
                    done[r["key"]] = r
    with CHARS.open("w") as out:
        for k in sorted(done, key=lambda k: (int(k.split(":")[0]), k)):
            out.write(json.dumps(done[k], ensure_ascii=False, separators=(",", ":")) + "\n")
    print(f"посчитано {len(done)} из {len(chars_jobs())}")


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
    ap.add_argument("--свойства", dest="gprops", action="store_true",
                    help="метабелевость, ступень 2, экспонента, порядки элементов, дедекиндовость → data/finite/grp-props.jsonl")
    ap.add_argument("--свойства2x", dest="gprops2x", action="store_true",
                    help="props2 построенных групп библиотеки (Aut/Out/G′//Z//Φ) → data/finite/grp-props2x.jsonl")
    ap.add_argument("--до-порядка", dest="max_order", type=int, default=100_000)
    ap.add_argument("--свойства2", dest="gprops2", action="store_true",
                    help="ранг, клт, дедекиндовость, свойства собственных подгрупп всех конечных групп "
                         "библиотеки с ключом n:i (gap/props2.g) → data/finite/grp-props2.jsonl")
    ap.add_argument("--гомоморфизмы", dest="homs", action="store_true",
                    help="эндоморфизмы всех групп таблицы в data/finite/grp-homs.jsonl")
    ap.add_argument("--пересечения", dest="hk", action="store_true",
                    help="H ∩ K, ⟨H, K⟩, [H, K] для пар представителей классов в data/finite/grp-hk.jsonl")
    ap.add_argument("--перестановочность", dest="perm", action="store_true",
                    help="перестановочность представителей классов подгрупп в data/finite/grp-perm.jsonl")
    ap.add_argument("--авт", dest="aut", action="store_true",
                    help="посчитать Aut, Inn, Out всех групп таблицы в data/finite/grp-aut.jsonl")
    ap.add_argument("--застой", dest="stall", type=int, default=300,
                    help="пропускать группу, на которой GAP думает дольше стольких секунд")
    ap.add_argument("--минут", dest="minutes", type=int, default=300,
                    help="через столько минут записать то, что есть")
    ap.add_argument("--характеристические", dest="chars", action="store_true",
                    help="1, Z, G′, Φ, Aut, Out групп без таблицы подгрупп → data/finite/grp-chars.jsonl")
    a = ap.parse_args()
    if a.chars:
        build_chars(a.jobs, per=a.stall)
        raise SystemExit
    if a.present:
        build_present()
        print(PRESENT, sum(1 for _ in PRESENT.open()))
        raise SystemExit
    if a.compl:
        build_table(COMPL_SCRIPT, COMPL, a.jobs)
        print(COMPL, sum(1 for _ in COMPL.open()))
        raise SystemExit
    if a.gprops:
        import time
        build_table(PROPS_SCRIPT, PROPS, a.jobs, stall=a.stall, deadline=time.time() + a.minutes * 60)
        print(PROPS, sum(1 for _ in PROPS.open()))
        raise SystemExit
    if a.homs:
        import time
        build_table(HOMS_SCRIPT, HOMS, a.jobs, stall=a.stall, deadline=time.time() + a.minutes * 60)
        print(HOMS, sum(1 for _ in HOMS.open()))
        raise SystemExit
    if a.gprops2x:
        build_props2x(a.jobs, max_order=a.max_order)
        print(PROPS2X, sum(1 for _ in PROPS2X.open()))
        raise SystemExit
    if a.gprops2:
        import time
        build_table(PROPS2_SCRIPT, PROPS2, a.jobs, stall=a.stall, deadline=time.time() + a.minutes * 60,
                    keys=library_finite_keys())
        print(PROPS2, sum(1 for _ in PROPS2.open()))
        raise SystemExit
    if a.elts:
        build_table(ELTS_SCRIPT, ELTS, a.jobs)
        print(ELTS, sum(1 for _ in ELTS.open()))
        raise SystemExit
    if a.endo:
        build_table(ENDO_SCRIPT, ENDO, a.jobs)
        print(ENDO, sum(1 for _ in ENDO.open()))
        raise SystemExit
    if a.hk:
        build_table(HK_SCRIPT, HK, a.jobs, stall=a.stall)
        print(HK, sum(1 for _ in HK.open()))
        raise SystemExit
    if a.perm:
        build_table(PERM_SCRIPT, PERM, a.jobs, stall=a.stall)
        print(PERM, sum(1 for _ in PERM.open()))
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
