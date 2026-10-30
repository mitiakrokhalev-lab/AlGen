"""Таблицы баз: значения всех атомов над вселенной термов на всех строках
библиотеки — считаются один раз, а схемы берут из них столбцы.

База — переменные (G; G и N ⩽ G; A, B; …). Вселенная базы — все термы глубины 1
над её переменными (Z(G), G′, G/N, A × B, …) и отобранные термы глубины 2.
Схема — замкнутый (с подтермами) набор не больше чем из k + 1 термов вселенной.
Условие выдаётся ровно в одной схеме: той, что порождена термами, которых оно
касается. Поэтому одно и то же условие не повторяется в разных схемах.

    cd py
    python3 -m algen.table вселенная GN                      # термы вселенной
    python3 -m algen.table схемы GN                          # схемы базы
    python3 -m algen.table строить GN --часть 3/20 --каталог ../кэш/табл
    python3 -m algen.table перебор GN --каталог ../кэш/табл --выход ../кэш/прогон --часть 1/4
"""

import argparse
import io
import json
import signal
import multiprocessing as mp
import os
import pickle
import sys
import time
import traceback
from itertools import combinations, product
from pathlib import Path

import numpy as np

from . import enumerate as E
from .etalon import scheme, term
from .library import _fingerprint, built_library
from .logic import App, Var, Vocab

BASES = {
    "G": "∀ G : Grp",
    "GN": "∀ G : Grp; ∀ N : Sub(G)",
    "AB": "∀ A : Grp; ∀ B : Grp",
    "GHK": "∀ G : Grp; ∀ H : Sub(G); ∀ K : Sub(G)",
    "GMN": "∀ G : Grp; ∀ M : Sub(G); ∀ N : Sub(M)",
    "GHF": "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, H)",
    "Fam": "∀ F : Fam",
    # новые сорта: действие (со скрытой точкой x_A), элемент, эндоморфизм
    # (два элемента «Gxy» — позже: пар классов слишком много для таблицы)
    "GX": "∀ G : Grp; ∀ A : GSet(G)",
    "Gx": "∀ G : Grp; ∀ x : Elt(G)",
    "GE": "∀ G : Grp; ∀ F : Mor(G, G)",
}

# Конструкции вселенной (термы-«вершины» схем).
CONS = ["center", "commutator", "ab", "aut", "inn", "quotient", "prod", "freeprod", "wreath",
        "meet", "join", "normalizer", "centralizer", "normal-closure", "ker", "im", "torsion", "frattini", "prod-fam", "sum-fam",
        "stab", "act-ker", "gen", "centralizer-elt"]
SYMMETRIC = {"prod", "freeprod"}            # A × B ≅ B × A: берём один порядок
SYMMETRIC_SUB = {"meet", "join"}            # meet(G, H, K) = meet(G, K, H)

# Термы глубины 2, известные по задачам (подтермы добавляются сами).
DEPTH2 = {
    "G": ["center(commutator(G))", "commutator(commutator(G))", "G / center(G)",
          "center(G / center(G))", "G / commutator(G)", "aut(G) / inn(G)",
          "G / frattini(G)"],
    "AB": ["center(A × B)", "commutator(A × B)"],
    "GMN": ["M / N", "G / M", "normal-closure(M, N)"],
    "GHF": ["G / ker(F)"],
    "Fam": ["center(prod-fam(F))", "commutator(prod-fam(F))", "prod-fam(F) / sum-fam(F)"],
}


def universe(vocab, base):
    """Термы вселенной базы (строки) в порядке построения."""
    g, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
    vars_ = list(g.terms)
    out = []
    for op in CONS:
        c = vocab.cons.get(op)
        if not c:
            continue
        for args in product(vars_, repeat=len(c["in"])):
            if op in SYMMETRIC and str(args[0]) > str(args[1]):
                continue
            if op in SYMMETRIC_SUB and not str(args[1]) < str(args[2]):
                continue
            t = g.make(op, list(args))
            if t is not None and t not in out:
                out.append(t)
    names = {str(t): t for t in g.terms}
    for x in DEPTH2.get(base, []):
        t = term(g, x, names, "grp")
        for s in subterms(t):
            if isinstance(s, App) and s not in out:
                out.append(s)
    return [str(t) for t in out]


def subterms(t):
    """Подтермы t, включая сам t, снизу вверх."""
    out = []
    if isinstance(t, App):
        for a in t.args:
            for s in subterms(a):
                if s not in out:
                    out.append(s)
    out.append(t)
    return out


def closure(g, elems):
    """Замыкание набора: подтермы и связи (объемлющая группа, области F)."""
    out, todo = set(), list(elems)
    while todo:
        t = todo.pop()
        if t in out:
            continue
        out.add(t)
        if isinstance(t, App):
            todo += list(t.args)
        todo += [v for v in g.terms[t].links.values() if v is not None]
    return out


def maximal(g, elems):
    """Верхние элементы: не подтермы и не связи других элементов набора."""
    low = set()
    for t in elems:
        low |= closure(g, [t]) - {t}
    return [t for t in elems if t not in low]


# Симметрии баз: перестановка переменных, переводящая запись базы в себя.
SWAP = {"AB": ("A", "B"), "GHK": ("H", "K")}


def _swap(s, pair):
    import re
    a, b = pair
    return re.sub(rf"\b({a}|{b})\b", lambda m: b if m.group(1) == a else a, s)


def schemes(vocab, base, k=2):
    """Схемы базы: (id, термы-строки) — замыкания наборов из ⩽ k + 1 термов
    вселенной, без повторов. id — номера термов вселенной через «-»."""
    g, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
    names = {str(t): t for t in g.terms}
    uni = universe(vocab, base)
    ts = [term(g, x, names, "grp") for x in uni]
    num = {t: i + 1 for i, t in enumerate(ts)}
    vars_ = [t for t in g.terms if isinstance(t, Var)]
    seen, out = set(), []
    swap = SWAP.get(base)
    for r in range(0, k + 2):
        for pick in combinations(ts, r):
            cl = closure(g, list(pick) + vars_)
            if len(maximal(g, cl)) > k + 1:
                continue
            terms_ = sorted((t for t in cl if isinstance(t, App)), key=num.get)
            key = tuple(terms_)
            if key in seen:
                continue
            seen.add(key)
            if swap:
                # схема, симметричная уже взятой (A ↔ B, H ↔ K), — тот же набор задач
                try:
                    tw = tuple(sorted({term(g, _swap(str(t), swap), names, "grp") for t in terms_}, key=num.get))
                except Exception:
                    tw = None
                if tw is not None and tw != key and tw in seen:
                    continue
                if tw is not None:
                    seen.add(tw)
            sid = base + ("-" + "-".join(str(num[t]) for t in terms_) if terms_ else "")
            out.append((sid, [str(t) for t in terms_]))
    return out


# --- таблица ------------------------------------------------------------------

def grow_ops(vocab):
    """Достраивать служебные конструкции и дешёвые унарные (Z, ′, кручение),
    но не конструкции вселенной: их термы уже даны."""
    return set(vocab.cons) - set(CONS) | {"center", "commutator", "torsion"}


def skeleton(lib, vocab, base, part=None, with_rows=False):
    return E.SchemeForm(lib, vocab, BASES[base], universe(vocab, base),
                        grow_ops=grow_ops(vocab), part=part, with_rows=with_rows)


def _fp(base):
    return f"{_fingerprint()}:{base}:{','.join(sorted(E.SKIP))}"


def build(lib, vocab, base, part, outdir, skel=None):
    """Часть таблицы базы. skel — готовый каркас (теория строится один раз на
    базу, части получают его через fork); иначе строится здесь."""
    t0 = time.time()
    if skel is not None:
        f = skel
        f.sc.s = f.sc.T.solver()  # свой решатель в дочернем процессе
        f.fill_rows(part)
    else:
        f = skeleton(lib, vocab, base, part=part, with_rows=True)
    path = Path(outdir) / f"{base}.{part[0]}-{part[1]}.pickle"
    path.parent.mkdir(parents=True, exist_ok=True)
    data = {"отпечаток": _fp(base), "атомов": len(f.atoms), "envs": f.envs, "skipped": f.skipped,
            **{k: np.packbits(getattr(f, k), axis=1) for k in "mse"}}
    with open(path, "wb") as fh:
        pickle.dump(data, fh, protocol=pickle.HIGHEST_PROTOCOL)
    print(f"{base} {part[0]}/{part[1]}: строк {len(f.envs)}, атомов {len(f.atoms)}, "
          f"{round(time.time() - t0)} с → {path}", file=sys.stderr)


# Частей таблицы на базу (по числу строк и цене строки).
# Подобрано по цене «строк × атомов» (замер 30.10: G 12 тыс. × 659, GN 148 тыс. × 1412,
# AB 89 тыс. × 1225, GHK 53 тыс. × 3494, GMN 24 тыс. × 3196, GHF 92 тыс. × 1301):
# части примерно равной цены, по 4 на машину при 20 машинах.
PARTS = {"G": 2, "GN": 24, "AB": 12, "GHK": 21, "GMN": 9, "GHF": 14, "Fam": 1, "GX": 1, "Gx": 3, "GE": 2}
COST = {"G": 8.0, "GN": 209.5, "AB": 108.8, "GHK": 185.0, "GMN": 76.7, "GHF": 119.8, "Fam": 0.01,
        "GX": 2.7, "Gx": 22.4, "GE": 14.8}


def assignment(jobs):
    """Части таблиц по машинам: самые дорогие — первыми, каждая — на наименее
    загруженную машину (одинаково на всех машинах: порядок детерминирован)."""
    tasks = [(b, (i, n)) for b, n in PARTS.items() for i in range(1, n + 1)]
    tasks.sort(key=lambda t: (-COST[t[0]] / PARTS[t[0]], t[0], t[1]))
    load = [0.0] * jobs
    out = [[] for _ in range(jobs)]
    for b, part in tasks:
        j = min(range(jobs), key=lambda x: (load[x], x))
        load[j] += COST[b] / PARTS[b]
        out[j].append((b, part))
    for o in out:  # одна база подряд: каркас строится один раз
        o.sort(key=lambda t: (list(PARTS).index(t[0]), t[1]))
    return out


def build_all(lib, vocab, job, jobs, outdir, threads):
    """Задание job из jobs: части таблиц job, job + jobs, … по threads процессов."""
    mine = assignment(jobs)[job - 1]
    ctx = mp.get_context("fork")
    running = []
    skel = {}
    for b, part in mine:
        while True:
            running = [p for p in running if p.exitcode is None]
            if len(running) < threads:
                break
            time.sleep(0.5)
        if b not in skel:  # каркас базы — один раз на машину
            t = time.time()
            skel[b] = skeleton(lib, vocab, b)
            print(f"{b}: каркас {round(time.time() - t)} с", file=sys.stderr, flush=True)
        p = ctx.Process(target=build, args=(lib, vocab, b, part, outdir, skel[b]))
        p.start()
        running.append(p)
    for p in running:
        p.join()


def load(lib, vocab, base, tdir):
    """Каркас базы со строками из всех частей таблицы."""
    f = skeleton(lib, vocab, base)
    parts = sorted(Path(tdir).glob(f"{base}.*-*.pickle"))
    if not parts:
        raise FileNotFoundError(f"нет таблицы {base} в {tdir}")
    n = int(parts[0].stem.split("-")[-1])
    if len(parts) != n:
        raise FileNotFoundError(f"{base}: частей {len(parts)} из {n}")
    mats = {k: [] for k in "mse"}
    f.envs, f.skipped = [], []
    width = 2 * len(f.atoms)
    for p in parts:
        with open(p, "rb") as fh:
            d = pickle.load(fh)
        if d["отпечаток"] != _fp(base) or d["атомов"] != len(f.atoms):
            raise ValueError(f"{p}: таблица от другого кода или данных")
        f.envs += d["envs"]
        f.skipped += d["skipped"]
        for k in "mse":
            mats[k].append(np.unpackbits(d[k], axis=1, count=width).astype(bool))
    f.m, f.s, f.e = (np.concatenate(mats[k]) for k in "mse")
    f.names = list(range(len(f.envs)))
    return f


def view(base_form, terms):
    """Схема-вид: столбцы таблицы для переменных базы и термов terms."""
    b = base_form
    g = b.g
    by_name = {str(t): t for t in b.own}
    elems = {t for t in b.own if isinstance(t, Var)} | {by_name[x] for x in terms}
    v = object.__new__(E.SchemeForm)
    v.g, v.lib, v.sc, v.search = g, b.lib, b.sc, b.search
    v._kept, v._derived, v._facts = {}, {}, b._facts
    v.envs, v.skipped, v.names = b.envs, b.skipped, b.names
    v.fixed_lits = b.fixed_lits
    v.own = [t for t in b.own if t in elems]
    v.atoms = [a for a in b.atoms if all(x in elems for x in a[2:] if not isinstance(x, (str, int)))]
    v.index = {a: i for i, a in enumerate(v.atoms)}
    v.req = {}
    for i, a in enumerate(v.atoms):
        need = {2 * v.index[("p", p, u)] for p, u in g.requires(a[2]) if ("p", p, u) in v.index}
        if need:
            v.req[i] = need
    v.fixed = [2 * v.index[a] + (0 if val else 1) for a, val in b.fixed_lits if a in v.index]
    cols = np.array([2 * b.index[a] + d for a in v.atoms for d in (0, 1)], dtype=np.int64)
    v.m, v.s, v.e = b.m[:, cols], b.s[:, cols], b.e[:, cols]
    top = maximal(g, elems)
    v.need = [{i for i, a in enumerate(v.atoms) if t in a[2:]} for t in top]
    sw = SWAP.get(_STATE.get("base_of", {}).get(id(b)))
    if sw:  # парные атомы «P(A) и P(B)» для симметричных переменных базы
        vs = {str(t): t for t in v.own if isinstance(t, Var)}
        if sw[0] in vs and sw[1] in vs:
            v.pairs = [(vs[sw[0]], vs[sw[1]])]
    gb = _STATE.get("forms", {}).get("G") or _STATE.get("generic")
    if gb is not None:
        GV = next(t for t in gb.own if isinstance(t, Var))
        v.generic = (gb.e, {a[1]: i for i, a in enumerate(gb.atoms) if a[0] == "p" and a[2] == GV})
    return v


# --- перебор схем из таблиц ---------------------------------------------------

_STATE = {}


def k_for(ks, n_top):
    """Посылок для схемы с n_top верхними термами: ks = [k при 0 термов, при 1, …];
    последнее значение — для всех больших."""
    return ks[min(n_top, len(ks) - 1)]


class SchemeTimeout(Exception):
    pass


def _alarm(signum, frame):
    raise SchemeTimeout()


def _one(job):
    base, sid, terms, k, outdir, fp = job
    out, err = io.StringIO(), io.StringIO()
    t0 = time.time()
    limit = _STATE.get("limit") or 0
    if limit:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(int(limit))
    try:
        form = view(_STATE["forms"][base], terms)
        form, alive, empty, report = E.run(k, _STATE["lib"], _STATE["vocab"], form)
        summary = E.render(form, alive, empty, report, out=out, err=err, registry=_STATE["registry"])
        status = "ok"
    except SchemeTimeout:
        summary, status = {}, f"таймаут {limit} с"
    except Exception:
        summary, status = {}, "ошибка"
        err.write(traceback.format_exc())
    finally:
        if limit:
            signal.alarm(0)
    rec = {"id": sid, "условие": BASES[base], "термы": terms, "посылок": k, "без": sorted(E.SKIP),
           "отпечаток": fp, "секунд": round(time.time() - t0, 1), "статус": status, **summary}
    p = Path(outdir) / sid
    p.with_suffix(".txt").write_text(err.getvalue() + "\n" + out.getvalue(), encoding="utf-8")
    p.with_suffix(".json").write_text(json.dumps(rec, ensure_ascii=False, indent=1), encoding="utf-8")


def run_schemes(a):
    vocab = Vocab.section("grp")
    lib = built_library(vocab)
    E.DEFER = getattr(a, "defer", 0) or 0
    _STATE.update(lib=lib, vocab=vocab, registry=E.load_registry(), forms={})
    outdir = Path(a.out)
    outdir.mkdir(parents=True, exist_ok=True)
    jobs = []
    ks = [int(x) for x in str(a.k).split(",")]
    try:  # таблица базы G — для фильтра условий об одном терме (generic_filter)
        _STATE["generic"] = load(lib, vocab, "G", a.dir)
    except (FileNotFoundError, ValueError) as e:
        print(f"нет таблицы G для фильтра: {e}", file=sys.stderr)
    for base in a.bases.split(","):
        fp = _fp(base) + f":{a.k}" + (f":d{a.defer}" if a.defer else "")
        todo = schemes(vocab, base, ks[-1])
        g0, _, _ = scheme(vocab, {"раздел": "grp", "условие": BASES[base]})
        n0 = {str(t): t for t in g0.terms}
        tops = {}
        for sid, terms in todo:
            ts = [term(g0, x, n0, "grp") for x in terms]
            tops[sid] = sum(1 for t in maximal(g0, closure(g0, ts + [t for t in g0.terms if isinstance(t, Var)]))
                            if isinstance(t, App))
        if a.part:
            i, n = map(int, a.part.split("/"))
            todo = todo[i - 1::n]
        for sid, terms in todo:
            j = outdir / f"{sid}.json"
            if j.exists() and not a.force:
                try:
                    old = json.loads(j.read_text(encoding="utf-8"))
                    if old.get("отпечаток") == fp and old.get("статус") == "ok":
                        continue
                except Exception:
                    pass
            jobs.append((base, sid, terms, k_for(ks, tops[sid]), str(outdir), fp))
        if any(j[0] == base for j in jobs) or (base == "G" and a.bases != "G"):
            t = time.time()
            _STATE["forms"][base] = load(lib, vocab, base, a.dir)
            _STATE.setdefault("base_of", {})[id(_STATE["forms"][base])] = base
            print(f"{base}: таблица {_STATE['forms'][base].e.shape}, {round(time.time() - t)} с",
                  file=sys.stderr, flush=True)
    print(f"схем к перебору {len(jobs)}, нитей {a.jobs}", file=sys.stderr, flush=True)
    t0 = time.time()
    ctx = mp.get_context("fork")  # таблицы наследуются без копирования
    limit = int(a.mem * 2**30) if a.mem else 0

    def worker(chunk):
        if limit:
            import resource
            vm = 0
            with open("/proc/self/status") as fh:
                for line in fh:
                    if line.startswith("VmSize:"):
                        vm = int(line.split()[1]) * 1024
            resource.setrlimit(resource.RLIMIT_AS, (vm + limit, vm + limit))
        for job in chunk:
            if _STATE.get("deadline") and time.time() > _STATE["deadline"]:
                break  # срок вышел: схемы пачки после него не начинаем
            try:
                _one(job)
            except MemoryError:
                p = Path(job[4]) / job[1]
                p.with_suffix(".json").write_text(json.dumps(
                    {"id": job[1], "условие": BASES[job[0]], "термы": job[2], "отпечаток": job[5],
                     "статус": "ошибка: память"}, ensure_ascii=False), encoding="utf-8")
        os._exit(0)

    # Дочерний процесс берёт пачку схем (форк на каждую схему дорог при тысячах схем).
    size = max(1, min(50, len(jobs) // (a.jobs * 4) or 1))
    queue = [jobs[i:i + size] for i in range(0, len(jobs), size)]
    running, done = {}, 0
    _STATE["limit"] = a.limit
    deadline = t0 + a.until * 60 if a.until else None
    _STATE["deadline"] = deadline  # видят и дочерние процессы (fork)
    while queue or running:
        if deadline and time.time() > deadline and queue:
            print(f"срок вышел: не начато схем {sum(len(c) for c in queue)}", file=sys.stderr, flush=True)
            queue = []
        while queue and len(running) < a.jobs:
            chunk = queue.pop(0)
            p = ctx.Process(target=worker, args=(chunk,))
            p.start()
            running[p] = chunk
        for p in list(running):
            if p.exitcode is None:
                continue
            chunk = running.pop(p)
            done += len(chunk)
            if p.exitcode != 0:
                for job in chunk:
                    j = Path(job[4]) / f"{job[1]}.json"
                    if not j.exists():
                        j.write_text(json.dumps({"id": job[1], "условие": BASES[job[0]], "термы": job[2],
                                                 "отпечаток": job[5], "статус": f"ошибка: код {p.exitcode}"},
                                                ensure_ascii=False), encoding="utf-8")
            print(f"[{done}/{len(jobs)}] {round(time.time() - t0)} с", file=sys.stderr, flush=True)
        time.sleep(0.2)
    print(f"готово за {round(time.time() - t0)} с", file=sys.stderr)


def completeness(lib, vocab, base, tdir, top=15):
    """Полнота библиотеки по термам вселенной: доля известных значений атомов
    терма по строкам, где терм существует, и группы с наибольшим числом
    неизвестных значений (что вписать в библиотеку в первую очередь)."""
    from collections import Counter
    f = load(lib, vocab, base, tdir)
    known = f.e[:, 0::2] | f.e[:, 1::2]
    out = []
    for t in f.own:
        idx = [i for i, a in enumerate(f.atoms) if a[0] == "p" and a[2] == t]
        if not idx:
            continue
        rows = np.array([f.search._image(t, env) is not None or isinstance(t, Var) for env in f.envs])
        k = known[:, idx]
        miss = Counter()
        for r in np.flatnonzero((~k).any(axis=1)):
            env = f.envs[r]
            g = next(iter(env.values()))
            miss[lib.obj[g[1]].get("имя", g[1])] += int((~k[r]).sum())
        out.append((str(t), float(k.mean()), float(rows.mean()), miss.most_common(top)))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("вселенная", "схемы"):
        s = sub.add_parser(name)
        s.add_argument("base")
        s.add_argument("--посылок", dest="k", type=int, default=2)
    s = sub.add_parser("строить")
    s.add_argument("base")
    s.add_argument("--часть", dest="part", default="1/1")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("строить-все")
    s.add_argument("--задание", dest="job", required=True, help="j/N")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--нитей", dest="jobs", type=int, default=mp.cpu_count())
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("полнота")
    s.add_argument("base")
    s.add_argument("--каталог", dest="dir", required=True)
    s.add_argument("--без", dest="skip", default="")
    s = sub.add_parser("перебор")
    s.add_argument("bases", help="базы через запятую")
    s.add_argument("--каталог", dest="dir", required=True, help="где таблицы")
    s.add_argument("--выход", dest="out", required=True)
    s.add_argument("--часть", dest="part")
    s.add_argument("--нитей", dest="jobs", type=int, default=mp.cpu_count())
    s.add_argument("--посылок", dest="k", default="2",
                   help="k или список «k0,k1,k2»: посылок для схем с 0, 1, ⩾ 2 верхними термами")
    s.add_argument("--без", dest="skip", default="")
    s.add_argument("--заново", dest="force", action="store_true")
    s.add_argument("--память", dest="mem", type=float, default=0)
    s.add_argument("--отложить", dest="defer", type=float, default=0,
                   help="откладывать атомы, известные меньше чем в этой доле строк (например 0.15)")
    s.add_argument("--до", dest="until", type=float, default=0, help="минут: после этого новые схемы не начинать")
    s.add_argument("--предел", dest="limit", type=float, default=0, help="секунд на одну схему")
    a = ap.parse_args()
    E.SKIP.update(x.strip() for x in getattr(a, "skip", "").split(",") if x.strip())
    vocab = Vocab.section("grp")
    if a.cmd == "вселенная":
        for i, x in enumerate(universe(vocab, a.base)):
            print(i + 1, x)
    elif a.cmd == "схемы":
        ss = schemes(vocab, a.base, a.k)
        for sid, ts in ss:
            print(f"{sid} | {BASES[a.base]} | {'; '.join(ts)}")
        print(f"# схем {len(ss)}", file=sys.stderr)
    elif a.cmd == "строить":
        i, n = map(int, a.part.split("/"))
        build(built_library(vocab), vocab, a.base, (i, n), a.dir)
    elif a.cmd == "полнота":
        for t, k, im, miss in completeness(built_library(vocab), vocab, a.base, a.dir):
            print(f"{t:36s} известно {k:.0%}, образ в библиотеке {im:.0%}")
            print("    больше всего неизвестных: " + "; ".join(f"{g} {n}" for g, n in miss[:8]))
    elif a.cmd == "строить-все":
        j, n = map(int, a.job.split("/"))
        build_all(built_library(vocab), vocab, j, n, a.dir, a.jobs)
    else:
        run_schemes(a)


if __name__ == "__main__":
    main()
