"""Генератор от знаний: вид неизвестного условия и корни недостающих знаний (ALGEN_KNOWLEDGE=1).

Неизвестное условие — запрет F: посылки, отрицание цели и закреплённые литералы формы. По строкам
таблицы (записанные группы и построенные произведения):
  R — есть строка, где верны все литералы F: условие опровергнуто (у неизвестного быть не должно);
  A — есть строка без ложных литералов F, где неизвестен ровно один: его значение решает условие
      (верно — строка опровергает условие, ложно — строка выбывает);
  B — таких строк нет, но есть строки без ложных литералов с ⩾ 2 неизвестными;
  C — в каждой строке какой-то литерал F ложен: данных хватает, условие верно на всех примерах —
      вопрос человеку (правило, новая группа или открытый вопрос).
Положительный парный литерал «P(A) и P(B)» раскладывается на два литерала, повторы схлопываются
(как в value_classify.py, GPT 15.11: виды совпадают с его C++-классификатором — тест). Отрицание
парного литерала в запрете не бывает (цель не парная, в посылках только столбец 0): если встретится,
вид «ОШИБКА», как и у противоречивого запрета.

Корень знания — (шаблон атома, объект строки). Объект — ключ записанной группы библиотеки (у
подгруппы — «ключ/номер»), у построенного произведения «×»: одна задача-правило на шаблон для всех
произведений. Корни условия A — неизвестные клетки строк с одним неизвестным, B — строк с ⩾ 2.
Заполнить все корни — условие опровергнуто или стало C; доказательства это не даёт: C остаются
вопросами (их решает теория или человек).

Поля только добавляются: у неизвестных строк отчёта «вид», «строк», «корней», «корни» (первые
ROW_ROOTS по частоте в схеме); сводка схемы — «знания»; полные корни — form.knowledge["корни"]
(table.py пишет их в <схема>.knowledge.json.gz для сжатия между схемами). Без флага выдача прежняя.
"""
import heapq
from collections import Counter

import numpy as np

ROW_ROOTS = 30     # корней в строке отчёта (полный счёт — в «корней» и в сводке)
QUEUE = 100        # корней в очереди знаний сводки
C_LIST = 500       # условий C в списке сводки (полное число — в «вопросов человеку (C)»)
PRODUCT = "×"
LABELS = ("все неизвестные", "оставленные после сжатия")


def _popcount(bits):
    return int(np.bitwise_count(bits).sum())


class Knowledge:
    """Разметка неизвестных условий одной формы (таблица m: строки × столбцы-литералы)."""

    def __init__(self, form):
        from .enumerate import atom_name, term_vars
        self.form = form
        _, self.P, self.valid = form._bits(form.m)
        self.nrows = form.m.shape[0]
        self.atoms = list(form.atoms)
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.fixed = [int(c) for c in getattr(form, "fixed", []) or []]
        self.pattern = [atom_name(a) for a in self.atoms]
        # переменные атома: объект строки — образы этих переменных
        self.avars = []
        for a in self.atoms:
            if a[0] == "pair":
                a = ("p", a[1], a[2])
            vs = set()
            for x in a[2:]:
                if not isinstance(x, (str, int, bool, float)):
                    try:
                        vs |= term_vars(x)
                    except AttributeError:
                        pass
            self.avars.append(tuple(sorted(vs, key=str)))
        allvars = sorted(set().union(*map(set, self.avars)) if self.avars else set(), key=str)
        self.codes, self.names = {}, {}
        for v in allvars:
            objs = [self._object(r, v) for r in range(self.nrows)]
            names = sorted(set(objs))
            pos = {o: i for i, o in enumerate(names)}
            self.codes[v] = np.array([pos[o] for o in objs], dtype=np.int64)
            self.names[v] = names
        self._combined = {}
        radix = 1
        for v in allvars:
            radix *= len(self.names[v]) + 1
        self.radix = max(1, radix)

    def _object(self, r, v):
        """Объект строки r для переменной v: ключ записанной группы, «ключ/номер» подгруппы,
        «×» у построенного произведения; у строк без образа — «#номер строки»."""
        f = self.form
        try:
            im = f._image(r, v)
        except (IndexError, KeyError, AttributeError):
            im = None
        if im is None:
            return f"#{r}"
        lib = getattr(f, "lib", None)
        if im[0] in ("obj", "sub"):
            rec = lib.obj.get(im[1], {}) if lib is not None else {}
            if rec.get("синтез") or PRODUCT in str(im[1]):
                return PRODUCT
            return im[1] if im[0] == "obj" else f"{im[1]}/{im[2]}"
        return str(im[:2])

    def _objcode(self, vs):
        """Код объекта строки для набора переменных (смешанное основание), по всем строкам."""
        hit = self._combined.get(vs)
        if hit is None:
            hit = np.zeros(self.nrows, dtype=np.int64)
            for v in vs:
                hit = hit * (len(self.names[v]) + 1) + self.codes[v]
            self._combined[vs] = hit
        return hit

    def root_name(self, rid):
        """(шаблон, объект) по номеру корня."""
        atom, code = divmod(int(rid), self.radix)
        vs = self.avars[atom]
        parts = []
        for v in reversed(vs):
            code, c = divmod(code, len(self.names[v]) + 1)
            parts.append(self.names[v][c])
        return self.pattern[atom], ", ".join(reversed(parts))

    def expand(self, cols):
        """Литералы запрета: столбцы условия + закреплённые, парные — по составляющим."""
        out = set()
        for c in list(cols) + self.fixed:
            c = int(c)
            a = self.atoms[c // 2]
            if a[0] == "pair":
                if c % 2:
                    raise ValueError("отрицание парного литерала в запрете")
                _, p, x, y, pol = a
                for t in (x, y):
                    out.add(2 * self.index[("p", p, t)] + (0 if pol else 1))
            else:
                out.add(c)
        if any(c ^ 1 in out for c in out):
            raise ValueError("противоречивый запрет")
        return sorted(out)

    def classify(self, cols):
        """(вид, строк с одним неизвестным, с ⩾ 2, опровергающих, номера корней)."""
        try:
            lits = self.expand(cols)
        except (ValueError, KeyError) as e:
            return f"ОШИБКА: {e}", 0, 0, 0, np.empty(0, dtype=np.int64)
        P = self.P
        ok = self.valid.copy()
        one, two = np.zeros_like(ok), np.zeros_like(ok)
        unk = {}
        for c in lits:
            ok &= ~P[c ^ 1]  # ни один литерал не ложен
        for c in lits:
            u = ok & ~P[c] & ~P[c ^ 1]
            unk[c] = u
            two |= one & u
            one |= u
        alltrue, single, multi = ok & ~one, one & ~two, two
        n1, n2, n0 = _popcount(single), _popcount(multi), _popcount(alltrue)
        kind = "R" if n0 else "A" if n1 else "B" if n2 else "C"
        if kind not in ("A", "B"):
            return kind, n1, n2, n0, np.empty(0, dtype=np.int64)
        rows_mask = single if kind == "A" else multi
        ids = []
        for c in lits:
            m = unk[c] & rows_mask
            if not m.any():
                continue
            rows = np.flatnonzero(np.unpackbits(m.view(np.uint8), bitorder="little")[:self.nrows])
            atom = c // 2
            codes = np.unique(self._objcode(self.avars[atom])[rows])
            ids.append(atom * self.radix + codes)
        roots = np.unique(np.concatenate(ids)) if ids else np.empty(0, dtype=np.int64)
        return kind, n1, n2, n0, roots


def hitting(sets):
    """Жадное покрытие (ленивая куча) по спискам номеров корней: сколько корней, чтобы у каждого
    непустого набора был хотя бы один выбранный. Память — массивы numpy, не множества Python."""
    sets = [np.asarray(s, dtype=np.int64) for s in sets]
    sizes = np.array([len(s) for s in sets], dtype=np.int64)
    if not sizes.sum():
        return 0
    flat = np.concatenate([s for s in sets if len(s)])
    owner = np.repeat(np.arange(len(sets)), sizes)
    uniq, dense = np.unique(flat, return_inverse=True)
    order = np.argsort(dense, kind="stable")
    members = owner[order]
    ptr = np.zeros(len(uniq) + 1, dtype=np.int64)
    np.cumsum(np.bincount(dense, minlength=len(uniq)), out=ptr[1:])
    alive = sizes > 0
    left = int(alive.sum())
    heap = [(-int(ptr[v + 1] - ptr[v]), v) for v in range(len(uniq))]
    heapq.heapify(heap)
    picked = 0
    while left and heap:
        neg, v = heapq.heappop(heap)
        ms = members[ptr[v]:ptr[v + 1]]
        cur = int(alive[ms].sum())
        if cur == 0:
            continue
        if cur < -neg:
            heapq.heappush(heap, (-cur, v))
            continue
        alive[ms] = False
        left -= cur
        picked += 1
    return picked


def _aggregate(kn, rows, roots_of):
    kinds, roots, sets = Counter(), Counter(), []
    for r in rows:
        kinds[r["вид"]] += 1
        ids = roots_of.get(id(r))
        if ids is not None and len(ids):
            sets.append(ids)
            roots.update(ids.tolist())
    named = [(kn.root_name(rid), n) for rid, n in roots.items()]
    product = sum(1 for (_p, o), _n in named if PRODUCT in o.split(", "))
    out = {"условий": len(rows), "разобрано": len(rows), "по видам": dict(sorted(kinds.items())),
           "вопросов человеку (C)": kinds.get("C", 0),
           "ждут знаний (A + B)": kinds.get("A", 0) + kinds.get("B", 0),
           "корней знаний всего": len(roots),
           "из них значений записанных групп": len(roots) - product,
           "из них правил для произведений (шаблон × «×»)": product,
           "шаблонов атомов": len({p for (p, _o), _n in named}),
           "корней, чтобы затронуть все условия A/B (жадно)": hitting(sets)}
    named.sort(key=lambda x: (-x[1], x[0]))
    return out, named


def annotate(form, report):
    """Размечает неизвестные строки отчёта (у них «_cols») и возвращает
    {"сводка": …, "корни": {метка: [[шаблон, объект, условий], …]}}."""
    kn = Knowledge(form)
    unknown = [r for r in report if r.get("вердикт") == "неизвестно" and "_cols" in r]
    roots_of, freq = {}, Counter()
    memo = {}  # контрапозиции запрета — тот же набор литералов
    for r in unknown:
        key = tuple(sorted(r["_cols"]))
        hit = memo.get(key)
        if hit is None:
            hit = memo[key] = kn.classify(key)
        kind, n1, n2, n0, ids = hit
        r["вид"] = kind
        r["строк"] = {"с одним неизвестным": n1, "с несколькими": n2, **({"опровергают": n0} if n0 else {})}
        r["корней"] = int(len(ids))
        roots_of[id(r)] = ids
        freq.update(ids.tolist())
    for r in unknown:
        ids = roots_of[id(r)]
        top = sorted(ids.tolist(), key=lambda x: (-freq[x], x))[:ROW_ROOTS]
        r["корни"] = [" у ".join(kn.root_name(x)) for x in top]
    kept = [r for r in unknown if not r.get("свёрнута")]
    summary, full = {}, {}
    for label, rows in zip(LABELS, (unknown, kept)):
        summary[label], named = _aggregate(kn, rows, roots_of)
        full[label] = [[p, o, n] for (p, o), n in named]
        summary[label]["топ корней"] = [[f"{p} у {o}", n] for (p, o), n in named[:30]]
    summary["очередь знаний"] = [
        {"корень": f"{p} у {o}", "условий": n,
         "что": "правило для произведений" if PRODUCT in o.split(", ") else "значение записанной группы"}
        for p, o, n in full[LABELS[1]][:QUEUE]]
    cs = [r for r in kept if r["вид"] == "C"]
    summary["вопросы человеку"] = [{"№": r.get("№"), "запрет": " & ".join(r.get("запрет", [])),
                                    "примеров": r.get("примеров")} for r in cs[:C_LIST]]
    errors = Counter(r["вид"] for r in unknown if r["вид"].startswith("ОШИБКА") or r["вид"] == "R")
    if errors:
        summary["ошибки разметки"] = dict(errors)
    return {"сводка": summary, "корни": full}


def text(summary, top=20):
    """Строки для текстовой выдачи схемы."""
    kept = summary[LABELS[1]]
    lines = [f"== знания: оставлено неизвестных {kept['условий']} — вопросов человеку (C) "
             f"{kept['вопросов человеку (C)']}, ждут знаний {kept['ждут знаний (A + B)']}: корней "
             f"{kept['корней знаний всего']} (значений групп {kept['из них значений записанных групп']}, "
             f"правил для произведений {kept['из них правил для произведений (шаблон × «×»)']}), "
             f"жадно {kept['корней, чтобы затронуть все условия A/B (жадно)']} затрагивают все =="]
    for q in summary["очередь знаний"][:top]:
        lines.append(f"знание {q['корень']} — условий {q['условий']} ({q['что']})")
    for q in summary["вопросы человеку"][:top]:
        num = f" №{q['№']}" if q["№"] is not None else ""
        lines.append(f"вопрос{num}: {q['запрет']}   [примеров посылок: {q['примеров']}]")
    return lines
