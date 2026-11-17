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

Корень знания — (шаблон атома, объект строки). Объект — образы переменных атома в строке: ключ
записанной группы, «ключ/номер» подгруппы, полный образ элемента, морфизма, действия, числа; у
построенного произведения (и всего, что из него взято) «×»: одна задача-правило на шаблон для всех
произведений; у строки без образа (живая строка) — «#номер». Корни условия A — неизвестные клетки
строк с одним неизвестным, B — строк с ⩾ 2 неизвестными. Заполнив корень A значением «верно»,
получаем опровержение; «ложно» — строка выбывает, и условие может стать B или C. Заполнив все
неизвестные клетки строк без ложных литералов, получаем опровержение или C. Доказательства это не
даёт: C остаются вопросами (их решает теория или человек).

Счёт — по запретам: контрапозиции одного запрета (тот же набор литералов) размечаются один раз,
единица счёта — «№» сжатия (класс запрета), без сжатия — «класс»; число строк отчёта — отдельно.
Поля только добавляются: у неизвестных строк отчёта «вид», «строк», «корней», «корни» (первые
ROW_ROOTS по частоте в схеме); сводка схемы — «знания»; полные корни — form.knowledge["корни"]
(table.py пишет их в <схема>.knowledge.json.gz для сжатия между схемами). Без флага выдача прежняя.
"""
import heapq
from collections import Counter

import numpy as np

ROW_ROOTS = 30          # корней в строке отчёта (полный счёт — в «корней» и в сводке)
QUEUE = 100             # корней в очереди знаний сводки
C_LIST = 500            # вопросов C в списке сводки (полное число — в «вопросов человеку (C)»)
HITTING_MAX = 3_000_000  # пар (запрет, корень) для жадного покрытия; больше — покрытие не считается
FULL_MAX = 500_000      # корней в полном списке «все неизвестные» (оставленные — всегда целиком)
PRODUCT = "×"
LABELS = ("все неизвестные", "оставленные после сжатия")


def _popcount(bits):
    return int(np.bitwise_count(bits).sum())


def _vars_in_order(t, out):
    """Переменные терма в порядке появления (а не по имени)."""
    from .logic import Var
    if isinstance(t, Var):
        if t not in out:
            out.append(t)
    elif hasattr(t, "args"):
        for a in t.args:
            _vars_in_order(a, out)
    return out


class Knowledge:
    """Разметка неизвестных условий одной формы (таблица m: строки × столбцы-литералы)."""

    def __init__(self, form):
        from .enumerate import atom_name
        self.form = form
        _, self.P, self.valid = form._bits(form.m)
        self.nrows = form.m.shape[0]
        self.atoms = list(form.atoms)
        self.index = {a: i for i, a in enumerate(self.atoms)}
        self.fixed = [int(c) for c in getattr(form, "fixed", []) or []]
        self.pattern = [atom_name(a) for a in self.atoms]
        lib = getattr(form, "lib", None)
        self._synth = {k for k, rec in lib.obj.items() if rec.get("синтез")} if lib is not None else set()
        # переменные атома (в порядке аргументов): объект строки — их образы
        self.avars = []
        for a in self.atoms:
            if a[0] == "pair":
                a = ("p", a[1], a[2])
            vs = []
            for x in a[2:]:
                if not isinstance(x, (str, int, bool, float)):
                    _vars_in_order(x, vs)
            self.avars.append(tuple(vs))
        self.codes, self.names = {}, {}
        for v in {v for vs in self.avars for v in vs}:
            objs = [self._object(r, v) for r in range(self.nrows)]
            names = sorted(set(objs))
            pos = {o: i for i, o in enumerate(names)}
            self.codes[v] = np.array([pos[o] for o in objs], dtype=np.int64)
            self.names[v] = names
        # объект набора переменных — плотный код (различных объектов не больше строк): номер
        # корня = атом · D + код, без переполнения при любом числе переменных и объектов
        self.D = self.nrows + 1
        self._dense = {}
        self._name = {}  # только для корней, которые выписываются (не для всех)

    def _object(self, r, v):
        f = self.form
        try:
            im = f._image(r, v)
        except (IndexError, KeyError, AttributeError):
            im = None
        if im is None:
            return f"#{r}"

        def synth(x):
            if isinstance(x, (tuple, list)):
                return any(synth(y) for y in x)
            return isinstance(x, str) and (x in self._synth or PRODUCT in x)
        if im[0] in ("obj", "sub"):
            if synth(im[1]):
                return PRODUCT
            return im[1] if im[0] == "obj" else f"{im[1]}/{im[2]}"
        # элемент, морфизм, действие, число…: полный образ (у построенных — «×»)
        return PRODUCT if synth(im[1:]) else repr(im)

    def _objcode(self, vs):
        """(плотный код объекта по строкам, имена объектов) для набора переменных."""
        hit = self._dense.get(vs)
        if hit is None:
            if not vs:
                hit = (np.zeros(self.nrows, dtype=np.int64), ["—"])
            else:
                stack = np.stack([self.codes[v] for v in vs], axis=1)
                uniq, inv = np.unique(stack, axis=0, return_inverse=True)
                names = [", ".join(self.names[v][c] for v, c in zip(vs, row)) for row in uniq.tolist()]
                hit = (inv.reshape(-1).astype(np.int64), names)
            self._dense[vs] = hit
        return hit

    def product_flags(self, vs):
        """Для плотных кодов объектов набора переменных: объект — построенное произведение («×»)."""
        names = self._objcode(vs)[1]
        return np.fromiter((PRODUCT in n.split(", ") for n in names), dtype=bool, count=len(names))

    def root_name(self, rid):
        """(шаблон, объект) по номеру корня."""
        rid = int(rid)
        hit = self._name.get(rid)
        if hit is None:
            atom, code = divmod(rid, self.D)
            hit = self._name[rid] = (self.pattern[atom], self._objcode(self.avars[atom])[1][code])
        return hit

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
        """(вид, строк с одним неизвестным, с ⩾ 2, опровергающих, номера корней по возрастанию)."""
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
            code, names = self._objcode(self.avars[atom])
            seen = np.zeros(len(names), dtype=bool)
            seen[code[rows]] = True
            ids.append(atom * self.D + np.flatnonzero(seen))
        roots = np.unique(np.concatenate(ids)) if ids else np.empty(0, dtype=np.int64)
        return kind, n1, n2, n0, roots


def _hitting_csr(owner, dense, nsets, nroots):
    """Жадное покрытие (ленивая куча): пары (набор, корень) без повторов → сколько корней, чтобы у
    каждого непустого набора был хотя бы один выбранный."""
    if not len(dense):
        return 0
    order = np.argsort(dense, kind="stable")
    members = owner[order]
    ptr = np.zeros(nroots + 1, dtype=np.int64)
    np.cumsum(np.bincount(dense, minlength=nroots), out=ptr[1:])
    alive = np.zeros(nsets, dtype=bool)
    alive[owner] = True
    left = int(alive.sum())
    heap = [(-int(ptr[v + 1] - ptr[v]), v) for v in range(nroots) if ptr[v + 1] > ptr[v]]
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


def hitting(sets):
    """Жадное покрытие по спискам номеров корней (повторы внутри набора не в счёт)."""
    sets = [np.unique(np.asarray(s, dtype=np.int64)) for s in sets]
    sizes = np.array([len(s) for s in sets], dtype=np.int64)
    if not sizes.sum():
        return 0
    uniq, dense = np.unique(np.concatenate([s for s in sets if len(s)]), return_inverse=True)
    owner = np.repeat(np.arange(len(sets)), sizes)
    return _hitting_csr(owner, dense.reshape(-1), len(sets), len(uniq))


def _unit(r):
    """Единица счёта — запрет: «№» сжатия (класс), без сжатия — «класс» (или набор литералов)."""
    if "№" in r:
        return ("№", r["№"])
    k = r.get("класс")
    if k is None:
        return ("литералы", tuple(sorted(r["_cols"])))
    return ("класс", tuple(map(tuple, k)) if k and isinstance(k[0], list) else tuple(k) if isinstance(k, list) else k)


def annotate(form, report):
    """Размечает неизвестные строки отчёта (у них «_cols») и возвращает
    {"сводка": …, "корни": {метка: [[шаблон, объект, запретов], …]}}."""
    kn = Knowledge(form)
    unknown = [r for r in report if r.get("вердикт") == "неизвестно" and "_cols" in r]
    # 1. разметка по различным наборам литералов (контрапозиции запрета — один набор)
    key_index, results, row_key = {}, [], np.empty(len(unknown), dtype=np.int64)
    for i, r in enumerate(unknown):
        k = tuple(sorted(r["_cols"]))
        j = key_index.get(k)
        if j is None:
            j = key_index[k] = len(results)
            results.append(list(kn.classify(k)))
        row_key[i] = j
    nkeys = len(results)
    # 2. запреты (единицы счёта) и их представители; вес набора — число запретов с ним
    reps = {LABELS[0]: {}, LABELS[1]: {}}
    for i, r in enumerate(unknown):
        u = _unit(r)
        reps[LABELS[0]].setdefault(u, i)
        if not r.get("свёрнута"):
            reps[LABELS[1]].setdefault(u, i)
    weight = {}
    for label, rp in reps.items():
        w = np.zeros(nkeys, dtype=np.int64)
        if rp:
            np.add.at(w, row_key[list(rp.values())], 1)
        weight[label] = w
    # 3. плотные номера корней: один np.unique по всем наборам
    sizes = np.fromiter((len(x[4]) for x in results), dtype=np.int64, count=nkeys)
    ptr = np.zeros(nkeys + 1, dtype=np.int64)
    np.cumsum(sizes, out=ptr[1:])
    if ptr[-1]:
        cat = np.concatenate([x[4] for x in results if len(x[4])])
        for x in results:  # память: номера корней дальше только плотные
            x[4] = None
        uniq, dense = np.unique(cat, return_inverse=True)
        del cat
        dense = dense.reshape(-1).astype(np.int32 if len(uniq) < 2 ** 31 else np.int64)
    else:
        uniq, dense = np.empty(0, dtype=np.int64), np.empty(0, dtype=np.int32)
    owner = np.repeat(np.arange(nkeys, dtype=np.int32 if nkeys < 2 ** 31 else np.int64), sizes)
    freq = {label: np.bincount(dense, weights=weight[label][owner], minlength=len(uniq)).astype(np.int64)
            for label in LABELS}
    # 4. поля строк: «корни» — первые ROW_ROOTS по частоте среди всех неизвестных (затем по номеру)
    score = freq[LABELS[0]] * (len(uniq) + 1) - np.arange(len(uniq))
    tops = []
    for j in range(nkeys):
        d = dense[ptr[j]:ptr[j + 1]]
        if len(d) > ROW_ROOTS:
            d = d[np.argpartition(-score[d], ROW_ROOTS - 1)[:ROW_ROOTS]]
        d = d[np.argsort(-score[d], kind="stable")]
        tops.append([" у ".join(kn.root_name(uniq[x])) for x in d])
    for i, r in enumerate(unknown):
        kind, n1, n2, n0, _ = results[row_key[i]]
        r["вид"] = kind
        r["строк"] = {"с одним неизвестным": n1, "с несколькими": n2, **({"опровергают": n0} if n0 else {})}
        r["корней"] = int(sizes[row_key[i]])
        r["корни"] = tops[row_key[i]]
    # 5. сводка по меткам
    summary, full = {}, {}
    # корень — правило для произведений, если объект «×» (векторно, без имён всех корней)
    is_product = np.zeros(len(uniq), dtype=bool)
    atom_of, code_of = np.divmod(uniq, kn.D)
    by_vs = {}
    for a in np.unique(atom_of).tolist():
        by_vs.setdefault(kn.avars[a], []).append(a)
    for vs, atoms in by_vs.items():
        m = np.isin(atom_of, atoms)
        is_product[m] = kn.product_flags(vs)[code_of[m]]
    for label in LABELS:
        rp, f = reps[label], freq[label]
        rows = len(unknown) if label == LABELS[0] else sum(1 for r in unknown if not r.get("свёрнута"))
        kinds = Counter(results[row_key[i]][0] for i in rp.values())
        nz = np.flatnonzero(f)
        prod = int(is_product[nz].sum())
        keys = np.flatnonzero(weight[label] > 0)
        pairs = int(sizes[keys].sum())
        if pairs <= HITTING_MAX:
            sel = np.repeat(np.isin(np.arange(nkeys), keys), sizes)
            greedy = _hitting_csr(owner[sel], dense[sel], nkeys, len(uniq))
        else:
            greedy = None
        out = {"строк": rows, "запретов": len(rp), "по видам": dict(sorted(kinds.items())),
               "вопросов человеку (C)": kinds.get("C", 0),
               "ждут знаний (A + B)": kinds.get("A", 0) + kinds.get("B", 0),
               "корней знаний всего": int(len(nz)),
               "из них значений записанных групп": int(len(nz)) - prod,
               "из них правил для произведений (шаблон × «×»)": prod,
               "шаблонов атомов": int(len(np.unique(atom_of[nz]))),
               "корней, чтобы затронуть все условия A/B (жадно)": greedy}
        if greedy is None:
            out["покрытие не считалось"] = f"пар (запрет, корень) {pairs} > {HITTING_MAX}"
        order = nz[np.argsort(-(f[nz] * (len(uniq) + 1) - nz), kind="stable")] if len(nz) else nz
        out["топ корней"] = [[" у ".join(kn.root_name(uniq[x])), int(f[x])] for x in order[:30]]
        cut = order if label == LABELS[1] else order[:FULL_MAX]
        full[label] = [[*kn.root_name(uniq[x]), int(f[x])] for x in cut]
        if len(cut) < len(order):
            out["полный список корней обрезан"] = f"{len(cut)} из {len(order)}"
        summary[label] = out
    summary["очередь знаний"] = [
        {"корень": f"{p} у {o}", "запретов": n,
         "что": "правило для произведений" if PRODUCT in o.split(", ") else "значение записанной группы"}
        for p, o, n in full[LABELS[1]][:QUEUE]]
    cs = [unknown[i] for i in reps[LABELS[1]].values() if results[row_key[i]][0] == "C"]
    summary["вопросы человеку"] = [{"№": r.get("№"), "запрет": " & ".join(r.get("запрет", [])),
                                    "примеров": r.get("примеров")} for r in cs[:C_LIST]]
    errors = Counter(results[row_key[i]][0] for i in reps[LABELS[0]].values()
                     if results[row_key[i]][0].startswith("ОШИБКА") or results[row_key[i]][0] == "R")
    if errors:
        summary["ошибки разметки"] = dict(errors)
    return {"сводка": summary, "корни": full}


def text(summary, top=20):
    """Строки для текстовой выдачи схемы."""
    kept = summary[LABELS[1]]
    greedy = kept["корней, чтобы затронуть все условия A/B (жадно)"]
    lines = [f"== знания: оставлено неизвестных запретов {kept['запретов']} — вопросов человеку (C) "
             f"{kept['вопросов человеку (C)']}, ждут знаний {kept['ждут знаний (A + B)']}: корней "
             f"{kept['корней знаний всего']} (значений групп {kept['из них значений записанных групп']}, "
             f"правил для произведений {kept['из них правил для произведений (шаблон × «×»)']})"
             + (f", жадно {greedy} затрагивают все ==" if greedy is not None else " ==")]
    for q in summary["очередь знаний"][:top]:
        lines.append(f"знание {q['корень']} — запретов {q['запретов']} ({q['что']})")
    for q in summary["вопросы человеку"][:top]:
        num = f" №{q['№']}" if q["№"] is not None else ""
        lines.append(f"вопрос{num}: {q['запрет']}   [примеров посылок: {q['примеров']}]")
    return lines
