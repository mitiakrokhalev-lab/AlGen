"""Тождества как свойства: «тождество L ⇒ тождество M» (дорожка «Язык», Я2).

Многообразие V(L) — все группы, где верно L. Утверждение «L ⇒ M» верно
тогда и только тогда, когда M верно в относительно свободной группе
F_r / V(F_r), r — число переменных M (V(F_r) вполне характеристична, поэтому
M(x₁, …, x_r) ∈ V(F_r) значит M ∈ V).

Вывод. Возьмём конечный набор подстановок L в слова от образующих
x₁, …, x_r: Q = ⟨x | подстановки⟩ = F_r / N, N ⊆ V(F_r). Если перечисление
смежных классов единичной подгруппы (Тодд–Коксетер) завершилось, Q конечна и
задана перестановками. M(x) = 1 в Q ⇒ M(x) ∈ N ⊆ V(F_r) ⇒ «L ⇒ M» верно.
Ответ «выводится» — с сертификатом: число подстановок и порядок Q.

Опровержение. Если вдобавок L верно в самой Q (проверка на всех наборах
элементов), то Q ∈ V(L); M(x) ≠ 1 в Q даёт контрпример — конечную группу Q.
Второй источник контрпримеров — свободные нильпотентные группы ступени c
(алгебра Магнуса, identities.holds): если L верно во всех группах ступени ⩽ c,
а M — нет, то свободная нильпотентная группа ступени c — контрпример.

Иначе — «неизвестно» (перечисление не уложилось в предел или Q не из V(L)).
"""

from itertools import product

from .identities import holds, inv, parse, reduce, subst


def law_word(text):
    """«u = v» → слово u⁻¹v; «u» → слово u (u = 1)."""
    if "=" in text:
        lhs, rhs = text.split("=", 1)
        return reduce(inv(parse(lhs.strip())) + parse(rhs.strip()))
    return reduce(parse(text.strip()))


def variables(w):
    seen = []
    for x, _ in w:
        if x not in seen:
            seen.append(x)
    return seen


def words(gens, length):
    """Все свободно несократимые слова длины ⩽ length (с пустым)."""
    letters = [(g, 1) for g in gens] + [(g, -1) for g in gens]
    out, layer = [[]], [[]]
    for _ in range(length):
        nxt = []
        for w in layer:
            for l in letters:
                if w and w[-1] == (l[0], -l[1]):
                    continue
                nxt.append(w + [l])
        out += nxt
        layer = nxt
    return out


def instances(law, gens, length):
    """Подстановки закона в слова длины ⩽ length от gens: циклически сокращённые, без повторов."""
    vs = variables(law)
    seen, out = set(), []
    pool = words(gens, length)
    for images in product(pool, repeat=len(vs)):
        w = reduce(subst(law, dict(zip(vs, images))))
        # циклическое сокращение
        while len(w) > 1 and w[0] == (w[-1][0], -w[-1][1]):
            w = w[1:-1]
        if not w:
            continue
        key = tuple(w)
        if key not in seen:
            seen.add(key)
            out.append(w)
    return out


class TooBig(Exception):
    pass


def todd_coxeter(gens, rels, limit=50000):
    """Регулярное представление ⟨gens | rels⟩ (смежные классы единичной подгруппы),
    стратегия HLT с обработкой совпадений. Возвращает {(g, ±1): [образ класса i]}
    на классах 0..n−1 или бросает TooBig."""
    cols = [(g, 1) for g in gens] + [(g, -1) for g in gens]
    inv_col = {c: (c[0], -c[1]) for c in cols}
    table = {c: [None] for c in cols}
    parent = [0]  # union-find для совпадений
    alive = [True]

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def new():
        n = len(parent)
        if n >= limit:
            raise TooBig(n)
        parent.append(n)
        alive.append(True)
        for c in cols:
            table[c].append(None)
        return n

    queue = []

    def coincide(a, b):
        a, b = find(a), find(b)
        if a == b:
            return
        if a > b:
            a, b = b, a
        queue.append((a, b))
        while queue:
            a, b = queue.pop()
            a, b = find(a), find(b)
            if a == b:
                continue
            if a > b:
                a, b = b, a
            parent[b] = a
            alive[b] = False
            for c in cols:
                t = table[c][b]
                if t is None:
                    continue
                t = find(t)
                ic = inv_col[c]
                if table[ic][t] is not None and find(table[ic][t]) == b:
                    table[ic][t] = None
                u = table[c][a]
                if u is None:
                    table[c][a] = t
                    if table[ic][t] is None:
                        table[ic][t] = a
                else:
                    queue.append((find(u), t))
                    if table[ic][t] is None:
                        table[ic][t] = a

    def define(a, c):
        b = new()
        table[c][a] = b
        table[inv_col[c]][b] = a
        return b

    def scan(a, w):
        """Проследить слово w от класса a, дополняя таблицу (HLT)."""
        f, i = a, 0
        while i < len(w):
            nxt = table[w[i]][find(f)]
            if nxt is None:
                break
            f, i = find(nxt), i + 1
        if i == len(w):
            if find(f) != find(a):
                coincide(f, a)
            return
        b, j = a, len(w)
        while j > i:
            prv = table[inv_col[w[j - 1]]][find(b)]
            if prv is None:
                break
            b, j = find(prv), j - 1
        if j < i:
            coincide(f, b)
            return
        while j > i + 1:
            f = define(find(f), w[i])
            i += 1
        if j == i + 1:
            f, b = find(f), find(b)
            c = w[i]
            if table[c][f] is None and table[inv_col[c]][b] is None:
                table[c][f] = b
                table[inv_col[c]][b] = f
            else:
                tgt = table[c][f]
                if tgt is not None:
                    coincide(tgt, b)
                else:
                    coincide(table[inv_col[c]][b], f)

    a = 0
    while a < len(parent):
        if alive[a] and find(a) == a:
            for r in rels:
                scan(a, list(r))
                if find(a) != a:
                    break
            if find(a) == a:
                for c in cols:
                    if table[c][a] is None:
                        define(a, c)
        a += 1
    reps = [i for i in range(len(parent)) if find(i) == i]
    index = {r: k for k, r in enumerate(reps)}
    return {c: [index[find(table[c][r])] for r in reps] for c in cols}


def act(perms, w, start=0):
    i = start
    for x in w:
        i = perms[x][i]
    return i


def is_identity(perms, w, n):
    """w = 1 в группе, заданной регулярным действием: достаточно класса 0
    (регулярное действие точно), но проверяем все n для надёжности."""
    return all(act(perms, w, i) == i for i in range(n))


def elements(perms, gens, n):
    """Каждому элементу (классу) — слово-представитель (поиск в ширину)."""
    rep = {0: []}
    frontier = [0]
    cols = [(g, 1) for g in gens] + [(g, -1) for g in gens]
    while frontier:
        nxt = []
        for i in frontier:
            for c in cols:
                j = perms[c][i]
                if j not in rep:
                    rep[j] = rep[i] + [c]
                    nxt.append(j)
        frontier = nxt
    return [rep[i] for i in range(n)]


def law_holds_in(perms, gens, n, law, budget=2_000_000):
    """Верно ли закон law во всей конечной группе (все наборы элементов).
    None — перебор больше бюджета."""
    vs = variables(law)
    if n ** len(vs) > budget:
        return None
    reps = elements(perms, gens, n)
    for images in product(reps, repeat=len(vs)):
        w = subst(law, dict(zip(vs, images)))
        if act(perms, w) != 0:
            return False
    return True


# Добавочные законы для поиска конечных контрпримеров в V(L)
EXTRA = ["x^2 = 1", "x^3 = 1", "x^4 = 1", "x^5 = 1", "x^6 = 1", "[x, y, z] = 1", "[[x, y], [z, t]] = 1"]


def decide_laws(premise, goal, length=2, limit=50000, max_class=4):
    """«premise ⇒ goal» для законов-текстов. Возвращает (вердикт, пояснение)."""
    L, M = law_word(premise), law_word(goal)
    gens = variables(M) or ["x"]
    # 1) конечная Q = ⟨gens | подстановки L⟩
    rels = instances(L, gens, length)
    try:
        perms = todd_coxeter(gens, rels, limit)
    except TooBig as e:
        perms = None
        q_note = f"перечисление больше {e.args[0]} классов"
    if perms is not None:
        n = len(perms[(gens[0], 1)])
        if act(perms, M) == 0:
            return "выводится", f"M = 1 в ⟨{','.join(gens)} | {len(rels)} подстановок L⟩ порядка {n}"
        ok = law_holds_in(perms, gens, n, L)
        if ok:
            return "опровергается", f"Q = F_{len(gens)}/V(L) порядка {n}: L верно, M нет"
        q_note = f"Q порядка {n} не из V(L)" if ok is False else f"Q порядка {n}: L не проверено (велика)"
    # 2) Кнут–Бендикс: M сводится к 1 в ⟨gens | подстановки L⟩ ⇒ выводится
    nf = knuth_bendix(gens, rels)
    if nf is not None and not nf(M):
        return "выводится", f"M = 1 в ⟨{','.join(gens)} | {len(rels)} подстановок L⟩ (Кнут–Бендикс)"
    # 3) конечные группы из V(L) ∩ V(E) для добавочных законов E
    for extra in EXTRA:
        E = law_word(extra)
        rels2 = rels + instances(E, gens, 1)
        try:
            perms = todd_coxeter(gens, rels2, limit)
        except TooBig:
            continue
        n = len(perms[(gens[0], 1)])
        if act(perms, M) != 0 and law_holds_in(perms, gens, n, L):
            return "опровергается", (f"конечная группа порядка {n} (⟨подстановки L и {extra}⟩): "
                                     "L проверено на всех наборах её элементов, M нет")
    # 4) свободные нильпотентные
    for c in range(1, max_class + 1):
        if holds(L, [], c)[0] and not holds(M, [], c)[0]:
            return "опровергается", f"свободная нильпотентная ступени {c}: L верно, M нет"
    return "неизвестно", q_note


# --- Кнут–Бендикс: вывод в бесконечных многообразиях ------------------------------


def _key(w, order):
    return (len(w), [order[x] for x in w])


def knuth_bendix(gens, rels, max_rules=400, max_len=24):
    """Пополнение (shortlex) для группы ⟨gens | rels⟩. Буквы — (g, ±1).
    Возвращает функцию нормальной формы или None, если не уложились в пределы.
    Нормальная форма пустая ⇔ слово = 1 в группе (если система конфлюэнтна)."""
    letters = []
    for g in gens:
        letters += [(g, 1), (g, -1)]
    order = {l: i for i, l in enumerate(letters)}
    rules = {}

    def add(lhs, rhs):
        lhs, rhs = tuple(lhs), tuple(rhs)
        if lhs == rhs:
            return False
        if _key(list(lhs), order) < _key(list(rhs), order):
            lhs, rhs = rhs, lhs
        if lhs in rules and rules[lhs] == rhs:
            return False
        rules[lhs] = rhs
        return True

    for l in letters:
        add([l, (l[0], -l[1])], [])

    def nf(w):
        w = list(w)
        changed = True
        while changed:
            changed = False
            for lhs, rhs in sorted(rules.items(), key=lambda r: -len(r[0])):
                n = len(lhs)
                for i in range(len(w) - n + 1):
                    if tuple(w[i:i + n]) == lhs:
                        w[i:i + n] = list(rhs)
                        changed = True
                        break
                if changed:
                    break
        return w

    for r in rels:
        r = list(r)
        h = (len(r) + 1) // 2
        add(nf(r[:h]), nf(inv(r[h:])))
    for _ in range(60):
        new = []
        items = list(rules.items())
        for l1, r1 in items:
            for l2, r2 in items:
                # перекрытие: суффикс l1 = префикс l2
                for k in range(1, min(len(l1), len(l2))):
                    if l1[-k:] == l2[:k]:
                        w = list(l1) + list(l2[k:])
                        a = nf(list(r1) + list(l2[k:]))
                        b = nf(list(l1[:-k]) + list(r2))
                        if a != b:
                            new.append((a, b))
                # вхождение l2 внутрь l1
                if len(l2) < len(l1):
                    for i in range(len(l1) - len(l2) + 1):
                        if l1[i:i + len(l2)] == l2:
                            a = nf(list(r1))
                            b = nf(list(l1[:i]) + list(r2) + list(l1[i + len(l2):]))
                            if a != b:
                                new.append((a, b))
        if not new:
            # межсокращение: левые части, сократимые другими правилами, убрать
            return nf
        for a, b in new:
            a, b = nf(a), nf(b)
            if a != b:
                add(a, b)
        if len(rules) > max_rules or any(len(l) > max_len for l in rules):
            return None
    return None
