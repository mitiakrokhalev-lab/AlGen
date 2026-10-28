"""Тождества в элементах (расширение E): «∀ a, b, c ∈ G: u = v».

Тождество верно во всех группах многообразия тогда и только тогда, когда
оно верно в относительно свободной группе этого многообразия того же ранга,
что и число переменных. Здесь разобраны три многообразия:

* все группы — свободная группа, слово сравнивается свободной редукцией;
* нильпотентные ступени ⩽ c — свободная нильпотентная группа F/γ_{c+1}F.
  Она вложена в единицы алгебры некоммутативных многочленов над ℤ по
  модулю мономов степени > c, xᵢ ↦ 1 + Xᵢ (теорема Магнуса: ядро
  отображения F → (ℤ⟨X⟩/степень > c)* — ровно γ_{c+1}F). Абелевы группы —
  это c = 1, «коммутант в центре» — c = 2.

Ответ точный в обе стороны: если слово u⁻¹v в относительно свободной группе
нетривиально, сама эта группа (а с ней и её конечные p-факторы) —
контрпример.

    cd py && python3 -m algen.identities "[a b, c] = [a, c][b, c]" --ступень 2
"""

import argparse
import re

SUP = {"⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9"}


class ParseError(ValueError):
    pass


# --- слова: список (переменная, ±1) -------------------------------------------


def inv(w):
    return [(x, -e) for x, e in reversed(w)]


def power(w, n):
    return (w if n >= 0 else inv(w)) * abs(n)


def comm(u, v, convention="x⁻¹y⁻¹xy"):
    if convention == "x⁻¹y⁻¹xy":
        return inv(u) + inv(v) + u + v
    if convention == "xyx⁻¹y⁻¹":
        return u + v + inv(u) + inv(v)
    raise ParseError(f"неизвестное соглашение о коммутаторе: {convention}")


def reduce(w):
    out = []
    for x, e in w:
        if out and out[-1] == (x, -e):
            out.pop()
        else:
            out.append((x, e))
    return out


def parse(s, convention="x⁻¹y⁻¹xy"):
    """Слово в нотации задачника: ab, a⁻¹, a^3, a^b = b⁻¹ab, [a, b], [a, b, c] = [[a, b], c]."""
    s = s.replace("^-1", "⁻¹").replace("^{-1}", "⁻¹")
    toks = re.findall(r"⁻¹|[⁰¹²³⁴⁵⁶⁷⁸⁹]+|\^-?\d+|\^[a-z]|[a-z]|1|[\[\](),*·]|\S", s)
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def take(t=None):
        nonlocal pos
        tok = peek()
        if t is not None and tok != t:
            raise ParseError(f"ждал «{t}», а там «{tok}» в «{s}»")
        pos += 1
        return tok

    def expr():
        w = []
        while peek() not in (None, ")", "]", ","):
            if peek() in ("*", "·"):
                take()
                continue
            w += term()
        return w

    def term():
        tok = take()
        if tok == "1":
            w = []
        elif re.fullmatch(r"[a-z]", tok):
            w = [(tok, 1)]
        elif tok == "(":
            w = expr()
            take(")")
        elif tok == "[":
            parts = [expr()]
            while peek() == ",":
                take()
                parts.append(expr())
            take("]")
            if len(parts) < 2:
                raise ParseError(f"в коммутаторе меньше двух аргументов: «{s}»")
            w = parts[0]
            for p in parts[1:]:
                w = comm(w, p, convention)
        else:
            raise ParseError(f"непонятный знак «{tok}» в «{s}»")
        while peek() is not None:
            t = peek()
            if t == "⁻¹":
                take()
                w = inv(w)
            elif t[0] in SUP:
                take()
                w = power(w, int("".join(SUP[c] for c in t)))
            elif t.startswith("^") and re.fullmatch(r"\^-?\d+", t):
                take()
                w = power(w, int(t[1:]))
            elif t.startswith("^"):
                take()
                g = [(t[1], 1)]
                w = inv(g) + w + g
            else:
                break
        return w

    w = expr()
    if peek() is not None:
        raise ParseError(f"лишнее «{peek()}» в «{s}»")
    return w


# --- алгебра Магнуса ------------------------------------------------------------


class Magnus:
    """ℤ⟨X⟩ по модулю мономов степени > c; элемент — {моном: коэффициент}."""

    def __init__(self, c):
        self.c = c

    def mul(self, p, q):
        out = {}
        for m1, a in p.items():
            for m2, b in q.items():
                if len(m1) + len(m2) <= self.c:
                    m = m1 + m2
                    out[m] = out.get(m, 0) + a * b
        return {m: v for m, v in out.items() if v}

    def letter(self, x, e):
        # 1 + X и (1 + X)⁻¹ = Σ (−X)^k
        if e > 0:
            return {(): 1, (x,): 1} if self.c >= 1 else {(): 1}
        return {(x,) * k: (-1) ** k for k in range(self.c + 1)}

    def image(self, w):
        p = {(): 1}
        for x, e in w:
            p = self.mul(p, self.letter(x, e))
        return p


def holds(lhs, rhs, c=None):
    """Верно ли u = v во всех группах ступени нильпотентности ⩽ c
    (c = None — во всех группах). Возвращает (верно, свидетель): свидетель —
    ненулевой член u⁻¹v в алгебре Магнуса или несокращаемое слово."""
    w = inv(lhs) + rhs
    if c is None:
        r = reduce(w)
        return (not r, r)
    if c == 0:
        return True, None
    img = Magnus(c).image(w)
    rest = {m: v for m, v in img.items() if m}
    return (not rest, rest)


def show_word(w):
    return "".join(x if e > 0 else x + "⁻¹" for x, e in w) or "1"


def show_poly(p):
    terms = sorted(p.items(), key=lambda t: (len(t[0]), t[0]))
    return " + ".join(f"{v}·{''.join(m).upper()}" for m, v in terms[:4]) + (" + …" if len(terms) > 4 else "")


# --- гипотезы условия → многообразие ------------------------------------------

# Свойства, которыми обладает свободная нильпотентная группа ступени c ⩾ 1
# конечного ранга или её конечные p-факторы. Если остальные посылки только
# такие, контрпример в относительно свободной группе годится и для условия.
FREE_NILPOTENT = {"nilpotent", "solvable", "residually-finite", "fin-gen", "linear", "polycyclic",
                  "hopfian", "finite", "periodic", "torsion-free"}


def variety(premises):
    """Ступень c по посылкам условия: (c, лишние посылки)."""
    c, rest = None, []
    for a, v in premises:
        if a[0] == "p" and a[1] == "abelian" and v:
            c = 1 if c is None else min(c, 1)
        elif a[0] == "p" and a[1] == "trivial" and v:
            c = 0
        elif (a[0] == "r" and a[1] == "le" and v and len(a) == 4
              and getattr(a[2], "op", None) == "commutator" and getattr(a[3], "op", None) == "center"):
            c = 2 if c is None else min(c, 2)
        else:
            rest.append((a, v))
    return c, rest


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("тождество")
    ap.add_argument("--ступень", dest="c", type=int, default=None)
    ap.add_argument("--коммутатор", dest="conv", default="x⁻¹y⁻¹xy")
    a = ap.parse_args()
    lhs, rhs = a.тождество.split("=")
    ok, wit = holds(parse(lhs, a.conv), parse(rhs, a.conv), a.c)
    where = "во всех группах" if a.c is None else f"в группах ступени ⩽ {a.c}"
    if ok:
        print(f"верно {where}")
    else:
        print(f"неверно {where}: u⁻¹v = " + (show_word(wit) if a.c is None else show_poly(wit) + " ≠ 0"))


if __name__ == "__main__":
    main()
