"""Условия с параметрами (расширение P): «p < q — простые, |G| = pq ⇒ …».

Параметры — вершины сортов Prime и ℕ, числа — термы: |G| = ord(G), индекс
index(G, N), арифметика (+, −, ·, ^, gcd, lcm, φ) и семейства групп Cₙ, Dₙ
(порядка 2n), Sₙ, Aₙ, Dicₙ. Цель — формула (¬, ∧, ∨, ⇒, ⇔) над свойствами,
сравнениями чисел, делимостью и изоморфизмом.

Проверка — перебор всех примеров в таблице конечных групп: параметры
пробегают простые и натуральные числа до границы, группы — таблицу GAP,
подгруппы — классы подгрупп. Найденный пример, где посылки верны, а цель
ложна, опровергает условие. Если такого нет, условие верно на всех
примерах до границы, но это не доказательство: такое условие генератор
не закрывает.

    cd py && python3 -m algen.params "∀ p : Prime; ∀ G : Grp | ord(G) = p^2" "abelian(G)"
"""

import argparse
import json
import math
import re
from itertools import islice

from .library import GROUP_PROPS, SUB_PROPS, Library
from .logic import DATA

FAMILIES = DATA / "finite" / "grp-families.json"
BOUND = 100  # параметры и порядки групп не больше этого


class ParseError(ValueError):
    pass


def primes(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def phi(n):
    return sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1)


# --- разбор ----------------------------------------------------------------------

SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")
TOKEN = re.compile(r"\s*(⇔|⇒|∨|∧|¬|≠|≤|≥|≅|∤|[0-9]+|[⁰¹²³⁴⁵⁶⁷⁸⁹]+|[A-Za-zА-Яа-я][\w′'-]*|[()=<>|,+\-*·×/^])")


def tokenize(s):
    out, pos = [], 0
    s = s.strip()
    while pos < len(s):
        m = TOKEN.match(s, pos)
        if not m:
            raise ParseError(f"непонятный знак в «{s[pos:]}»")
        out.append(m.group(1))
        pos = m.end()
    return out


class Parser:
    """Формулы и термы. Узлы — кортежи (тег, …)."""

    def __init__(self, s):
        self.t, self.i, self.s = tokenize(s), 0, s

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def take(self, x=None):
        tok = self.peek()
        if x is not None and tok != x:
            raise ParseError(f"ждал «{x}», а там «{tok}» в «{self.s}»")
        self.i += 1
        return tok

    def done(self):
        if self.peek() is not None:
            raise ParseError(f"лишнее «{self.peek()}» в «{self.s}»")

    # формулы
    def formula(self):
        a = self.imp()
        if self.peek() == "⇔":
            self.take()
            return ("iff", a, self.imp())
        return a

    def imp(self):
        a = self.disj()
        if self.peek() == "⇒":
            self.take()
            return ("imp", a, self.imp())
        return a

    def disj(self):
        xs = [self.conj()]
        while self.peek() == "∨":
            self.take()
            xs.append(self.conj())
        return xs[0] if len(xs) == 1 else ("or", *xs)

    def conj(self):
        xs = [self.neg()]
        while self.peek() in ("∧", ","):
            self.take()
            xs.append(self.neg())
        return xs[0] if len(xs) == 1 else ("and", *xs)

    def neg(self):
        if self.peek() == "¬":
            self.take()
            return ("not", self.neg())
        if self.peek() == "(":
            # скобка формулы или терма: пробуем формулу, иначе откатываемся
            save = self.i
            self.take()
            try:
                f = self.formula()
                self.take(")")
                if self.peek() not in ("=", "≠", "<", "≤", ">", "≥", "|", "∤", "≅", "+", "-", "*", "·", "×", "/", "^"):
                    return f
            except ParseError:
                pass
            self.i = save
        a = self.expr()
        op = self.peek()
        if op in ("=", "≠", "<", "≤", ">", "≥", "|", "∤", "≅"):
            self.take()
            return ("cmp", op, a, self.expr())
        if a[0] != "call":
            raise ParseError(f"«{self.s}»: ждал свойство или сравнение")
        return ("pred", a[1], a[2])

    # термы
    def expr(self):
        a = self.term()
        while self.peek() in ("+", "-"):
            op = self.take()
            a = ("op", op, a, self.term())
        return a

    def term(self):
        a = self.power()
        while True:
            op = self.peek()
            if op in ("*", "·", "×", "/"):
                self.take()
                a = ("op", op, a, self.power())
            elif op is not None and (op[0].isalnum() or op == "(") and op not in ("∧", "∨"):
                a = ("op", "·", a, self.power())  # 2p, p q
            else:
                return a

    def power(self):
        a = self.primary()
        if self.peek() == "^":
            self.take()
            return ("op", "^", a, self.primary())
        if self.peek() and self.peek()[0] in "⁰¹²³⁴⁵⁶⁷⁸⁹":
            return ("op", "^", a, ("int", int(self.take().translate(SUP))))
        return a

    def primary(self):
        tok = self.take()
        if tok is None:
            raise ParseError(f"«{self.s}» оборвалось")
        if tok.isdigit():
            return ("int", int(tok))
        if tok == "(":
            a = self.expr()
            self.take(")")
            return a
        if tok[0].isalpha():
            if self.peek() == "(":
                self.take()
                args = [self.expr()]
                while self.peek() == ",":
                    self.take()
                    args.append(self.expr())
                self.take(")")
                return ("call", tok, args)
            return ("var", tok)
        raise ParseError(f"непонятный знак «{tok}» в «{self.s}»")


def parse_formula(s):
    p = Parser(s)
    f = p.formula()
    p.done()
    return f


SORTS = {"Prime": "prime", "ℕ": "nat", "N": "nat", "Nat": "nat", "Grp": "grp"}


def parse_condition(cond):
    """«∀ p : Prime; ∀ G : Grp | ord(G) = p^2; ∀ H : Sub(G) | …» → [(имя, сорт, родитель, посылка)]."""
    out = []
    for decl in cond.split(";"):
        head, _, body = decl.partition("|")
        m = re.fullmatch(r"\s*∀\s*([\w,\s]+?)\s*:\s*(\w+|ℕ)(?:\((\w+)\))?\s*", head)
        if not m:
            raise ParseError(f"объявление «{head.strip()}»")
        names, sort, parent = m.groups()
        if sort == "Sub":
            kind = "sub"
        elif sort in SORTS:
            kind = SORTS[sort]
        else:
            raise ParseError(f"сорт {sort}")
        names = [x.strip() for x in names.split(",")]
        for x in names[:-1]:
            out.append((x, kind, parent, None))
        out.append((names[-1], kind, parent, parse_formula(body) if body.strip() else None))
    return out


# --- значения ---------------------------------------------------------------------


class Model:
    """Вычисление формул на примерах из таблицы конечных групп."""

    def __init__(self, lib=None):
        self.lib = lib or Library()
        self.raw = None  # записи GAP (размеры классов подгрупп) — по требованию
        with open(FAMILIES, encoding="utf-8") as f:
            self.fam = {k: {int(n): v for n, v in d.items()} for k, d in json.load(f)["семейства"].items()}
        self.finite = [k for k, o in self.lib.obj.items() if o["конечная"]]
        self.by_order = {}
        for k in self.finite:
            self.by_order.setdefault(int(k.split(":")[0]), []).append(k)

    # значение терма: ("num", n), ("grp", key), ("sub", key, i) или None
    def term(self, t, env):
        tag = t[0]
        if tag == "int":
            return ("num", t[1])
        if tag == "var":
            if t[1] not in env:
                raise ParseError(f"переменная {t[1]} не объявлена")
            return env[t[1]]
        if tag == "op":
            a, b = self.term(t[2], env), self.term(t[3], env)
            if a is None or b is None:
                return None
            if a[0] == "num" and b[0] == "num":
                x, y = a[1], b[1]
                if t[1] == "+":
                    return ("num", x + y)
                if t[1] == "-":
                    return ("num", x - y)
                if t[1] in ("*", "·", "×"):
                    return ("num", x * y)
                if t[1] == "/":
                    return ("num", x // y) if y and x % y == 0 else None
                if t[1] == "^":
                    return ("num", x ** y) if y >= 0 and abs(x) ** y <= 10 ** 12 else None
            if t[1] in ("×", "·", "*") and a[0] != "num" and b[0] != "num":
                p = self.lib.prod.get((self.group(a), self.group(b)))
                return ("grp", p) if p else None
            if t[1] == "/" and a[0] == "grp" and b[0] == "sub" and b[1] == a[1]:
                q = self.lib.obj[a[1]]["подгруппы"][b[2]].get("фактор")
                return ("grp", q) if q else None
            raise ParseError(f"«{t[1]}» между {a[0]} и {b[0]}")
        if tag == "call":
            f, args = t[1], [self.term(x, env) for x in t[2]]
            if any(x is None for x in args):
                return None
            if f in self.fam:
                n = args[0][1]
                k = self.fam[f].get(n)
                return ("grp", k) if k in self.lib.obj else None
            if f in ("ord", "order"):
                return ("num", int(self.group(args[0]).split(":")[0]))
            if f == "index":
                g, h = args
                return ("num", int(self.group(g).split(":")[0]) // int(self.group(h).split(":")[0]))
            if f in ("gcd", "НОД"):
                return ("num", math.gcd(args[0][1], args[1][1]))
            if f in ("lcm", "НОК"):
                return ("num", math.lcm(args[0][1], args[1][1]))
            if f in ("fact", "factorial"):
                n = args[0][1]
                return ("num", math.factorial(n)) if 0 <= n <= 20 else None
            if f in ("phi", "φ"):
                return ("num", phi(args[0][1]))
            if f in ("n_p", "sylow_count"):
                # число силовских p-подгрупп: размер класса сопряжённых силовских
                pr, g = args[0][1], self.group(args[1])
                if self.raw is None:
                    from .finite import load
                    self.raw = load(extra=True)
                r = self.raw.get(g)
                if r is None or r["subs"] is None:
                    return None
                n = int(g.split(":")[0])
                pk = 1
                while n % (pk * pr) == 0:
                    pk *= pr
                cls = [x for x in r["subs"] if int(x["group"].split(":")[0]) == pk]
                return ("num", sum(x["class_size"] for x in cls)) if cls else None
            if f in ("Aut", "Out"):
                k = self.lib.obj[self.group(args[0])].get(f.lower())
                return ("grp", k) if k in self.lib.obj else None
            if f in ("Z", "center", "commutator"):
                g = args[0]
                if g[0] != "grp":
                    return None
                sid = self.lib.obj[g[1]].get("центр" if f != "commutator" else "коммутант")
                subs = self.lib.obj[g[1]]["подгруппы"] or []
                idx = next((i for i, s in enumerate(subs) if s["id"] == sid), None)
                return ("sub", g[1], idx) if idx is not None else None
            raise ParseError(f"неизвестная функция {f}")
        raise ParseError(f"терм {t}")

    def group(self, v):
        if v[0] == "grp":
            return v[1]
        if v[0] == "sub":
            return self.lib.obj[v[1]]["подгруппы"][v[2]]["≅"]
        raise ParseError("число там, где нужна группа")

    def props(self, v):
        if v[0] == "sub":
            s = self.lib.obj[v[1]]["подгруппы"][v[2]]
            return {**self.lib.obj[s["≅"]]["свойства"], **s["свойства"]}
        return self.lib.obj[self.group(v)]["свойства"]

    # значение формулы: True, False или None (не известно)
    def holds(self, f, env):
        tag = f[0]
        if tag == "not":
            x = self.holds(f[1], env)
            return None if x is None else not x
        if tag in ("and", "or"):
            vals = [self.holds(x, env) for x in f[1:]]
            if tag == "and":
                return False if False in vals else None if None in vals else True
            return True if True in vals else None if None in vals else False
        if tag == "imp":
            return self.holds(("or", ("not", f[1]), f[2]), env)
        if tag == "iff":
            a, b = self.holds(f[1], env), self.holds(f[2], env)
            return None if a is None or b is None else a == b
        if tag == "cmp":
            op, a, b = f[1], self.term(f[2], env), self.term(f[3], env)
            if a is None or b is None:
                return None
            if op == "≅":
                return self.group(a) == self.group(b)
            if op == "=" and a[0] == "sub" and b[0] == "sub":
                return a == b
            if a[0] != "num" or b[0] != "num":
                raise ParseError(f"сравнение «{op}» не чисел")
            x, y = a[1], b[1]
            return {"=": x == y, "≠": x != y, "<": x < y, "≤": x <= y, ">": x > y, "≥": x >= y,
                    "|": x != 0 and y % x == 0, "∤": not (x != 0 and y % x == 0)}[op]
        if tag == "pred":
            name, args = f[1], [self.term(x, env) for x in f[2]]
            if any(x is None for x in args):
                return None
            if name in ("prime", "простое"):
                return args[0][1] in set(primes(max(args[0][1], 2)))
            if name in ("even", "чётно"):
                return args[0][1] % 2 == 0
            if name in ("odd", "нечётно"):
                return args[0][1] % 2 == 1
            if name in GROUP_PROPS or name in SUB_PROPS:
                return self.props(args[0]).get(name)
            raise ParseError(f"неизвестное свойство {name}")
        raise ParseError(f"формула {f}")

    # перебор примеров
    def candidates(self, kind, parent, prem, env):
        if kind == "prime":
            return [("num", p) for p in primes(BOUND)]
        if kind == "nat":
            return [("num", n) for n in range(1, BOUND + 1)]
        if kind == "grp":
            order = self.order_hint(prem, env)
            keys = self.by_order.get(order, []) if order is not None else self.finite
            return [("grp", k) for k in keys]
        if kind == "sub":
            g = env[parent]
            subs = self.lib.obj[self.group(g)]["подгруппы"] or []
            return [("sub", self.group(g), i) for i in range(len(subs))]
        raise ParseError(kind)

    def order_hint(self, prem, env):
        """Если среди посылок есть ord(G) = e и e уже вычисляется — порядок."""
        if prem is None:
            return None
        conj = prem[1:] if prem[0] == "and" else [prem]
        for c in conj:
            if c[0] == "cmp" and c[1] == "=" and c[2][0] == "call" and c[2][1] in ("ord", "order"):
                try:
                    v = self.term(c[3], env)
                except ParseError:
                    continue
                if v and v[0] == "num":
                    return v[1]
        return None

    def instances(self, decls, env=None, k=0):
        env = env or {}
        if k == len(decls):
            yield dict(env)
            return
        name, kind, parent, prem = decls[k]
        for v in self.candidates(kind, parent, prem, env):
            env[name] = v
            if prem is None or self.holds_safe(prem, env) is True:
                yield from self.instances(decls, env, k + 1)
        env.pop(name, None)

    def holds_safe(self, f, env):
        try:
            return self.holds(f, env)
        except ParseError:
            raise
        except (KeyError, IndexError, TypeError, ZeroDivisionError):
            return None


def show_env(env, model):
    out = []
    for k, v in env.items():
        if v[0] == "num":
            out.append(f"{k} = {v[1]}")
        elif v[0] == "grp":
            out.append(f"{k} = {model.lib.obj[v[1]].get('имя') or v[1]} ({v[1]})")
        else:
            s = model.lib.obj[v[1]]["подгруппы"][v[2]]
            out.append(f"{k} ≅ {model.lib.obj[s['≅']].get('имя') or s['≅']}")
    return ", ".join(out)


def check(cond, goal, model, limit=200000):
    """(вердикт, детали, число проверенных примеров)."""
    decls = parse_condition(cond)
    g = parse_formula(goal)
    seen = unknown = 0
    for env in islice(model.instances(decls), limit):
        v = model.holds_safe(g, env)
        if v is None:
            unknown += 1
            continue
        seen += 1
        if v is False:
            return "опровергается", "контрпример: " + show_env(env, model), seen
    tail = f"; не вычислено на {unknown}" if unknown else ""
    if not seen:
        return "неизвестно", "ни одного примера в таблице" + tail, 0
    return "проверено", f"верно на всех {seen} примерах с параметрами и порядками ⩽ {BOUND}" + tail, seen


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("условие")
    ap.add_argument("цель")
    a = ap.parse_args()
    kind, detail, _ = check(a.условие, a.цель, Model())
    print(kind + ": " + detail)


if __name__ == "__main__":
    main()
