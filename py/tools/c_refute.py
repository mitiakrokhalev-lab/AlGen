"""Поиск конечных контрпримеров к вопросам человеку (вид C) среди малых групп GAP.

    python3 -B -m tools.c_refute ВОПРОСЫ --выход найдено.jsonl [--до 1000] [--нечётные-до 2000]
        [--групп-на-порядок 2000] [--попаданий 2] [--только-скрипт скрипт.g]

ВОПРОСЫ — строки «схема запрет [примеров посылок: n]» (как в тексте выдачи «вопрос №…: …») или
JSON-список запретов. Запрет (конъюнкция литералов о группе G) переводится в предикат GAP; группа
SmallGroup(n, i), на которой верны все литералы, — кандидат в контрпример. Атомы вне перевода —
вопрос пропускается с причиной. Кандидат не опровергает вопрос сам: группа добавляется в библиотеку
штатно (`finite.py --добавить n:i`), её значения считают прежние скрипты GAP, и опровержение даёт
обычная пересборка — ошибка перевода не может дать ложного опровержения.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

GAP_HEAD = r'''
BreakOnError := false;  # ошибка в предикате — в CALL_WITH_CATCH, не в цикл прерывания
QuotientBy := function(X, N) return Image(NaturalHomomorphismByNormalSubgroup(X, N)); end;
OutP := function(X) local A;
  A := AutomorphismGroup(X);
  return Image(IsomorphismPermGroup(QuotientBy(A, InnerAutomorphismsAutomorphismGroup(A))));
end;
OrderPQ := function(n) local f; f := Factors(n); return Length(f) = 2 and f[1] <> f[2]; end;
OrderP2 := function(n) local f; f := Factors(n); return Length(f) = 2 and f[1] = f[2]; end;
PrimeOrders := X -> ForAll(ConjugacyClasses(X), c -> Order(Representative(c)) = 1 or IsPrimeInt(Order(Representative(c))));
MaxAll := function(X, test)
  if Size(X) = 1 then return true; fi;
  return ForAll(MaximalSubgroupClassReps(X), test);
end;
Indec := X -> Size(X) = 1 or Length(DirectFactorsOfGroup(X)) = 1;
IsoG := function(X, Y)
  if Size(X) <> Size(Y) then return false; fi;
  if Size(X) = 1 then return true; fi;
  if IdGroupsAvailable(Size(X)) then return IdGroup(X) = IdGroup(Y); fi;
  return IsomorphismGroups(X, Y) <> fail;
end;
EmbedsG := function(X, Y)
  if Size(X) = 1 then return true; fi;
  if Size(Y) mod Size(X) <> 0 then return false; fi;
  if Size(X) = Size(Y) then return IsoG(X, Y); fi;
  return IsomorphicSubgroups(Y, X) <> [];
end;
AutP := X -> Image(IsomorphismPermGroup(AutomorphismGroup(X)));
TwoGen := function(X)
  if Size(X) = 1 or IsCyclic(X) then return true; fi;
  if IsSolvableGroup(X) then return Length(MinimalGeneratingSet(X)) <= 2; fi;
  return Length(SmallGeneratingSet(X)) <= 2;  # верхняя оценка: «не 2-порождена» здесь — лишь кандидат
end;
CLT := X -> Set(List(ConjugacyClassesSubgroups(X), c -> Size(Representative(c)))) = DivisorsInt(Size(X));
InnQ := X -> QuotientBy(X, Centre(X));
'''

# свойство группы → выражение GAP от X (строка «{x}»)
GROUP_PROPS = {
    "trivial": "Size({x}) = 1", "abelian": "IsAbelian({x})", "cyclic": "IsCyclic({x})",
    "nilpotent": "IsNilpotentGroup({x})", "solvable": "IsSolvableGroup({x})", "perfect": "IsPerfectGroup({x})",
    "simple": "(Size({x}) > 1 and IsSimpleGroup({x}))", "centerless": "Size(Centre({x})) = 1",
    "odd-order": "IsOddInt(Size({x}))", "order-pq": "OrderPQ(Size({x}))", "order-p2": "OrderP2(Size({x}))",
    "prime-order": "IsPrimeInt(Size({x}))", "indecomposable": "Indec({x})",
    "exponent-2": "2 mod Exponent({x}) = 0", "exponent-3": "3 mod Exponent({x}) = 0",
    "exponent-4": "4 mod Exponent({x}) = 0", "exponent-6": "6 mod Exponent({x}) = 0",
    "metabelian": "IsAbelian(DerivedSubgroup({x}))",
    "class-2": "(IsNilpotentGroup({x}) and NilpotencyClassOfGroup({x}) <= 2)",
    "prime-orders": "PrimeOrders({x})",
    "proper-subs-abelian": "MaxAll({x}, IsAbelian)", "proper-subs-cyclic": "MaxAll({x}, IsCyclic)",
    "proper-subs-nilpotent": "MaxAll({x}, IsNilpotentGroup)",
    # у конечных групп
    "finite": "true", "fin-gen": "true", "periodic": "true", "hopfian": "true", "co-hopfian": "true",
    "residually-finite": "true", "linear": "true", "bounded-exponent": "true", "two-primes": None,
    "residually-nilpotent": "IsNilpotentGroup({x})", "locally-cyclic": "IsCyclic({x})",
    "free": "Size({x}) = 1", "free-abelian": "Size({x}) = 1", "divisible": "Size({x}) = 1",
    "torsion-free": "Size({x}) = 1", "no-finite-quotients": "Size({x}) = 1",
    "p-group": "IsPGroup({x})", "hyperbolic": "true", "two-generated": "TwoGen({x})", "clt": "CLT({x})",
}
DEAR_PROPS = {"clt"}  # перебор решётки подгрупп — только малые порядки
# свойства вложения: подгруппа {h} группы {a}
SUB_PROPS = {
    "normal": "IsNormal({a}, {h})", "central": "IsSubset(Centre({a}), {h})", "whole": "Size({h}) = Size({a})",
    "index-2": "Index({a}, {h}) = 2", "hall": "Gcd(Size({h}), Index({a}, {h})) = 1",
    "characteristic": None, "maximal": None,
}
# конструкции: (число аргументов, шаблон, вид результата: "obj" — группа, "sub" — подгруппа первого аргумента,
# дорого — True, если нужен Aut)
CONS = {
    "center": (1, "Centre({0})", "sub", False), "commutator": (1, "DerivedSubgroup({0})", "sub", False),
    "frattini": (1, "FrattiniSubgroup({0})", "sub", False), "quotient": (2, "QuotientBy({0}, {1})", "obj", False),
    "inn": (1, "InnQ({0})", "obj", False), "aut": (1, "AutP({0})", "obj", True),
    "prod": (2, "DirectProduct({0}, {1})", "obj", False), "profinite": (1, "{0}", "obj", False),
    "torsion": (1, "{0}", "sub", False), "ulm": (1, "TrivialSubgroup({0})", "sub", False),
    "ab": (1, "QuotientBy({0}, DerivedSubgroup({0}))", "obj", False),
    "normal-closure": (2, "NormalClosure({0}, {1})", "sub", False), "core": (2, "Core({0}, {1})", "sub", False),
    "centralizer": (2, "Centralizer({0}, {1})", "sub", False), "normalizer": (2, "Normalizer({0}, {1})", "sub", False),
}


class Unsupported(Exception):
    pass


def translate(conj):
    """(тело функции GAP от G, дорого?) — проверка, что G удовлетворяет всем литералам запрета."""
    from algen.etalon import scheme
    from algen.logic import App, Var, Vocab
    v = Vocab.section("grp")
    lits = [x.strip() for x in conj.split(" & ")]
    names, lines, expensive = {}, [], [False]

    def term(t):
        if isinstance(t, Var):
            if str(t) != "G":
                raise Unsupported(f"переменная {t}")
            return "G"
        key = str(t)
        if key in names:
            return names[key]
        # Out(X) = Aut(X)/Inn(X): Inn — подгруппа Aut, а не отдельная группа X/Z(X)
        if (isinstance(t, App) and t.op == "quotient" and isinstance(t.args[0], App) and t.args[0].op == "aut"
                and isinstance(t.args[1], App) and t.args[1].op == "inn" and t.args[0].args == t.args[1].args):
            x = term(t.args[0].args[0])
            expensive[0] = True
            var = f"t{len(names) + 1}"
            names[key] = var
            lines.append(f"  {var} := OutP({x});")
            return var
        if not isinstance(t, App) or t.op not in CONS:
            raise Unsupported(f"конструкция {getattr(t, 'op', t)}")
        n, tpl, _kind, dear = CONS[t.op]
        if len(t.args) != n:
            raise Unsupported(f"арность {t.op}")
        args = [term(a) for a in t.args]
        expensive[0] |= dear
        var = f"t{len(names) + 1}"
        names[key] = var
        lines.append(f"  {var} := {tpl.format(*args)};")
        return var

    def ambient(t):
        if isinstance(t, App) and t.op in CONS and CONS[t.op][2] == "sub":
            return term(t.args[0])
        raise Unsupported(f"у {t} нет объемлющей")

    checks = []
    for lit in lits:
        neg = lit.startswith("¬")
        body = lit[1:] if neg else lit
        g, _prem, gl = scheme(v, {"раздел": "grp", "условие": "∀ G : Grp", "цель": body})
        atom = gl[0]
        if atom[0] == "p":
            p, t = atom[1], atom[2]
            if p == "primitive" and isinstance(t, App) and t.op == "regular-act":
                # регулярное действие примитивно ⇔ |G| простое (G = 1 в переборе не встречается: n ⩾ 2)
                expr = f"IsPrimeInt(Size({term(t.args[0])}))"
            elif p in GROUP_PROPS and GROUP_PROPS[p] is not None:
                expensive[0] |= p in DEAR_PROPS
                expr = GROUP_PROPS[p].format(x=term(t))
            elif p in SUB_PROPS and SUB_PROPS[p] is not None:
                expr = SUB_PROPS[p].format(h=term(t), a=ambient(t))
            else:
                raise Unsupported(f"свойство {p}")
        elif atom[0] == "r":
            r, a, b = atom[1], atom[2], atom[3]
            if r == "iso":
                expr = f"IsoG({term(a)}, {term(b)})"
            elif r == "embeds":
                expr = f"EmbedsG({term(a)}, {term(b)})"
            elif r == "le":
                expr = f"IsSubset({term(b)}, {term(a)})"
            elif r == "eq-sub":
                expr = f"{term(a)} = {term(b)}"
            else:
                raise Unsupported(f"отношение {r}")
        else:
            raise Unsupported(f"атом {atom[0]}")
        checks.append(f"not ({expr})" if neg else f"({expr})")
    # литералы проверяются по одному — дорогие подтермы не считаются, если раньше уже «нет»
    out = []
    computed = set()
    for lit_lines, chk in _split(lines, checks, names):
        for ln in lit_lines:
            if ln not in computed:
                out.append(ln)
                computed.add(ln)
        out.append(f"  if not {chk} then return false; fi;")
    out.append("  return true;")
    return "\n".join(out), expensive[0]


def _split(lines, checks, names):
    """Строки определения подтермов перед каждой проверкой: только нужные ей (по именам tK)."""
    defs = {ln.split(" := ")[0].strip(): ln for ln in lines}
    order = [ln.split(" := ")[0].strip() for ln in lines]
    for chk in checks:
        used = set(re.findall(r"\bt\d+\b", chk))
        need, stack = set(), list(used)
        while stack:
            x = stack.pop()
            if x in need:
                continue
            need.add(x)
            stack += re.findall(r"\bt\d+\b", defs[x].split(" := ", 1)[1])
        yield [defs[x] for x in order if x in need], chk


def read_questions(path):
    text = Path(path).read_text(encoding="utf-8")
    if text.lstrip().startswith("["):
        return json.loads(text)
    out = []
    for line in text.splitlines():
        if not line.strip():
            continue
        body = line.split("   [")[0]
        parts = body.split(" ", 1)
        conj = parts[1] if len(parts) > 1 and "(" not in parts[0] else body
        out.append(conj.strip())
    return out


def script(questions, out_path, upto, odd_upto, per_order, hits):
    preds, skipped = [], []
    for k, q in enumerate(questions):
        try:
            body, dear = translate(q)
        except Exception as e:  # noqa: BLE001 — перевод не удался: вопрос пропускается с причиной
            skipped.append({"вопрос": q, "причина": str(e)[:160]})
            continue
        odd = "odd-order(G)" in [x.strip() for x in q.split(" & ")]
        preds.append((k, q, body, dear, odd))
    g = [GAP_HEAD]
    for k, q, body, _dear, _odd in preds:
        locs = sorted(set(re.findall(r"\bt\d+\b", body)), key=lambda x: int(x[1:]))
        local = f"  local {', '.join(locs)};\n" if locs else ""
        g.append(f"P{k} := function(G)\n{local}{body}\nend;")
    meta = ", ".join(f"[{k}, P{k}, {str(dear).lower()}, {str(odd).lower()}]" for k, _q, _b, dear, odd in preds)
    g.append(f'''
QS := [{meta}];
FOUND := List(QS, q -> 0);
OUT := OutputTextFile("{out_path}", false);
SetPrintFormattingStatus(OUT, false);
for n in [2..{max(upto, odd_upto)}] do
  # порядок без библиотеки малых групп (512, 1024, … в пакете дистрибутива) — пропуск, а не обрыв перебора
  if SmallGroupsAvailable(n) and NrSmallGroups(n) <= {per_order} then
    for i in [1..NrSmallGroups(n)] do
      G := SmallGroup(n, i);
      for j in [1..Length(QS)] do
        q := QS[j];
        if FOUND[j] < {hits} and (n <= {upto} or (q[4] and IsOddInt(n) and n <= {odd_upto}))
           and (not q[3] or n <= 300) and (not q[4] or IsOddInt(n)) then
          r := CALL_WITH_CATCH(q[2], [G]);
          if r[1] = true and r[2] = true then
            FOUND[j] := FOUND[j] + 1;
            AppendTo(OUT, "{{\\"k\\":", q[1], ",\\"n\\":", n, ",\\"i\\":", i, "}}\\n");
          fi;
        fi;
      od;
    od;
  fi;
od;
CloseStream(OUT);
QUIT;
''')
    return "\n".join(g), preds, skipped


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("вопросы")
    ap.add_argument("--выход", required=True)
    ap.add_argument("--до", type=int, default=1000)
    ap.add_argument("--нечётные-до", type=int, default=2000)
    ap.add_argument("--групп-на-порядок", type=int, default=2000)
    ap.add_argument("--попаданий", type=int, default=2)
    ap.add_argument("--только-скрипт")
    ap.add_argument("--секунд", type=int, default=18000)
    ap.add_argument("--журнал", help="вывод GAP (ошибки разбора и счёта) — в этот файл")
    a = ap.parse_args(argv)
    qs = read_questions(a.вопросы)
    with tempfile.TemporaryDirectory() as tmp:
        raw = Path(tmp) / "hits.jsonl"
        text, preds, skipped = script(qs, raw, a.до, a.нечётные_до, a.групп_на_порядок, a.попаданий)
        if a.только_скрипт:
            Path(a.только_скрипт).write_text(text, encoding="utf-8")
        else:
            log = open(a.журнал, "w", encoding="utf-8") if a.журнал else subprocess.DEVNULL
            try:
                subprocess.run(["gap", "-q", "-o", "8g"], input=text, text=True, timeout=a.секунд,
                               stdout=log, stderr=subprocess.STDOUT)
            except subprocess.TimeoutExpired:
                pass
            finally:
                if a.журнал:
                    log.close()
        hits = [json.loads(x) for x in raw.read_text().splitlines()] if raw.exists() else []
    by = {}
    for h in hits:
        by.setdefault(h["k"], []).append(f"{h['n']}:{h['i']}")
    with open(a.выход, "w", encoding="utf-8") as f:
        for k, q, *_ in preds:
            f.write(json.dumps({"вопрос": q, "кандидаты": by.get(k, [])}, ensure_ascii=False) + "\n")
        for s in skipped:
            f.write(json.dumps(dict(s, кандидаты=None), ensure_ascii=False) + "\n")
    print(json.dumps({"вопросов": len(qs), "переведено": len(preds), "пропущено": len(skipped),
                      "с кандидатами": len(by)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
