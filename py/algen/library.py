"""Библиотека групп: конечные из GAP и бесконечные из data/infinite/grp.json.

Конечные группы вычислены (algen.finite), их значения — истина. Бесконечные
записаны рукой, и каждое их значение проверяется выводом: на сцену «G, N ⩽ G,
G/N» ставятся все записанные значения группы, подгруппы и фактора, и
SAT-решатель ищет противоречие с базой правил. Противоречие — ошибка либо в
записи, либо в правиле, и ядро решателя показывает, какие значения вместе
невозможны. Значения, которых в записи нет, но которые следуют из записанных,
решатель выводит, и библиотека отдаёт их как выведенные.

Эта же сцена служит поиском контрпримеров: подставляем каждую пару (G, N)
из библиотеки и смотрим, верны ли посылки и ложна ли цель.

    cd py && python3 -m algen.library              # сверка бесконечных групп
    python3 -m algen.library --конечные 200        # сверка движка на конечных
"""

import functools
import argparse
import json
import math
import random
import sys
from pathlib import Path
from multiprocessing import Pool

from .finite import FINITE_DERIVED, arith_props, arith_sub_props, load as load_finite, load_aut, load_chars, load_compl, load_endo, load_elts, load_homs, load_hk, load_perm, load_products
from math import gcd

from .logic import DATA, App, Graph, Theory, Var, Vocab


def backbone(s, assume, lits):
    """Для каждого литерала из lits: True, если он следует из assume, False, если
    следует его отрицание, иначе None. Ответ тот же, что у двух вызовов на литерал
    (solve(assume + [-l]), затем solve(assume + [l])), но вызов делается только
    для значения, которого ещё не было ни в одной найденной модели: литерал,
    принимавший в моделях оба значения, не следует ни так, ни так."""
    if not s.solve(assumptions=assume):
        return [True] * len(lits)  # как у двух вызовов: из противоречия следует всё
    seen = [0] * len(lits)  # биты: 1 — был верен в модели, 2 — был ложен

    def see(m):
        n = len(m)
        for i, l in enumerate(lits):
            if type(l) is int:
                v = abs(l)
                seen[i] |= 3 if v > n else 1 if (m[v - 1] > 0) == (l > 0) else 2

    see(s.get_model())
    out = [None] * len(lits)
    for i, l in enumerate(lits):
        if type(l) is not int:  # не номер переменной: как раньше, двумя вызовами
            if not s.solve(assumptions=assume + [-l]):
                out[i] = True
            elif not s.solve(assumptions=assume + [l]):
                out[i] = False
            continue
        if seen[i] == 3:
            continue
        v = seen[i] == 1
        if not s.solve(assumptions=assume + [-l if v else l]):
            out[i] = v
        else:
            see(s.get_model())
    return out

# Числа (сорт Num) в перебора: малые и ∞; BS(m, n) — группы библиотеки
INF = "∞"
NUMS = (1, 2, 3, 4, 5, 6, 7, INF)
BS = {(1, 1): "ZxZ", (1, 2): "BS12", (2, 1): "BS12", (2, 3): "BS23", (3, 2): "BS23"}

INFINITE = DATA / "infinite" / "grp.json"
# Конечные множители произведений сверх малых и простых: A₄, S₄, SL(2, 3) (коммутант Q₈
# неабелев нильпотентен), SL(2, 5) (совершенная с центром).
EXTRA_FINITE = ("12:3", "24:12", "24:3", "120:5",
                # для произведений: ступени 3 (D₁₆, SD₁₆, Q₁₆), группы Гейзенберга порядка 27,
                # неабелевы порядка pq (D₁₀, C₇ ⋊ C₃) — Q₈ × Heis₃ (Z = G′ = C₆) и подобные
                "16:7", "16:8", "16:9", "27:3", "27:4", "10:1", "21:1")
# A(n), S(n), C(n), D(n) (порядка 2n) — ключи SmallGroups (номера: IdGroup(CyclicGroup(n)),
# IdGroup(DihedralGroup(2n)) в GAP). C(∞) и D(∞) не заводятся: в словаре эти группы конечны
_CYC_ID = [1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2]
_DIH_ID = [1, 2, 1, 3, 1, 4, 1, 7, 1, 4, 1, 6, 1, 3, 3, 18, 1, 4, 1, 6, 5, 3, 1, 7, 1, 4, 1, 5, 1, 12, 1, 52, 3, 4, 3, 6, 1, 3, 5, 7, 1, 14, 1, 5, 3, 3, 1, 6, 1, 4]
SMALL_FAMILY = {
    "alt": {1: "1:1", 2: "1:1", 3: "3:1", 4: "12:3", 5: "60:5", 6: "360:118"},
    "sym-n": {1: "1:1", 2: "2:1", 3: "6:1", 4: "24:12", 5: "120:34", 6: "720:763"},
    "cyc": {n: f"{n}:{i}" for n, i in enumerate(_CYC_ID, 1)},
    "dih": {n: f"{2 * n}:{i}" for n, i in enumerate(_DIH_ID, 1)},
}
ALL, ONE = "<всё>", "<1>"  # подгруппы множителя в метках подгрупп произведения
SUB_PROPS = ("normal", "characteristic", "maximal", "whole", "central", "finite-index",
             # арифметика индекса (конечный индекс): 2, простой, наименьший простой делитель |G|;
             # силовская (нетривиальная), холлова (порядок взаимно прост с индексом)
             "index-2", "prime-index", "min-prime-index", "sylow", "hall",
             # есть дополнение B: N ∩ B = 1, NB = G
             "complemented")


class Library:
    def __init__(self, infinite=INFINITE):
        self.obj = {}
        patch = DATA / "finite" / "grp-subs-patch.json"
        patch = json.loads(patch.read_text(encoding="utf-8"))["группы"] if patch.exists() else {}
        compl, endo, elts, homs, perm, hk = (load_compl(), load_endo(), load_elts(), load_homs(), load_perm(),
                                              load_hk())
        for k, r in load_finite(extra=True).items():
            for data, field, prop in ((compl, "complemented", "complemented"),
                                      (endo, "fully_invariant", "fully-invariant"),
                                      (endo, "subnormal", "subnormal")):
                c = data.get(k)
                if c and c.get(field) is not None and r["subs"] is not None and \
                        [[x["group"], x["class_size"]] for x in r["subs"]] == c["check"]:
                    for x, v in zip(r["subs"], c[field]):
                        x["props"][prop] = v
            partial = r["subs"] is None and k in patch
            if partial:
                r = {**r, **patch[k]}
            self.obj[k] = {"key": k, "имя": r["name"], "конечная": True, "свойства": r["props"],
                           "подгруппы": None if r["subs"] is None else [
                               {"id": str(i), "≅": s["group"], "свойства": s["props"],
                                **({"фактор": s["quotient"]} if "quotient" in s else {}),
                                **({"над": [str(x) for x in s["le"]]} if s.get("le") is not None else {}),
                                # номера подгрупп (представители классов сопряжённости)
                                **{f: str(s[k]) for k, f in (("normalizer", "нормализатор"),
                                   ("centralizer", "централизатор"), ("normal_closure", "нормальное замыкание"))
                                   if s.get(k) is not None}}
                               for i, s in enumerate(r["subs"])],
                           "центр": None if r.get("center") is None else str(r["center"]),
                           "коммутант": None if r.get("commutator") is None else str(r["commutator"]),
                           "фраттини": None if r.get("frattini") is None else str(r["frattini"]),
                           **({"подгруппы неполные": True} if partial else {})}
            e = elts.get(k)
            if e and e.get("classes") and r["subs"] is not None and \
                    [[x["group"], x["class_size"]] for x in r["subs"]] == e["check"]:
                self.obj[k]["элементы"] = e["classes"]
            q = hk.get(k)
            if q and q.get("hk") is not None and r["subs"] is not None and \
                    [[x["group"], x["class_size"]] for x in r["subs"]] == q["check"]:
                self.obj[k]["hk"] = (len(r["subs"]), q["hk"])
            q = perm.get(k)
            if q and q.get("nonperm") is not None and r["subs"] is not None and \
                    [[x["group"], x["class_size"]] for x in r["subs"]] == q["check"]:
                self.obj[k]["неперестановочны"] = {tuple(x) for x in q["nonperm"]}
            h = homs.get(k)
            if h and h.get("endos") is not None and r["subs"] is not None and \
                    [[x["group"], x["class_size"]] for x in r["subs"]] == h["check"]:
                self.obj[k]["эндоморфизмы"] = h["endos"]
        self._aut_out()
        self._chars()
        self._props2()
        with open(infinite, encoding="utf-8") as f:
            raw = json.load(f)
            for r in raw["группы"]:
                self.obj[r["id"]] = {"key": r["id"], "конечная": False, **r}
                # Элементы бесконечной группы (классы сопряжённости): ⟨x⟩ и C(x) —
                # по id подгрупп записи; размер класса — 1 у центральных, иначе «много».
                if r.get("элементы"):
                    ids = {x["id"]: i for i, x in enumerate(r.get("подгруппы") or [])}
                    els = []
                    for e in r["элементы"]:
                        e = dict(e)
                        for f in ("gen", "cent"):
                            if isinstance(e.get(f), str):
                                e[f] = ids.get(e[f])
                        e.setdefault("size", 1 if e.get("central") else 2)
                        e.setdefault("ord", 0)
                        if e.get("gen") is None or e.get("cent") is None:
                            raise KeyError(f"{r['id']}: элемент {e.get('имя')}: нет подгруппы ⟨x⟩ или C(x)")
                        els.append(e)
                    self.obj[r["id"]]["элементы"] = els
        # Счётность бесконечных групп — наложением с обоснованием (5.11)
        cnt = infinite.parent / "countable.json"
        if cnt.exists():
            with open(cnt, encoding="utf-8") as f:
                over = json.load(f)
            for field, val in (("счётны", True), ("несчётны", False)):
                for gid, why in over[field].items():
                    if gid not in self.obj:
                        raise KeyError(f"countable.json: нет группы {gid}")
                    o = self.obj[gid]
                    if o["свойства"].get("countable", val) != val:
                        raise ValueError(f"countable.json: {gid} — записано {o['свойства']['countable']}, а здесь {val}")
                    o["свойства"]["countable"] = val
                    o.setdefault("почему", {})["countable"] = why
        # Прочие значения бесконечных групп — наложением с обоснованием (6.11)
        vals = infinite.parent / "values.json"
        if vals.exists():
            with open(vals, encoding="utf-8") as f:
                over = json.load(f)
            for gid, ps in over["значения"].items():
                if gid not in self.obj:
                    raise KeyError(f"values.json: нет группы {gid}")
                o = self.obj[gid]
                for p, (val, why) in ps.items():
                    if o["свойства"].get(p, val) != val:
                        raise ValueError(f"values.json: {gid} {p} — записано {o['свойства'][p]}, а здесь {val}")
                    o["свойства"][p] = val
                    o.setdefault("почему", {})[p] = why
        self.fam = {f["id"]: f for f in raw.get("семейства", [])}
        self._sums()
        self.prod = load_products()
        # Свободные произведения и сплетения: поля записи «свободное произведение»
        # и «сплетение»: [A, B]. Сплетение A ≀ B не симметрично.
        self.fprod, self.wreath = {}, {}
        for k, o in self.obj.items():
            ab = o.get("свободное произведение")
            if ab:
                self.fprod[ab[0], ab[1]] = self.fprod[ab[1], ab[0]] = k
            ab = o.get("сплетение")
            if ab:
                self.wreath[ab[0], ab[1]] = k
        for k, o in self.obj.items():
            for other, p in o.get("произведения", {}).items():
                self.prod[k, other] = self.prod[other, k] = p
        for o in self.obj.values():
            for s in o["подгруппы"] or []:
                for k in (s["≅"], s.get("фактор")):
                    if k is not None and k not in self.obj:
                        raise KeyError(f"{o['key']}/{s['id']}: нет группы {k}")
            if not o["конечная"]:  # ссылки на подгруппы записи должны существовать
                ids = {x["id"] for x in o["подгруппы"] or []}
                for f in ("центр", "коммутант", "фраттини", "кручение"):
                    if o.get(f) is not None and o[f] not in ids:
                        raise KeyError(f"{o['key']}: {f} = {o[f]!r}, такой подгруппы нет")
        self._check_negations()
        for o in self.obj.values():
            self._center_commutator(o)
        self._quantified_props()
        self._finite_subgroup_props()
        for f in self.fam.values():
            self._fam_props(f)
        # Направленные системы: члены, свойства отображений, прямой и обратный пределы.
        self.diag = {f["id"]: f for f in raw.get("системы", [])}
        for f in self.diag.values():
            self._fam_props(f)
            f["свойства"].pop("finite-fam", None)
            for k in ("injective-sys", "surjective-sys", "constant-sys"):
                if f.get(k) is not None:
                    f["свойства"][k] = f[k]

    def _check_negations(self):
        """Поля «≇» и «↪̸» бесконечных групп обходят вывод, поэтому у каждой записи
        должна быть причина в «почему» (ключ «≇ K» или «↪̸ K»), а сама запись не
        должна спорить с библиотекой: «≇» с той же группой, «↪̸» в группу, у
        которой A записана подгруппой, или в группу A вкладывается сама в себя."""
        for k, o in self.obj.items():
            for f in ("≇", "↪̸"):
                for other in o.get(f, ()):
                    if other not in self.obj:
                        raise KeyError(f"{k}: {f} {other}: нет такой группы")
                    if not isinstance(o.get("почему"), dict) or not o["почему"].get(f"{f} {other}"):
                        raise KeyError(f"{k}: {f} {other}: нет причины в «почему»")
                    if other == k:
                        raise ValueError(f"{k}: {f} самой себе")
                    if f == "↪̸" and any(x["≅"] == k for x in self.obj[other]["подгруппы"] or []):
                        raise ValueError(f"{k} ↪̸ {other}, но {k} записана подгруппой {other}")

    SUM_MAX = 24  # ⊕_ℕ H для всех конечных H порядка ⩽ SUM_MAX

    def _sums(self):
        """Прямые суммы ⊕_ℕ H счётного числа копий конечной H ≠ 1, без ручных записей.

        Значения следуют из H: ⊕H ≅ H × ⊕H (разложима, не хопфова и не кохопфова —
        сдвиг слагаемых), периодическая, локально конечная, ф. а., ограниченного
        показателя, не к. п.; абелевость, разрешимость, нильпотентность,
        совершенность, отсутствие центра, p-группа и показатели — как у H.
        Z, G′, Φ и Gᵃᵇ — суммы соответствующих подгрупп и факторов H
        (Φ(A × B) = Φ(A) × Φ(B), поэтому Φ(⊕H) = ⊕Φ(H)). Линейна, если H
        элементарная абелева p-группа (⊕C_p ⊂ (𝔽_p(t), +) ⊂ UT₂), и не линейна,
        если |H| делится на два простых (⊕C_p × ⊕C_q). Уже записанные руками
        суммы (семейства с одним членом) берутся как есть."""
        hand = {f["члены"][0]: f["⊕"] for f in self.fam.values()
                if f.get("бесконечное") and len(f["члены"]) == 1 and f.get("⊕")}
        hand.update({"6:2": "SumC6", "36:2": "SumC36"})
        hand = {h: k for h, k in hand.items() if k in self.obj}
        keys = [k for k, o in list(self.obj.items()) if o["конечная"] and ":" in k and k != "1:1"
                and int(k.split(":")[0]) <= self.SUM_MAX and o.get("подгруппы")]
        key = {h: hand.get(h, f"Sum_{h.replace(':', '_')}") for h in keys}
        key["1:1"] = "1:1"
        copy = ("abelian", "solvable", "nilpotent", "perfect", "centerless", "p-group", "metabelian", "class-2",
                "exponent-2", "exponent-3", "exponent-4", "exponent-6")
        for h in keys:
            if h in hand:
                continue
            o = self.obj[h]
            hp = o["свойства"]
            p = {x: hp[x] for x in copy if hp.get(x) is not None}
            p.update({"trivial": False, "cyclic": False, "finite": False, "fin-gen": False, "free": False,
                      "simple": False, "torsion-free": False, "periodic": True, "divisible": False,
                      "residually-finite": True, "indecomposable": False, "hopfian": False, "co-hopfian": False,
                      "bounded-exponent": True, "polycyclic": False, "amenable": True, "left-orderable": False,
                      "bi-orderable": False, "property-t": False, "locally-finite": True, "locally-cyclic": False,
                      "free-abelian": False, "countable": True})
            # 9.11 (2а.4): ⊕_ℕ H — счётная, не к. п. (два-порождённость, конечная и рекурсивная
            # определённость, разрешимая проблема слов, гиперболичность требуют к. п.); копредставление
            # из таблиц копий H рекурсивно; локально конечна ⇒ без свободных подгрупп.
            # Виртуальные и локальные свойства, свойства собственных подгрупп — как у H:
            # подгруппа конечного индекса содержит почти все копии H; собственная подгруппа
            # H × H × … (без одной копии) бесконечна и нециклична.
            p.update({"rec-pres-ctbl": True, "two-generated": False, "fin-pres": False, "rec-pres": False,
                      "word-problem": False, "hyperbolic": False, "contains-free": False,
                      "proper-subs-cyclic": False, "proper-subs-finite": False})
            for x, y in (("nilpotent", ("virtually-nilpotent", "locally-nilpotent", "proper-subs-nilpotent")),
                         ("solvable", ("virtually-solvable", "locally-solvable")),
                         ("abelian", ("proper-subs-abelian",))):
                if hp.get(x) is not None:
                    for z in y:
                        p[z] = hp[x]
            if hp.get("nilpotent") is not None:
                p["residually-nilpotent"] = hp["nilpotent"]
            if hp.get("abelian") is not None:
                p["dedekind"] = hp["abelian"]
            n = int(h.split(":")[0])
            primes = {q for q in range(2, n + 1) if n % q == 0 and all(q % r for r in range(2, q))}
            if len(primes) >= 2:
                p["linear"] = False
            elif hp.get("abelian") and any(hp.get(f"exponent-{q}") for q in primes):
                p["linear"] = True
            subs = o["подгруппы"]
            by = {x["id"]: x for x in subs}
            c = by.get(o.get("коммутант"))
            if c is not None and self.obj.get(c["≅"]):
                p["metabelian"] = bool(self.obj[c["≅"]]["свойства"].get("abelian"))
                p["class-2"] = bool(c["свойства"].get("central"))
            canon = {}
            for f in ("центр", "коммутант", "фраттини"):
                sid = o.get(f)
                if sid is None or sid not in by:
                    continue
                x = by[sid]
                if x["≅"] == "1:1":
                    canon[f] = "1"
                elif x["свойства"].get("whole"):
                    canon[f] = "все"
                else:
                    canon[f] = f
            out = [{"id": "1", "имя": "1", "≅": "1:1", "свойства": {"normal": True, "characteristic": True,
                    "central": True, "whole": False, "maximal": False, "finite-index": False}, "фактор": key[h]}]
            for f, cid in canon.items():
                if cid != f:
                    continue
                x = by[o[f]]
                fac = x.get("фактор")
                out.append({"id": f, "имя": f"⊕ {f}", "≅": key.get(x["≅"]), "фактор": key.get(fac) if fac else None,
                            "свойства": {"normal": True, "characteristic": True,
                                         "central": bool(x["свойства"].get("central")),
                                         "whole": False, "maximal": False, "finite-index": False}})
            out.append({"id": "все", "имя": "все", "≅": key[h], "фактор": "1:1",
                        "свойства": {"normal": True, "characteristic": True, "central": bool(hp.get("abelian")),
                                     "whole": True, "maximal": False, "finite-index": True}})
            if any(x["≅"] is None for x in out):
                continue
            for x in out:
                if x["фактор"] is None:
                    del x["фактор"]
            ab = None
            if "коммутант" in canon:
                c = canon["коммутант"]
                ab = key[h] if c == "1" else ("1:1" if c == "все" else key.get(by[o["коммутант"]].get("фактор")))
            r = {"id": key[h], "key": key[h], "конечная": False, "синтез сумм": h, "без произведений": True,
                 "имя": f"⊕_ℕ {o.get('имя', h)}", "свойства": p, "подгруппы": out,
                 "произведения": {key[h]: key[h]}, **canon}
            if ab:
                r["абелианизация"] = ab
            self.obj[key[h]] = r
        while True:  # сумма, ссылающаяся на непостроенную, выбрасывается
            bad = [k for k, r in self.obj.items() if r.get("синтез сумм") and (
                any(x["≅"] not in self.obj or x.get("фактор", "1:1") not in self.obj for x in r["подгруппы"])
                or r.get("абелианизация", "1:1") not in self.obj)]
            if not bad:
                break
            for k in bad:
                del self.obj[k]

    def _quantified_props(self):
        """Свойства с квантором по подгруппам («кванторные» в data/new/grp.json):
        у конечной группы с полным списком классов подгрупп — по списку; у
        остальных — «нет», если записанная подгруппа с фильтром не обладает P."""
        patch = DATA / "new" / "grp.json"
        qs = json.loads(patch.read_text(encoding="utf-8")).get("кванторные", []) if patch.exists() else []

        def val(sub, p):
            v = sub["свойства"].get(p)
            if v is None and sub["≅"] in self.obj:
                v = self.obj[sub["≅"]]["свойства"].get(p)
            return v
        for o in self.obj.values():
            subs = o["подгруппы"]
            if not subs:
                continue
            complete = o["конечная"] and not o.get("подгруппы неполные")
            for q in qs:
                if o["свойства"].get(q["id"]) is not None:
                    continue
                verdict, unknown = True, False
                for sub in subs:
                    f = [val(sub, x["p"]) for x in q.get("фильтр", [])]
                    want = [x.get("значение", True) for x in q.get("фильтр", [])]
                    if any(v is not None and v != w for v, w in zip(f, want)):
                        continue
                    pv = val(sub, q["p"])
                    if None in f:
                        if pv is False:
                            unknown = True
                        continue
                    if pv is False:
                        verdict = False
                        break
                    if pv is None:
                        unknown = True
                if verdict is False:
                    o["свойства"][q["id"]] = False
                elif complete and not unknown:
                    o["свойства"][q["id"]] = True

    def finite_subgroup_values(self, o):
        """Свойства конечной группы по полному списку классов подгрупп и коммутанту:
        metabelian (G′ абелев), class-2 (G′ центральна), dedekind (все подгруппы
        нормальны), exponent-2/3 и prime-orders (по порядкам циклических подгрупп),
        clt (подгруппы всех порядков, делящих |G|). None — не вычислить."""
        out = {}
        subs = o.get("подгруппы") or []

        def order(k):
            h = k.split(":")[0] if isinstance(k, str) else ""
            return int(h) if h.isdigit() and self.obj.get(k, {}).get("конечная") else None
        cid = o.get("коммутант")
        cs = next((x for x in subs if x["id"] == cid), None) if cid is not None else None
        if cs is not None:
            ab = self.obj.get(cs["≅"], {}).get("свойства", {}).get("abelian")
            if ab is not None:
                out["metabelian"] = ab
            if cs["свойства"].get("central") is not None:
                out["class-2"] = cs["свойства"]["central"]
        if not o["конечная"]:
            return out
        # классы сопряжённых элементов (если посчитаны): порядки всех элементов — точно
        els = o.get("элементы")
        if els:
            eo = [c.get("ord") for c in els]
            if None not in eo and 0 not in eo:
                out["exponent-2"] = all(m in (1, 2) for m in eo)
                out["exponent-3"] = all(m in (1, 3) for m in eo)
                out["prime-orders"] = all(m == 1 or _is_prime(m) for m in eo)
        if o.get("подгруппы неполные") or not subs:
            # неполный список: только опровержения по записанным подгруппам
            for x in subs:
                m, c = order(x["≅"]), self.obj.get(x["≅"], {}).get("свойства", {}).get("cyclic")
                if x["свойства"].get("normal") is False:
                    out["dedekind"] = False
                if c and m is not None:
                    if m not in (1, 2):
                        out.setdefault("exponent-2", False)
                    if m not in (1, 3):
                        out.setdefault("exponent-3", False)
                    if m != 1 and not _is_prime(m):
                        out.setdefault("prime-orders", False)
            return out
        n = order(o["key"])
        ords = [order(x["≅"]) for x in subs]
        cyc = [self.obj.get(x["≅"], {}).get("свойства", {}).get("cyclic") for x in subs]
        if n is None or None in ords or None in cyc:
            return out
        corder = [m for m, c in zip(ords, cyc) if c]
        normal = [x["свойства"].get("normal") for x in subs]
        if None not in normal:
            out["dedekind"] = all(normal)
        for p, v in (("exponent-2", all(m in (1, 2) for m in corder)),
                     ("exponent-3", all(m in (1, 3) for m in corder)),
                     ("prime-orders", all(m == 1 or _is_prime(m) for m in corder))):
            if out.setdefault(p, v) != v:
                raise ValueError(f"{o['key']}: {p} по элементам и по подгруппам расходятся")
        have = set(ords)
        out["clt"] = all(d in have for d in range(1, n + 1) if n % d == 0) if n <= 10 ** 6 else None
        return {k: v for k, v in out.items() if v is not None}

    def _finite_subgroup_props(self):
        """Заполнить неизвестные значения finite_subgroup_values и таблицы GAP
        (finite.load_props); записанные не трогаются, расхождение — ошибка данных."""
        from .finite import load_props
        gap = load_props()
        for o in self.obj.values():
            if o.get("синтез"):
                continue
            vals = dict(gap.get(o["key"], {}))
            for p, v in self.finite_subgroup_values(o).items():
                if vals.setdefault(p, v) != v:
                    raise ValueError(f"{o['key']}: {p} по GAP {vals[p]}, по подгруппам {v}")
            for p, v in vals.items():
                have = o["свойства"].get(p)
                if have is None:
                    o["свойства"][p] = v
                elif have != v:
                    raise ValueError(f"{o['key']}: {p} записано {have}, по подгруппам {v}")

    def _fam_props(self, f):
        """Свойство семейства — у всех членов: да, если у всех да; нет, если у
        кого-то нет; иначе неизвестно. finite-fam — конечно ли семейство."""
        ms = [self.obj[k] for k in f["члены"] if k in self.obj]
        props = {"finite-fam": not f["бесконечное"]}
        for p in LIB_GROUP_PROPS:
            vs = [m["свойства"].get(p) for m in ms]
            props[p] = False if False in vs else True if vs and None not in vs else None
        f["свойства"] = {k: v for k, v in props.items() if v is not None}

    def _aut_out(self):
        """Aut(G) и Out(G) конечных групп таблицы (data/finite/grp-aut.jsonl,
        считает GAP). Группа вне таблицы заводится записью только со свойствами."""
        for k, r in load_aut().items():
            o = self.obj.get(k)
            if o is None:
                continue
            self._apply_aut(k, o, r)

    def _apply_aut(self, k, o, r):
        """Запись GAP об Aut, Inn, Out группы k (o — её запись в библиотеке)."""
        if True:
            for fld, name in (("aut", r.get("aut_name")), ("out", None)):
                ak = r.get(fld)
                if not ak or ak not in self.obj:
                    ak = ak or f"{r[fld + '_order']}:{fld.capitalize()}({k})"
                    if ak not in self.obj:
                        props = dict(r[fld + "_props"])
                        for p, f in FINITE_DERIVED.items():
                            props.setdefault(p, f(props))
                        for p, v in arith_props(r[fld + "_order"]).items():
                            props.setdefault(p, v)
                        self.obj[ak] = {"key": ak, "имя": name or ak, "конечная": True, "свойства": props,
                                        "подгруппы": None, "без произведений": True,
                                        # ключ не из SmallGroups: другой ключ может быть той же группой
                                        **({} if r.get(fld) else {"неканонический": True})}
                o[fld] = ak
            o["inn = aut"] = r["inn_whole"]
            o["inn центральна"] = r["inn_central"]
            o["|Aut|"], o["|Out|"] = r["aut_order"], r["out_order"]

    PROPS2 = ("two-generated", "clt", "dedekind", "prime-orders", "proper-subs-abelian",
              "proper-subs-nilpotent", "proper-subs-cyclic", "metabelian", "class-2", "exponent-4",
              "exponent-6")

    def _props2(self):
        """Свойства конечных групп, посчитанные GAP (gap/props2.g →
        data/finite/grp-props2.jsonl): ранг d(G) в поле «ранг» и свойства PROPS2.
        Значение, расходящееся с уже записанным, — ошибка (ни одно не затирается)."""
        from .finite import load_props2
        for k, r in load_props2().items():
            o = self.obj.get(k)
            if o is None or not o.get("конечная"):
                continue
            pr = o.setdefault("свойства", {})
            for p in self.PROPS2:
                v = r.get(p)
                if v is None:
                    continue
                if pr.get(p) is not None and pr[p] != v:
                    raise ValueError(f"grp-props2.jsonl: {k} {p} = {v}, а в библиотеке {pr[p]}")
                pr[p] = v
            if isinstance(r.get("exponent"), int):
                # экспонента exp(G) — число (конструкция exponent); сверка с порядками классов
                els = o.get("элементы")
                if els:
                    lcm = 1
                    for c in els:
                        lcm = lcm * c["ord"] // gcd(lcm, c["ord"])
                    if lcm != r["exponent"]:
                        raise ValueError(f"grp-props2.jsonl: {k} экспонента {r['exponent']}, а по классам {lcm}")
                o["экспонента"] = r["exponent"]
            if r.get("rank_exact"):
                if o.get("ранг") is not None and o["ранг"] != r["rank"]:
                    raise ValueError(f"grp-props2.jsonl: {k} ранг {r['rank']}, а в библиотеке {o['ранг']}")
                o["ранг"] = r["rank"]

    def _chars(self):
        """Конечные группы без таблицы подгрупп (порядок > 100): подгруппы 1, Z, G′,
        Φ, G с факторами и Aut/Out — data/finite/grp-chars.jsonl (считает GAP,
        `finite.py --характеристические`). Список подгрупп неполный. Группа,
        которой нет в библиотеке, заводится записью только со свойствами."""
        for k, r in load_chars().items():
            o = self.obj.get(k)
            if o is None or o["подгруппы"] is not None:
                continue
            n = r["order"]

            def obj_of(order, key, props, name):
                if order == 1:
                    return "1:1"
                if order == n:
                    return k
                if key and key in self.obj:
                    return key
                ak = key or name
                if ak not in self.obj:
                    props = dict(props)
                    for p, f in FINITE_DERIVED.items():
                        props.setdefault(p, f(props))
                    for p, v in arith_props(order).items():
                        props.setdefault(p, v)
                    self.obj[ak] = {"key": ak, "имя": ak, "конечная": True, "свойства": props,
                                    "подгруппы": None, "без произведений": True,
                                    **({} if key else {"неканонический": True})}
                return ak
            role = {r["center"]: "Z", r["commutator"]: "G′", r["frattini"]: "Φ"}
            subs = []
            for i, x in enumerate(r["subs"]):
                name = role.get(i, str(i))
                g = obj_of(x["order"], x["group"], x["gprops"], f"{x['order']}:{name}({k})")
                q = obj_of(x["qorder"], x["quotient"], x["qprops"], f"{x['qorder']}:{k}/{name}")
                props = dict(x["props"])
                # нормальная H максимальна ⇔ |G/H| простое (chars.g до 1.11 писал «G/H проста»)
                props["maximal"] = arith_props(x["qorder"])["prime-order"]
                for p, v in arith_sub_props(n, x["order"]).items():
                    props.setdefault(p, v)
                subs.append({"id": str(i), "≅": g, "свойства": props, "фактор": q, "над": [str(j) for j in x["le"]]})
            o["подгруппы"] = subs
            o["подгруппы неполные"] = True
            o["центр"], o["коммутант"], o["фраттини"] = str(r["center"]), str(r["commutator"]), str(r["frattini"])
            if "aut_order" in r and "aut" not in o:
                self._apply_aut(k, o, r)

    @staticmethod
    def _center_commutator(o):
        """Центр и коммутант, которые следуют из свойств группы: у абелевой
        центр — вся группа, коммутант — 1; у совершенной (и у простой
        неабелевой) коммутант — вся группа; у группы без центра центр — 1."""
        subs = o["подгруппы"] or []
        one = next((x["id"] for x in subs if x["≅"] == "1:1"), None)
        whole = next((x["id"] for x in subs if x["свойства"].get("whole")), None)
        p = o["свойства"]
        simple = p.get("simple") and p.get("abelian") is False
        if o.get("центр") is None:
            o["центр"] = whole if p.get("abelian") else one if p.get("centerless") or simple else None
        if o.get("коммутант") is None:
            o["коммутант"] = one if p.get("abelian") else whole if p.get("perfect") or simple else None
        if o.get("кручение") is None:
            # периодическая — кручение вся группа, без кручения — 1 (у любой, не только абелевой)
            o["кручение"] = whole if p.get("periodic") else one if p.get("torsion-free") else None
        for f in ("центр", "коммутант", "кручение"):
            if f in o and o[f] is None:
                del o[f]

    def sym_key(self, card):
        """Ключ записи Sym(X) по мощности X: card — порядок конечной X (int) или
        "ctbl" / "unctbl" для бесконечной счётной / несчётной. Sₙ при n ⩽ 6 — группы
        SmallGroups; при n ⩾ 7 и для бесконечных X — синтетические записи (создаются
        по требованию). Значения — только теоремы (5.11):
        Sₙ, n ⩾ 7: конечна, |Sₙ| = n!; Z = 1 (n ⩾ 3); Sₙ′ = Aₙ простая (n ⩾ 5) —
        не разрешима, не нильпотентна, не проста, не совершенна (Sₙ/Aₙ = C₂),
        неразложима (нормальные подгруппы — 1, Aₙ, Sₙ), 2-порождена ((12), (12…n));
        экспонента НОК(1..n) — не 2, 3, 4, 6; |Sₙ| делится на 2, 3, 5, 7 — не pᵃqᵇ;
        CLT-группы разрешимы — не CLT; конечная аппроксимируема нильпотентными ⇔
        нильпотентна — нет; Sₙ₋₁ — собственная неабелева, не нильпотентная, не
        циклическая. Конечные группы: периодичны, ограниченной экспоненты, локально
        конечны, финитно аппроксимируемы, линейны (и над ℂ), конечно определены,
        хопфовы и кохопфовы, гиперболичны, со свойством (T), с композиционным
        рядом, почти нильпотентны, полиномиального роста, аменабельны, без
        свободных подгрупп, не упорядочиваемы (есть кручение), все подгруппы конечны.
        Sym(ℕ) (только счётные X: при несчётных мощность Ω не записана, а один ключ
        значил бы изоморфизм). Sym(Ω), Ω бесконечно: |Sym(Ω)| = 2^|Ω| — несчётна, не конечно порождена;
        Z = 1; не проста (финитарные перестановки — собственная нормальная);
        совершенна (Ore 1951: каждый элемент — коммутатор); нормальные подгруппы
        (Baer–Schreier–Ulam) — цепь, Alt(Ω) в каждой нетривиальной — неразложима;
        подгруппа конечного индекса содержит нормальную конечного индекса, а
        собственные нормальные — ограниченного носителя, бесконечного индекса: нет
        собственных подгрупп конечного индекса — без конечных факторов, не финитно
        аппроксимируема, почти нильпотентна (разрешима) ⇔ нильпотентна (разрешима) —
        нет; содержит каждую группу мощности ⩽ |Ω| (Кэли): F₂ и все Sₙ — не
        аменабельна, не локально разрешима, не линейна над ℂ (Жордан); сдвиг на
        ℤ ⊂ Ω — элемент бесконечного порядка: не периодична, не ограниченной
        экспоненты, не локально конечна, не p-группа и т. п.; транспозиция — не
        квадрат (у квадрата число циклов длины 2 чётно или бесконечно) — не делима;
        совершенная нетривиальная — не аппроксимируема нильпотентными; стабилизатор
        точки — собственная бесконечная (≅ Sym(Ω)) неабелева подгруппа."""
        from math import factorial
        if isinstance(card, int):
            if card <= 6:
                k = SMALL_FAMILY["sym-n"].get(card)
                return k if k in self.obj else None
            # Sym(Sym(X)) даёт card = n!: десятичная запись больших чисел запрещена
            # (sys.int_info, 4300 цифр) — ключ тогда в шестнадцатеричной
            key = f"Sym({card})" if card < 10 ** 60 else f"Sym(0x{card:x})"
            if key not in self.obj:
                yes = dict.fromkeys((
                    "finite", "periodic", "bounded-exponent", "locally-finite", "residually-finite",
                    "linear", "linear-c", "fin-gen", "fin-pres", "rec-pres", "word-problem", "countable",
                    "hopfian", "co-hopfian", "hyperbolic", "property-t", "comp-series",
                    "virtually-nilpotent", "virtually-solvable", "polynomial-growth", "amenable",
                    "proper-subs-finite", "centerless", "indecomposable", "two-generated"), True)
                no = dict.fromkeys((
                    "trivial", "abelian", "cyclic", "nilpotent", "class-2", "dedekind", "solvable",
                    "metabelian", "polycyclic", "simple", "perfect", "free", "free-abelian",
                    "torsion-free", "divisible", "no-finite-quotients", "contains-free", "left-orderable",
                    "bi-orderable", "exponent-2", "exponent-3", "exponent-4", "exponent-6",
                    "prime-orders", "clt", "p-group", "prime-order", "order-p2", "order-pq",
                    "two-primes", "odd-order", "residually-nilpotent", "locally-cyclic",
                    "locally-nilpotent", "locally-solvable", "proper-subs-abelian",
                    "proper-subs-nilpotent", "proper-subs-cyclic"), False)
                # «неканонический»: разные ключи конечных групп таблицы — «не изоморфны»;
                # для синтетической записи это не доказано (та же Sₙ может быть в
                # библиотеке под другим ключом) — решают свойства и порядок
                self.obj[key] = {"key": key, "имя": key.replace("Sym(", "S(", 1), "конечная": True, "синтез": True,
                                 "без произведений": True, "неканонический": True, "ранг": 2,  # Sₙ, n ⩾ 3: (1 2), (1 … n)
                                 # n! записывается при n ⩽ 150: порядок печатают (num-термы)
                                 "порядок": factorial(card) if card <= 150 else None,
                                 "свойства": {**yes, **no}, "почему": {}, "подгруппы": None}
            return key
        if card != "ctbl":
            # несчётные Ω разной мощности дают неизоморфные Sym(Ω), а один ключ —
            # это «изоморфны» в фактах строки: образа нет
            return None
        key = "Sym(ℕ)"
        base = "SymN" if "SymN" in self.obj else None  # запись Sym(ℕ) из data/infinite/grp.json
        yes = dict.fromkeys(("centerless", "perfect", "indecomposable", "no-finite-quotients",
                             "contains-free"), True)
        no = dict.fromkeys((
            "finite", "countable", "fin-gen", "two-generated", "fin-pres", "trivial", "abelian",
            "cyclic", "nilpotent", "class-2", "dedekind", "solvable", "metabelian", "polycyclic",
            "simple", "free", "free-abelian", "torsion-free", "periodic", "bounded-exponent",
            "locally-finite", "residually-finite", "virtually-nilpotent", "virtually-solvable",
            "amenable", "locally-solvable", "locally-nilpotent", "locally-cyclic", "linear-c",
            "divisible", "residually-nilpotent", "exponent-2", "exponent-3", "exponent-4",
            "exponent-6", "prime-orders", "clt", "p-group", "prime-order", "order-p2", "order-pq",
            "two-primes", "odd-order", "proper-subs-abelian", "proper-subs-nilpotent",
            "proper-subs-cyclic", "proper-subs-finite"), False)
        vals = {**yes, **no}
        if base is not None:
            # дописать недостающее в запись библиотеки; расхождение — ошибка данных
            props = self.obj[base]["свойства"]
            for q, v in vals.items():
                if props.get(q, v) != v:
                    raise ValueError(f"sym_key: SymN.{q} = {props[q]}, а по теореме {v}")
                props.setdefault(q, v)
            return base
        if key not in self.obj:
            self.obj[key] = {"key": key, "имя": key, "конечная": False, "синтез": True,
                             "без произведений": True, "свойства": vals, "почему": {},
                             "подгруппы": None}
        return key

    def amalgam_sym_key(self, d):
        """Запись Sym(X) ∗_X Sym(X) = pushout(cayley X, cayley X) (вложения Кэли).
        Ключ — свой у каждой X (один ключ значил бы изоморфизм). |X| ⩽ 2 и X без
        записи Sym — не здесь (см. _image). Значения — теоремы (5.11):
        Собственная амальгама A ∗_C B (C ≠ A, B): Z ⊆ Z(A) ∩ Z(B) ∩ C — у Sym(X)
        центр тривиален (|X| ⩾ 3): без центра; бесконечна (элемент ab, a ∈ A∖C,
        b ∈ B∖C, бесконечного порядка — не периодична, не локально конечна, не
        ограниченной экспоненты); содержит A, B: есть кручение (транспозиции) — не
        без кручения, не свободна, не упорядочиваема, в K[G] есть делители нуля;
        S₃ ⩽ A — не локально циклична, не дедекиндова, не абелева.
        |X| = 3: S₃ ∗_{C₃} S₃ — оба индекса 2, C₃ нормальна, фактор C₂ ∗ C₂ = D∞;
        C₃ × ℤ — абелева индекса 2: почти абелева, полициклическая, разрешима,
        аменабельна, конечно определена, финитно аппроксимируема, линейна (и над ℂ),
        хопфова, гиперболична (почти ℤ), без F₂; бесконечная аменабельная — без (T);
        не нильпотентна (фактор D∞), не совершенна, не проста.
        |X| = n ⩾ 4 (конечная): амальгама двух конечных групп с индексами (n−1)! ⩾ 6 —
        почти свободна (Karrass–Pietrowski–Solitar): конечно порождена и определена,
        финитно аппроксимируема, хопфова, линейна (и над ℂ), гиперболична, словарная
        проблема разрешима; индексы ⩾ 3 и ⩾ 2 — содержит F₂: не аменабельна, не
        разрешима (и не локально), не почти нильпотентна/разрешима, не полиномиального
        роста; действует на дереве Басса–Серра без неподвижной точки — без (T);
        Gᵃᵇ ↠ C₂ (знак) — не совершенна; нетривиальная финитно аппроксимируемая — не
        проста, не делима, с конечными факторами.
        X бесконечная счётная: Sym(ℕ) ∗_X Sym(ℕ) — содержит Sym(ℕ): несчётна, не
        конечно порождена; не финитно аппроксимируема, не аппроксимируема
        нильпотентными, не локально конечна, не ограниченной экспоненты, не почти
        разрешима (всё это наследуют подгруппы, а у Sym(ℕ) этого нет); содержит F₂ —
        не аменабельна."""
        o = self.obj.get(d)
        key = f"Sym∗Sym над {d}"
        if key in self.obj:
            return key
        fin_ord = None
        if o is not None and o.get("конечная"):
            head = d.split(":")[0]
            fin_ord = int(head) if head.isdigit() else o.get("порядок")
        common_no = ("finite", "trivial", "abelian", "cyclic", "nilpotent", "class-2", "dedekind",
                     "torsion-free", "free", "free-abelian", "simple", "left-orderable", "bi-orderable",
                     "kaplansky", "periodic", "bounded-exponent", "locally-finite", "exponent-2",
                     "exponent-3", "exponent-4", "exponent-6", "prime-orders", "clt", "p-group",
                     "prime-order", "order-p2", "order-pq", "two-primes", "odd-order", "locally-cyclic")
        if fin_ord == 3:
            yes = ("centerless", "virtually-nilpotent", "virtually-solvable", "polynomial-growth",
                   "polycyclic", "solvable", "amenable", "fin-gen", "fin-pres", "rec-pres", "word-problem",
                   "countable", "residually-finite", "linear", "linear-c", "hopfian", "hyperbolic")
            no = common_no + ("contains-free", "property-t", "perfect", "divisible", "no-finite-quotients")
        elif fin_ord is not None and fin_ord >= 4:
            yes = ("centerless", "fin-gen", "fin-pres", "rec-pres", "word-problem", "countable",
                   "residually-finite", "hopfian", "linear", "linear-c", "hyperbolic", "contains-free")
            no = common_no + ("amenable", "solvable", "locally-solvable", "virtually-nilpotent",
                              "virtually-solvable", "polynomial-growth", "polycyclic", "metabelian",
                              "locally-nilpotent", "property-t", "perfect", "divisible", "no-finite-quotients")
        elif o is not None and o["свойства"].get("finite") is False and o["свойства"].get("countable"):
            yes = ("centerless", "contains-free")
            no = common_no + ("countable", "fin-gen", "two-generated", "fin-pres", "residually-finite",
                              "residually-nilpotent", "virtually-solvable", "virtually-nilpotent", "amenable",
                              "solvable", "polycyclic", "metabelian", "locally-solvable", "locally-nilpotent",
                              "polynomial-growth")
        else:
            return None
        self.obj[key] = {"key": key, "имя": key, "конечная": False, "синтез": True, "без произведений": True,
                         "неканонический": True, "свойства": {**dict.fromkeys(yes, True), **dict.fromkeys(no, False)},
                         "почему": {}, "подгруппы": None}
        return key

    def infinite(self):
        return [k for k, o in self.obj.items() if not o["конечная"]]

    def synthesize_products(self, vocab, max_order=8):
        """Добавить прямые произведения A × B для бесконечных A и B из
        библиотеки и малых конечных (хотя бы один множитель бесконечен).

        Значения A × B не записываются рукой: решатель выводит их из значений
        множителей по правилам базы, неизвестное остаётся неизвестным.
        Подгруппы произведения — 1, A × 1, 1 × B, всё, а также H × B и A × K
        для записанных подгрупп H ⩽ A и K ⩽ B; их свойства вложения следуют
        из устройства прямого произведения."""
        g = Graph(vocab)
        X, Y = g.var("X", "Grp.obj"), g.var("Y", "Grp.obj")
        P = g.given(g.make("prod", [X, Y]))
        T = Theory(g, grow=1)
        s = T.solver()
        base = [k for k, o in self.obj.items() if not o.get("синтез") and not o.get("без произведений") and (
            not o["конечная"] or 1 < int(k.split(":")[0]) <= max_order or k in EXTRA_FINITE
            or (o["свойства"].get("simple") and not o["свойства"].get("abelian")))]
        prime_cyclic = {k for k, o in self.obj.items() if o["конечная"] and o["свойства"].get("simple")
                        and o["свойства"].get("abelian")}

        def small(a, b):
            oa, ob = self.obj[a], self.obj[b]
            return oa["конечная"] and ob["конечная"] and int(a.split(":")[0]) * int(b.split(":")[0]) <= 100

        def product(a, b):
            """Ключ A × B: из таблицы, из библиотеки или построенный заново."""
            if (a, b) in self.prod:
                return self.prod[a, b]
            if a == "1:1" or b == "1:1":
                return b if a == "1:1" else a
            if small(a, b):
                return None  # такое произведение есть в таблице GAP, но не размечено
            oa, ob = self.obj[a], self.obj[b]
            key = f"{a}×{b}"
            assume = []
            for t, o in ((X, oa), (Y, ob)):
                for p, v in o["свойства"].items():
                    l = T.lit(("p", p, t), v)
                    if l not in (None, False):
                        assume.append(l)
            if not s.solve(assumptions=assume):
                raise ValueError(f"{key}: значения множителей противоречат базе")
            props = {}
            pl = [(p, l) for p in LIB_GROUP_PROPS if type(l := T.lit(("p", p, P))) is int]
            for (p, _), v in zip(pl, backbone(s, assume, [l for _, l in pl])):
                if v is not None:
                    props[p] = v
            # конечное × конечное: порядок известен, арифметика порядка — из него
            if oa["конечная"] and ob["конечная"]:
                n = int(a.split(":")[0]) * int(b.split(":")[0])
                for p, v in arith_props(n).items():
                    if props.get(p, v) != v:
                        raise ValueError(f"{key}: {p} выведено {props[p]}, а по порядку {n} — {v}")
                    props[p] = v
            marks = {m: sorted(set(oa.get(m, [])) | set(ob.get(m, []))) for m in MARKS}

            def factor(own, other, okey, name):
                swap = {"characteristic": False} if a == b and not oa["свойства"].get("trivial") else {}
                return {"id": name, "имя": name, "≅": own, "фактор": okey,
                        "пара": (ALL, ONE) if name == "A × 1" else (ONE, ALL),
                        "свойства": {**swap, "normal": True, "whole": False,
                                     "finite-index": bool(other["свойства"].get("finite")),
                                     "maximal": okey in prime_cyclic,
                                     **central(self.obj[own]["свойства"].get("abelian"))}}
            self.obj[key] = {
                "key": key, "имя": f"{oa.get('имя', a)} × {ob.get('имя', b)}", "конечная": False,
                "синтез": True, "свойства": props, **marks, "почему": {},
                "подгруппы": [
                    {"id": "1", "≅": "1:1", "фактор": key, "пара": (ONE, ONE),
                     "свойства": {"normal": True, "characteristic": True, "maximal": False, "whole": False,
                                  "central": True, "finite-index": bool(props.get("finite"))}},
                    factor(a, ob, b, "A × 1"), factor(b, oa, a, "1 × B"),
                    {"id": "все", "≅": key, "фактор": "1:1", "пара": (ALL, ALL),
                     "свойства": {"normal": True, "characteristic": True, "maximal": False, "whole": True,
                                  "finite-index": True}}]}
            self._center_commutator(self.obj[key])
            self.prod[a, b] = self.prod[b, a] = key
            built.append((a, b, key))
            return key

        def central(v):
            return {"central": True} if v else {"central": False} if v is False else {}

        made, built = [], []
        for i, a in enumerate(base):
            for b in base[i:]:
                if (a, b) in self.prod or small(a, b):
                    continue
                made.append((a, b, product(a, b)))
        s.delete()
        # H × B и A × K: подгруппы множителя, умноженные на другой множитель.
        # Новые произведения H × B строятся здесь же, но своих H × B не получают.
        # Ещё H × 1 для ненормальных H и диагональ в A × A.
        s = T.solver()
        for a, b, key in made:
            subs = self.obj[key]["подгруппы"]
            if a == b and not self.obj[a]["свойства"].get("trivial", True):
                ap = self.obj[a]["свойства"]
                ab = ap.get("abelian")
                # Диагональ нормальна (и центральна) ровно для абелевой A, не
                # характеристична: (x, y) ↦ (x, xy) или сопряжение во втором
                # множителе её сдвигают. Для простой A она максимальна: H ⊋ Δ
                # пересекает A × 1 по подгруппе, нормализуемой Δ, то есть
                # нормальной в A; для абелевой A фактор A × A / Δ ≅ A.
                diag = {"id": "диагональ", "≅": a,
                        "свойства": {"normal": ab, "characteristic": False, "whole": False,
                                     **central(ab), "maximal": ap.get("simple"),
                                     "finite-index": ap.get("finite")}}
                if ab:
                    diag["фактор"] = a
                diag["свойства"] = {k: v for k, v in diag["свойства"].items() if v is not None}
                subs.insert(len(subs) - 1, diag)
            for own, other, side in ((a, b, 0), (b, a, 1)):
                if a == b and side == 1:
                    continue  # те же подгруппы с точностью до перестановки множителей
                for h in self.obj[own]["подгруппы"] or []:
                    hp = h["свойства"]
                    if hp.get("whole") or h["≅"] == "1:1":
                        continue
                    iso = product(h["≅"], other) if side == 0 else product(other, h["≅"])
                    if iso is None:
                        continue
                    op = self.obj[other]["свойства"]
                    # Номера подгрупп конечных групп («1») не путать с «1 × B».
                    hid = f"№{h['id']}" if h["id"].isdigit() else h["id"]
                    rec = {"id": f"{hid} × B" if side == 0 else f"A × {hid}", "≅": iso,
                           "пара": (h["id"], ALL) if side == 0 else (ALL, h["id"]),
                           "свойства": {"normal": hp.get("normal"), "whole": False,
                                        "maximal": hp.get("maximal"),
                                        "finite-index": hp.get("finite-index"),
                                        **central(hp.get("central") and op.get("abelian")
                                                  if hp.get("central") is not False and op.get("abelian") is not False
                                                  else False)}}
                    if hp.get("normal") is False:
                        rec["свойства"]["characteristic"] = False
                    if hp.get("normal") and h.get("фактор"):
                        rec["фактор"] = h["фактор"]
                    rec["свойства"] = {k: v for k, v in rec["свойства"].items() if v is not None}
                    subs.insert(len(subs) - 1, rec)
                    if hp.get("normal") is False:
                        # H × 1 — тоже не нормальна, не максимальна (H × 1 ⊊ H × B),
                        # бесконечного индекса, если A × B бесконечна по B или H.
                        subs.insert(len(subs) - 1, {
                            "id": f"{hid} × 1" if side == 0 else f"1 × {hid}", "≅": h["≅"],
                            "пара": (h["id"], ONE) if side == 0 else (ONE, h["id"]),
                            "свойства": {"normal": False, "characteristic": False, "whole": False,
                                         "maximal": False, "central": False,
                                         **({"finite-index": False} if hp.get("finite-index") is False
                                            or op.get("finite") is False else {})}})
        # Центр и коммутант: Z(A × B) = Z(A) × Z(B), (A × B)′ = A′ × B′ — для
        # всех построенных произведений, в том числе построенных здесь же.
        i = 0
        while i < len(built):
            a, b, key = built[i]
            i += 1
            o = self.obj[key]
            subs = o["подгруппы"]
            pairs = {x["пара"]: x["id"] for x in subs if "пара" in x}
            # Кручение абелевой: T(A × B) = T(A) × T(B).
            for field in ("центр", "коммутант", "кручение"):
                sa, sb = (self._sub(k, self.obj[k].get(field)) for k in (a, b))
                if sa is None or sb is None:
                    continue
                pair = (self._norm(sa), self._norm(sb))
                if pair in pairs:
                    o[field] = pairs[pair]
                    continue
                iso = product(sa["≅"], sb["≅"])
                if iso is None:
                    continue
                pa, pb = sa["свойства"], sb["свойства"]
                both = lambda p: (pa.get(p) and pb.get(p)) if None not in (pa.get(p), pb.get(p)) else None
                rec = {"id": field, "≅": iso, "пара": pair,
                       "свойства": {"normal": True, "characteristic": True, "whole": False,
                                    "central": True if field == "центр" else both("central"),
                                    "finite-index": both("finite-index"),
                                    # A × K максимальна ровно при максимальной K; при
                                    # собственных нормальных обоих множителях — нет.
                                    "maximal": pb.get("maximal") if pair[0] == ALL else
                                    pa.get("maximal") if pair[1] == ALL else False}}
                rec["свойства"] = {k: v for k, v in rec["свойства"].items() if v is not None}
                if sa.get("фактор") and sb.get("фактор"):
                    q = product(sa["фактор"], sb["фактор"])
                    if q:
                        rec["фактор"] = q
                subs.insert(len(subs) - 1, rec)
                pairs[pair] = field
                o[field] = field
        s.delete()
        return len(made)

    def rank_products(self):
        """Двупорождённость построенных A × B по рангу (Search._key_rank): d ⩽ 2.
        Расхождение с выведенным значением — ошибка."""
        sc = Search.__new__(Search)
        sc.lib = self
        for k in set(self.prod.values()):
            o = self.obj.get(k)
            if o is None:
                continue
            r = sc._key_rank(k)
            if r is None or r == INF:
                continue
            pr = o["свойства"]
            v = r <= 2
            if pr.get("two-generated") is not None and pr["two-generated"] != v:
                raise ValueError(f"{k}: ранг {r}, а two-generated = {pr['two-generated']}")
            pr["two-generated"] = v

    def saturate(self, workers=None, rounds=3):
        """Дописать в записи бесконечных групп значения, которые следуют по
        базе из записанных (самой группы, её подгрупп, центра, коммутанта и
        факторов). Свойство группы получает пометку, если без помеченных
        значений не выводится; свойства вложения подгрупп — только без
        пометок. Повторяется, пока что-то дописывается (не больше rounds раз),
        ведь выведенное у одной группы пригодится там, где она подгруппа."""
        global _LIB
        added = 0
        for _ in range(rounds):
            _LIB = self
            with Pool(workers, initializer=_init_scene) as pool:
                res = pool.map(_saturate, list(jobs(self, self.infinite())), chunksize=4)
            best = {}
            subs = []
            for key, sub, grp, emb in res:
                for prop, (v, mark) in grp.items():
                    old = best.get((key, prop))
                    if old is None or MARKS_ORDER[mark] < MARKS_ORDER[old[1]]:
                        best[key, prop] = (v, mark)
                subs += [(key, sub, prop, v) for prop, v in emb.items()]
            n = 0
            for (key, prop), (v, mark) in best.items():
                o = self.obj[key]
                if prop in o["свойства"]:
                    continue
                o["свойства"][prop] = v
                if mark:
                    o[mark] = sorted(set(o.get(mark, [])) | {prop})
                why = o.setdefault("почему", {})
                if isinstance(why, dict):
                    why.setdefault(prop, "выведено по базе из записанных значений")
                n += 1
            for key, sub, prop, v in subs:
                props = self.obj[key]["подгруппы"][sub]["свойства"]
                if prop not in props:
                    props[prop] = v
                    n += 1
            added += n
            if not n:
                break
        for o in self.obj.values():
            self._center_commutator(o)
        return added

    def _sub(self, key, sid):
        if sid is None:
            return None
        return next((x for x in self.obj[key]["подгруппы"] or [] if x["id"] == sid), None)

    @staticmethod
    def _norm(sub):
        """Подгруппа множителя для пары в произведении: вся, тривиальная или своя."""
        if sub["свойства"].get("whole"):
            return ALL
        return ONE if sub["≅"] == "1:1" else sub["id"]


# --- сцена G, N, G/N -----------------------------------------------------------


class Scene:
    """Граф «G, N ⩽ G, G/N» и его теория; собирается один раз на процесс."""

    def __init__(self, vocab):
        g = Graph(vocab)
        self.G = g.var("G", "Grp.obj")
        self.N = g.var("N", "Grp.sub", ambient=self.G)
        self.Q = g.given(g.make("quotient", [self.G, self.N]))
        self.Z = g.make("center", [self.G])
        self.C = g.make("commutator", [self.G])
        self.v = vocab
        self.T = Theory(g, grow=1)
        self.s = self.T.solver()

    def facts(self, lib, key, sub):
        """Записанные значения пары (G, N): {атом: (значение, откуда)}."""
        o, out = lib.obj[key], {}

        def put(prop, t, props, where):
            if prop in props:
                out[("p", prop, t)] = (props[prop], where)

        for p in LIB_GROUP_PROPS:
            put(p, self.G, o["свойства"], key)
        if sub is None:
            return out
        s = o["подгруппы"][sub]
        n = lib.obj[s["≅"]]
        for p in SUB_PROPS:
            put(p, self.N, s["свойства"], f"{key}/{s['id']}")
        for p in LIB_GROUP_PROPS:
            put(p, self.N, n["свойства"], f"{key}/{s['id']} ≅ {s['≅']}")
        if s.get("фактор"):
            q = lib.obj[s["фактор"]]
            for p in LIB_GROUP_PROPS:
                put(p, self.Q, q["свойства"], f"{key}/{s['id']}: фактор ≅ {s['фактор']}")
        for name, t in (("центр", self.Z), ("коммутант", self.C)):
            if o.get(name) is not None:
                out[("r", "eq-sub", *sorted((self.N, t), key=str))] = (
                    o[name] == s["id"], f"{key}: {name} — {o[name]}")
        return out

    def check(self, facts):
        """None, если записи совместны с базой, иначе ядро противоречия."""
        lits = {}
        for a, (v, where) in facts.items():
            l = self.T.lit(a, v)
            if l is False:
                return [(a, v, where)]
            if l is not None:
                lits[l] = (a, v, where)
        if self.s.solve(assumptions=list(lits)):
            return None
        return [lits[l] for l in self.s.get_core() or [] if l in lits]

    def derive(self, facts, atoms):
        """Значения атомов, которые следуют из записей: {атом: значение}."""
        assume = [l for a, (v, _) in facts.items()
                  if (l := self.T.lit(a, v)) not in (None, False)]
        todo = [a for a in atoms if a not in facts]
        return {a: v for a, v in zip(todo, backbone(self.s, assume, [self.T.lit(a) for a in todo])) if v is not None}

    def values(self, lib, key, sub, need=None, drop=()):
        """Значения атомов пары (G, N): записанные и выведенные из них.
        need — какие атомы нужны; выводятся только недостающие из них.
        drop — пометки (из MARKS), значения с которыми не используются."""
        facts = self.facts(lib, key, sub)
        if drop:
            hard = self.hard_atoms(lib, key, sub, drop)
            facts = {a: x for a, x in facts.items() if a not in hard}
        vals = {a: v for a, (v, _) in facts.items()}
        missing = [a for a in (need or self.atoms()) if a not in vals]
        if missing:
            vals.update(self.derive(facts, missing))
        return vals

    def witnesses(self, lib, premises, goal, limit=3):
        """Пары (G, N) библиотеки, где посылки верны, а цель ложна.

        premises, goal — (атом, значение) над термами сцены G, N, G/N."""
        need = [a for a, _ in premises] + [goal[0]]
        out = []
        for key, sub in jobs(lib, lib.obj):
            o = lib.obj[key]
            if sub is None:
                continue
            facts = self.facts(lib, key, sub)
            quick = {a: v for a, (v, _) in facts.items()}
            if any(quick.get(a, v) != v for a, v in premises) or quick.get(goal[0]) == goal[1]:
                continue  # уже по записям не подходит
            vals = self.values(lib, key, sub, need)
            if all(vals.get(a) == v for a, v in premises) and vals.get(goal[0]) == (not goal[1]):
                s = o["подгруппы"][sub]
                out.append({"G": key, "имя G": o.get("имя"), "N": s["id"],
                            "имя N": s.get("имя", lib.obj[s["≅"]].get("имя")),
                            **{m: self.hard(lib, key, sub, need, m) for m in MARKS}})
                if len(out) >= limit:
                    break
        return out

    def hard_atoms(self, lib, key, sub, marks=("трудно",)):
        """Атомы пары, записанные значения которых помечены одной из marks."""
        o = lib.obj[key]
        owner = [(self.G, o)]
        if sub is not None:
            s = o["подгруппы"][sub]
            owner += [(self.N, lib.obj[s["≅"]]), (self.Q, lib.obj.get(s.get("фактор")))]
        return {("p", p, t) for t, rec in owner if rec for m in marks for p in rec.get(m, ())}

    def hard(self, lib, key, sub, atoms, mark="трудно"):
        """Какие из атомов пары держатся на значениях с пометкой mark:
        «трудно» — сами по себе теоремы или требуют идеи, «короткий довод» —
        не учебные, но доказываются в несколько строк."""
        o = lib.obj[key]
        s = o["подгруппы"][sub]
        owner = {self.G: o, self.N: lib.obj[s["≅"]], self.Q: lib.obj.get(s.get("фактор"))}
        out = []
        for a in atoms:
            rec = owner.get(a[2]) if a[0] == "p" else None
            if rec and a[1] in rec.get(mark, ()):
                out.append(f"{a[1]}({rec.get('имя', rec['key'])})")
        return out

    def marked_name(self, lib, key, sub, atom, mark):
        """Имя помеченного значения как факта об исходной группе: у
        произведения — о том множителе, у которого оно помечено."""
        s = lib.obj[key]["подгруппы"][sub]
        rec = {self.G: key, self.N: s["≅"], self.Q: s.get("фактор")}[atom[2]]
        for part in rec.split("×"):
            if atom[1] in lib.obj[part].get(mark, ()):
                return f"{atom[1]}({part})"
        return f"{atom[1]}({rec})"

    def atoms(self):
        return ([("p", p, t) for t in (self.G, self.N, self.Q) for p in LIB_GROUP_PROPS]
                + [("p", p, self.N) for p in SUB_PROPS])


# Пометки значений библиотеки: контрпример, который держится на таком
# значении, условие не закрывает. «трудно» — теорема или нужна идея,
# «короткий довод» — довод в несколько строк, но не учебный.
MARKS = ("трудно", "короткий довод")

GROUP_PROPS = ("trivial", "abelian", "cyclic", "finite", "fin-gen", "free", "simple", "solvable",
               "nilpotent", "perfect", "torsion-free", "periodic", "divisible", "centerless",
               "residually-finite", "indecomposable", "hopfian", "linear", "polycyclic", "bounded-exponent",
               "free-abelian",
               # арифметика порядка: p-группа (порядки элементов — степени одного простого),
               # |G| простое, p², pq (p ≠ q), не больше двух простых делителей, нечётный
               "p-group", "prime-order", "order-p2", "order-pq", "two-primes", "odd-order",
               "exponent-2", "exponent-3", "clt", "prime-orders", "linear-c",
               # 30.10: дедекиндовы, метабелевы, ступени ⩽ 2, аменабельные, левоупорядочиваемые
               "dedekind", "metabelian", "class-2", "amenable", "left-orderable")
# Свойства групп, которые библиотека выводит по правилам базы у построенных
# произведений, семейств и при насыщении бесконечных групп. До 5.11 — только
# GROUP_PROPS (37 из 66): countable, fin-pres, contains-free, no-finite-quotients,
# residually-nilpotent, locally-finite, … у 27 984 построенных A × B не выводились
# никогда, даже когда следуют из множителей (аудит таблицы G: известно 35 %).
# GROUP_PROPS не трогаем: по нему — атомы старых форм перебора (класс).
LIB_GROUP_PROPS = GROUP_PROPS + (
    "countable", "two-generated", "fin-pres", "rec-pres", "word-problem", "virtually-nilpotent",
    "virtually-solvable", "polynomial-growth", "contains-free", "whitehead", "kaplansky", "comp-series",
    "hyperbolic", "no-finite-quotients", "rec-pres-ctbl", "exponent-4", "exponent-6", "co-hopfian",
    "bi-orderable", "property-t", "residually-nilpotent", "locally-finite", "locally-cyclic",
    "locally-nilpotent", "locally-solvable", "proper-subs-abelian", "proper-subs-nilpotent",
    "proper-subs-cyclic", "proper-subs-finite")

_LIB = _SCENE = None


# --- поиск контрпримера на произвольной схеме -----------------------------------


# Множители построенных произведений для схем с несколькими группами.
CORE = ["2:1", "6:1", "60:5", "Z", "Q", "QmodZ", "Pruf2", "F2", "Foo", "UT3Z", "PSL2R", "BS23", "Ainf",
        "SumC2", "Tarski", "SL2Rcov"]


FACT_MAX = 2000  # n! считается при n ⩽ FACT_MAX, иначе значение неизвестно (ослабление, в реестре)


def _is_prime(n):
    """Миллер — Рабин, детерминированный для n < 3.3·10²⁴ (основания — первые 13 простых)."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for p in small:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _rho(n):
    """Делитель составного n (Поллард — Брент)."""
    import math
    import random
    if n % 2 == 0:
        return 2
    rnd = random.Random(n)
    while True:
        y, c, m = rnd.randrange(1, n), rnd.randrange(1, n), 128
        g, r, q = 1, 1, 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g


@functools.lru_cache(maxsize=None)
def _phi(n):
    """φ(n) разложением на простые: малые делители перебором, остаток — Миллер —
    Рабин (детерминированный при n < 3.3·10²⁴) и Поллард — Брент. Для n ⩾ 3·10²⁴ —
    None (значение неизвестно): прежде перебор до √n зависал на огромных n из
    num-pow. Для прежних n ответ тот же (сверено с перебором при n < 5000 и на
    случайных n < 10¹²)."""
    if n >= 3 * 10 ** 24:
        return None
    primes, m = set(), n
    for p in range(2, 1000):
        if m % p == 0:
            primes.add(p)
            while m % p == 0:
                m //= p
    todo = [m] if m > 1 else []
    while todo:
        x = todo.pop()
        if x == 1:
            continue
        if _is_prime(x):
            primes.add(x)
            continue
        d = _rho(x)
        todo += [d, x // d]
    r = n
    for p in primes:
        r -= r // p
    return r


class Search:
    """Контрпример к «посылки ⇒ цель» на графе условия.

    Переменные схемы пробегают библиотеку: группа — объекты, подгруппа —
    записанные подгруппы уже выбранной группы. Построенные термы, которые
    библиотека знает (фактор, произведение, Aut, центр, коммутант), получают
    записанные значения; про остальные значения выводит SAT-решатель из
    записанных и базы правил. Подстановка — контрпример, если из записей
    следуют все посылки и отрицание цели."""

    def __init__(self, graph, theory, lib, max_order=16):
        self.g, self.T, self.lib = graph, theory, lib
        self.s = theory.solver()
        self.vars = [t for t in graph.terms if isinstance(t, Var)]
        # Несколько групп или больше двух переменных (цепочки подгрупп, гомоморфизмы):
        # строк иначе миллионы, берём сокращённый набор объектов.
        many = (sum(1 for t in self.vars if graph.terms[t].sort == "Grp.obj") > 1
                or len(self.vars) > 2 or any(graph.terms[t].sort == "Grp.num" for t in self.vars))
        # Для схем с несколькими группами — бесконечные и малые конечные.
        # Неразрешимые конечные порядка ⩽ 120 (A₅, S₅, SL(2, 5), …) нужны всегда.
        self.objects = [k for k, o in lib.obj.items()
                        if not many or (not o.get("синтез") and (
                            not o["конечная"] or int(k.split(":")[0]) <= max_order
                            or (o["свойства"].get("solvable") is False and int(k.split(":")[0]) <= 120)))]
        if sum(1 for t in self.vars if graph.terms[t].sort == "Grp.obj") >= 3:
            # Три группы и больше: строк — куб числа объектов; берём конечные порядка ⩽ 12
            # и бесконечные из CORE (A × B ≅ A × C — по ключам построенных произведений).
            self.objects = [k for k, o in lib.obj.items() if not o.get("синтез") and (
                (o["конечная"] and int(k.split(":")[0]) <= 12) or (not o["конечная"] and k in CORE))]
            many = False
        if many:
            # Разложимые примеры: построенные произведения небольшого набора групп.
            have = set(self.objects)
            for i, a in enumerate(CORE):
                for b in CORE[i:]:
                    k = lib.prod.get((a, b))
                    if k and k not in have:
                        self.objects.append(k)
                        have.add(k)

    def _obj(self, im):
        """Ключ группы-объекта для образа: самой группы или подгруппы (её ≅)."""
        if im is None:
            return None
        if im[0] == "obj":
            return im[1]
        if im[0] == "sub":
            return self.lib.obj[im[1]]["подгруппы"][im[2]]["≅"]
        return None

    def _sub_index(self, key, pred):
        subs = self.lib.obj[key]["подгруппы"] or []
        return next((j for j, x in enumerate(subs) if pred(x)), None)

    def _one(self, key):
        return self._sub_index(key, lambda x: x["≅"] == "1:1")

    def _all(self, key):
        return self._sub_index(key, lambda x: x["свойства"].get("whole"))

    def morphisms(self, d, c):
        """Гомоморфизмы d → c, которые библиотека знает: тождественный,
        нулевой, проекции на факторы, вложения подгрупп.
        ("mor", вид, d, c, номер подгруппы или None)."""
        out = [("mor", "zero", d, c, None)]
        if d == c:
            out.append(("mor", "id", d, c, None))
            # прочие эндоморфизмы конечной группы — из GAP (gap/homs.g)
            out += [("mor", "end", d, c, i) for i in range(len(self.lib.obj[d].get("эндоморфизмы") or []))]
        for j, x in enumerate(self.lib.obj[d]["подгруппы"] or []):
            if x["свойства"].get("normal") and x.get("фактор") == c and not x["свойства"].get("whole") \
                    and x["≅"] != "1:1":
                out.append(("mor", "proj", d, c, j))
        for j, x in enumerate(self.lib.obj[c]["подгруппы"] or []):
            if x["≅"] == d and not x["свойства"].get("whole") and x["≅"] != "1:1":
                out.append(("mor", "incl", d, c, j))
        return out

    def _assign(self, i, env):
        if i == len(self.vars):
            yield dict(env)
            return
        t = self.vars[i]
        info = self.g.terms[t]
        if info.sort == "Grp.obj":
            for k in self.objects:
                env[t] = ("obj", k)
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.sub":
            # подгруппа группы или подгруппы (тогда — подгруппа её типа ≅)
            amb = self._obj(self._image(info.links.get("ambient"), env))
            if amb is None:
                return
            for j in range(len(self.lib.obj[amb]["подгруппы"] or [])):
                env[t] = ("sub", amb, j)
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.mor":
            d = self._obj(self._image(info.links.get("dom"), env))
            c = self._obj(self._image(info.links.get("cod"), env))
            if d is None or c is None:
                return
            for f in self.morphisms(d, c):
                env[t] = f
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.num":
            for n in NUMS:
                env[t] = ("num", n)
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.diag":
            for k in self.lib.diag:
                env[t] = ("diag", k)
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.fam":
            for k in self.lib.fam:
                env[t] = ("fam", k)
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.elt":
            amb = self._obj(self._image(info.links.get("ambient"), env))
            cls = amb and self.lib.obj[amb].get("элементы")
            if not cls:
                return
            for j, c in enumerate(cls):
                env[t] = ("elt", amb, j)
                yield from self._assign(i + 1, env)
                if c["size"] > 1:  # другой элемент того же класса (не перестановочный с x, если такой есть)
                    env[t] = ("elt", amb, j, "g")
                    yield from self._assign(i + 1, env)
        elif info.sort == "Grp.gset":
            amb = self._obj(self._image(info.links.get("ambient"), env))
            if amb is None:
                return
            for a in self.actions(amb):
                env[t] = a
                yield from self._assign(i + 1, env)
        elif info.sort == "Grp.pt":
            a = self._image(info.links.get("ambient"), env)
            if not a or a[0] != "act":
                return
            subs = self.lib.obj[a[1]]["подгруппы"]
            for j in range(len(a[2])):
                env[t] = ("pt", a, j)
                yield from self._assign(i + 1, env)
                # другая точка той же орбиты: стабилизатор — другая сопряжённая с Hⱼ
                if subs[a[2][j]]["свойства"].get("normal") is False:
                    env[t] = ("pt", a, j, "g")
                    yield from self._assign(i + 1, env)
        # прочие сорта (элементы) библиотека пока не перебирает
        env.pop(t, None)

    # Действия: ("act", ключ группы, (i₁, …)) — дизъюнктное объединение
    # G/Hᵢ₁ ⊔ …, Hᵢ — представители классов подгрупп записи (стабилизаторы
    # точек орбит). Точка — ("pt", действие, номер орбиты).
    def actions(self, key):
        subs = self.lib.obj[key]["подгруппы"] or []
        one, whole = self._one(key), self._all(key)
        out = [("act", key, (j,)) for j in range(len(subs))]
        if whole is not None:
            out.append(("act", key, (whole, whole)))       # тривиальное на двух точках
        if one is not None and whole is not None:
            out.append(("act", key, (one, whole)))         # точное нетранзитивное
        return out

    def _core(self, key, idxs):
        """Наибольшая нормальная подгруппа, лежащая во всех Hᵢ (ядро действия)."""
        subs = self.lib.obj[key]["подгруппы"]
        hs = [subs[j] for j in idxs]
        if any(h["≅"] == "1:1" for h in hs):
            return self._one(key)
        if len(set(idxs)) == 1 and hs[0]["свойства"].get("normal"):
            return idxs[0]
        if not self.lib.obj[key]["конечная"] or any(x.get("над") is None for x in subs):
            return None
        best = None
        for j, n in enumerate(subs):
            if n["свойства"].get("normal") and all(h["id"] in n["над"] for h in hs):
                if best is None or int(n["≅"].split(":")[0]) > int(subs[best]["≅"].split(":")[0]):
                    best = j
        return best

    def _act_facts(self, a):
        _, key, orbs = a
        subs = self.lib.obj[key]["подгруппы"]
        hs = [subs[j] for j in orbs]
        tr = len(orbs) == 1
        core = self._core(key, orbs)
        free = all(h["≅"] == "1:1" for h in hs)
        single = tr and bool(hs[0]["свойства"].get("whole"))
        fin = [h["свойства"].get("finite-index") for h in hs]
        prim = (True if single else hs[0]["свойства"].get("maximal")) if tr else False
        return {"transitive": tr, "free-act": free, "regular": tr and free, "singleton-set": single,
                "finite-set": None if None in fin else all(fin), "primitive": prim,
                "faithful": None if core is None else subs[core]["≅"] == "1:1"}

    def _image(self, t, env):
        if t in env:
            return env[t]
        if not isinstance(t, App):
            return None
        lib = self.lib
        if (t.op == "quotient" and isinstance(t.args[0], App) and t.args[0].op == "aut"
                and isinstance(t.args[1], App) and t.args[1].op == "inn" and t.args[1].args == t.args[0].args):
            x = self._obj(self._image(t.args[0].args[0], env))  # Out(X) = Aut(X)/Inn(X)
            k = x and lib.obj[x].get("out")
            return ("obj", k) if k else None
        args = [self._image(a, env) for a in t.args]
        if t.op.startswith("num:"):
            return ("num", int(t.op[4:]))
        if t.op in ("alt", "sym-n", "cyc", "dih") and args[0] and args[0][0] == "num":
            # ключи SmallGroups: имена групп в таблице не однозначны (S₃ записана
            # как «S3», а не «D6»; S₅ — как «120:34»; тривиальная — как «1»)
            n = args[0][1]
            k = SMALL_FAMILY[t.op].get(n)
            if k is None and n != INF and t.op == "cyc":
                if not hasattr(self, "_by_name"):
                    self._by_name = {o.get("имя"): k for k, o in lib.obj.items() if o.get("конечная")}
                k = self._by_name.get(f"C{n}")
            if k is None and t.op == "sym-n" and isinstance(n, int) and n != INF:
                k = lib.sym_key(n)  # Sₙ при n ⩾ 7 (S_∞ не записывается: Sym(ℕ) или FSym — не определено)
            return ("obj", k) if k and k in lib.obj else None
        if t.op in ("num-add", "num-sub", "num-pow", "num-gcd") and all(a and a[0] == "num" for a in args):
            a, b = args[0][1], args[1][1]
            if INF in (a, b):
                return ("num", INF) if t.op in ("num-add", "num-pow") and a != 1 else None
            v = {"num-add": a + b, "num-sub": a - b, "num-pow": a ** b if b < 64 else None,
                 "num-gcd": gcd(a, b)}[t.op]
            return ("num", v) if v is not None and v >= 1 else None
        if t.op == "num-phi" and args[0] and args[0][0] == "num" and args[0][1] != INF:
            v = _phi(args[0][1])
            return ("num", v) if v is not None else None
        if t.op == "num-sylow" and args[0] and args[0][0] == "num" and args[0][1] != INF:
            p, key = args[0][1], self._obj(args[1])
            o = key and lib.obj[key]
            if not o or not o.get("конечная") or not o.get("подгруппы") or p >= 3 * 10 ** 24 or not _is_prime(p):
                return None
            n = int(key.split(":")[0])
            pp = 1
            while n % (pp * p) == 0:
                pp *= p
            for x in o["подгруппы"]:
                if int(x["≅"].split(":")[0]) == pp:
                    nid = x.get("нормализатор")
                    nx = next((y for y in o["подгруппы"] if y["id"] == nid), None) if nid is not None else None
                    if x["свойства"].get("normal"):
                        return ("num", 1)
                    return ("num", n // int(nx["≅"].split(":")[0])) if nx else None
            return None
        if t.op == "num-fact" and args[0] and args[0][0] == "num":
            n = args[0][1]
            if n == INF:
                return ("num", INF)
            if n > FACT_MAX:
                # |G|! для |G| ~ 10¹⁰ не вычислить (строка таблицы G висела часами:
                # num-fact(ord(G)) во вселенной G) — значение неизвестно
                return None
            from math import factorial
            return ("num", factorial(n))
        if t.op in ("ord", "index", "num-mul", "prod-card", "bs", "exponent", "num-classes"):
            return self._num_image(t, args, env)
        if t.op == "eltord" and len(args) == 2 and args[1] and args[1][0] == "elt":
            # порядок элемента — из записи класса (0 — бесконечный)
            o = lib.obj[args[1][1]]["элементы"][args[1][2]]["ord"]
            return ("num", INF if o == 0 else o)
        if t.op == "compose" and len(args) == 2 and all(a and a[0] == "mor" for a in args):
            f, e = args  # compose(F, E) = E ∘ F: dom F → cod E
            if f[1] == "id":
                return e
            if e[1] == "id":
                return f
            if "zero" in (f[1], e[1]):
                return ("mor", "zero", f[2], e[3], None)
            return None
        if t.op == "apply-mor" and len(args) == 2 and args[0] and args[0][0] == "mor" and args[1] and args[1][0] == "elt":
            if args[0][1] == "id":
                return args[1]
            if args[0][1] == "zero":
                cls = lib.obj[args[0][3]].get("элементы") or []
                one = next((i for i, c in enumerate(cls) if c["ord"] == 1), None)
                return ("elt", args[0][3], one) if one is not None else None
            return None
        if t.op in ("colim", "lim") and args[0] and args[0][0] == "diag":
            k = lib.diag[args[0][1]].get("прямой предел" if t.op == "colim" else "обратный предел")
            return ("obj", k) if k else None
        if t.op in ("prod-fam", "sum-fam") and args[0] and args[0][0] == "fam":
            f = lib.fam[args[0][1]]
            k = f.get("∏" if t.op == "prod-fam" else "⊕")
            if not k:
                return None
            if t.op == "sum-fam" and f.get("∏"):
                # ⊕F ⩽ ∏F: подгруппа записи ∏F, изоморфная ⊕F
                # конечное семейство: ⊕F = ∏F — вся группа, а не изоморфная ей собственная подгруппа (2ℤ × ℤ ⩽ ℤ²)
                idx = self._sub_index(f["∏"], lambda x: x["свойства"].get("whole")) if k == f["∏"] else None
                if idx is None:
                    idx = self._sub_index(f["∏"], lambda x: x["≅"] == k)
                if idx is not None:
                    return ("sub", f["∏"], idx)
            return ("obj", k)
        if t.op == "quotient" and args[0] and args[1] and args[1][0] == "sub":
            q = lib.obj[args[1][1]]["подгруппы"][args[1][2]].get("фактор")
            return ("obj", q) if q else None
        if t.op in ("prod", "freeprod", "wreath"):
            ks = [self._obj(a) for a in args]
            if None in ks:
                return None
            # тривиальный множитель: A × 1 = A ∗ 1 = A, A ≀ 1 = A, 1 ≀ B = B
            triv = [lib.obj[k]["свойства"].get("trivial") for k in ks]
            if triv[1]:
                return ("obj", ks[0])
            if triv[0] and t.op != "wreath":
                return ("obj", ks[1])
            if triv[0] and t.op == "wreath":
                return ("obj", ks[1])
            p = {"prod": lib.prod, "freeprod": lib.fprod, "wreath": lib.wreath}[t.op].get((ks[0], ks[1]))
            return ("obj", p) if p else None
        if t.op == "profinite" and self._obj(args[0]):
            # X̂ = X у конечной X; X̂ = 1, если у X нет собственных подгрупп конечного индекса
            k = self._obj(args[0])
            o = lib.obj[k]
            if o.get("конечная"):
                return ("obj", k)
            return ("obj", "1:1") if o["свойства"].get("no-finite-quotients") else None
        if t.op in ("aut", "ab", "inn") and self._obj(args[0]):
            o = lib.obj[self._obj(args[0])]
            k = o.get({"aut": "aut", "ab": "абелианизация", "inn": "inn"}[t.op])
            if not k and t.op in ("ab", "inn"):
                # Gᵃᵇ = G/G′, Inn(G) ≅ G/Z(G): фактор записанной подгруппы.
                sid = o.get("коммутант" if t.op == "ab" else "центр")
                s = next((x for x in o["подгруппы"] or [] if x["id"] == sid), None)
                k = s.get("фактор") if s else None
            return ("obj", k) if k else None
        if t.op == "profinite-map" and self._obj(args[0]):
            # X → X̂: у конечной X̂ ≅ X и это изоморфизм (не тождество: X̂ — другой
            # объект, соглашение 6.11 — не идемпотентно); без конечных факторов X̂ = 1
            k0 = self._obj(args[0])
            o = lib.obj[k0]
            if o.get("конечная") or o["свойства"].get("finite"):
                return ("mor", "isoprof", k0, k0, None)
            if o["свойства"].get("no-finite-quotients") and "1:1" in lib.obj:
                return ("mor", "zero", k0, "1:1", None)
            return None
        if (t.op in ("pullback", "pushout") and len(args) == 2 and all(a and a[0] == "mor" for a in args)
                and args[0] == args[1]):
            _, kind, d, c, j = args[0]
            if t.op == "pullback":
                # ядерная пара {(x, y): f x = f y}: у инъективного f — диагональ ≅ dom f;
                # у нулевого — dom f × dom f
                if kind in ("id", "isoprof", "cayley", "incl") or (kind == "end" and lib.obj[d]["эндоморфизмы"][j]["inj"]):
                    return ("obj", d)
                if kind == "zero":
                    p = d if lib.obj[d]["свойства"].get("trivial") else lib.prod.get((d, d))
                    return ("obj", p) if p else None
                return None
            # pushout(f, f) = cod f ∗_{im f} cod f
            if kind in ("id", "isoprof"):
                return ("obj", d)
            if kind == "zero":
                if lib.obj[c]["свойства"].get("trivial"):
                    return ("obj", c)
                p = lib.fprod.get((c, c))  # амальгама по 1 — свободное произведение
                return ("obj", p) if p else None
            if kind == "cayley":
                n = self._key_order(d)
                if isinstance(n, int) and n <= 2:
                    return ("obj", c)  # cayley — изоморфизм: амальгама ≅ Sym(X) ≅ X
                k = lib.amalgam_sym_key(d)
                return ("obj", k) if k else None
            return None
        if t.op in ("sym", "cayley") and self._obj(args[0]):
            # Sym(X) — по мощности X (Library.sym_key); cayley: X → Sym(X), левые сдвиги
            k0 = self._obj(args[0])
            n = self._key_order(k0)
            if n == "inf":
                c = lib.obj[k0]["свойства"].get("countable")
                n = None if c is None else "ctbl" if c else "unctbl"
            ks = lib.sym_key(n) if n is not None else None
            if ks is None:
                return None
            return ("obj", ks) if t.op == "sym" else ("mor", "cayley", k0, ks, None)
        if t.op == "coset-act" and args[1] and args[1][0] == "sub":
            return ("act", args[1][1], (args[1][2],))
        if t.op == "regular-act" and self._obj(args[0]):
            j = self._one(self._obj(args[0]))
            return ("act", self._obj(args[0]), (j,)) if j is not None else None
        if t.op == "choose-pt" and args[1] and args[1][0] == "act":
            return ("pt", args[1], 0)
        if t.op == "base-pt" and args[1] and args[1][0] == "sub":
            return ("pt", ("act", args[1][1], (args[1][2],)), 0)
        if t.op == "stab" and args[2] and args[2][0] == "pt":
            a, j = args[2][1], args[2][2]
            return ("sub", a[1], a[2][j], *args[2][3:])
        if t.op in ("gen", "centralizer-elt") and len(args) == 2 and args[1] and args[1][0] == "elt":
            c = lib.obj[args[1][1]]["элементы"][args[1][2]]
            j = c["gen" if t.op == "gen" else "cent"]
            # у другого элемента класса — сопряжённая подгруппа (та же, если она нормальна)
            # («?»: может и совпасть — ⟨x⁻¹⟩ = ⟨x⟩, C(x⁻¹) = C(x))
            v = ("?",) if args[1][3:] and not lib.obj[args[1][1]]["подгруппы"][j]["свойства"].get("normal") else ()
            return ("sub", args[1][1], j, *v)
        if t.op == "core" and args[1] and args[1][0] == "sub":
            c = self._core(args[1][1], (args[1][2],))
            return ("sub", args[1][1], c) if c is not None else None
        if t.op == "act-ker" and args[1] and args[1][0] == "act":
            c = self._core(args[1][1], args[1][2])
            return ("sub", args[1][1], c) if c is not None else None
        if t.op in ("center", "commutator", "frattini", "torsion") and self._obj(args[0]):
            key = self._obj(args[0])
            o = lib.obj[key]
            sid = o.get({"center": "центр", "commutator": "коммутант", "frattini": "фраттини",
                         "torsion": "кручение"}[t.op])
            idx = self._sub_index(key, lambda x: x["id"] == sid) if sid is not None else None
            return ("sub", key, idx) if idx is not None else None
        if t.op in ("ker", "im") and args[0] and args[0][0] == "mor":
            _, kind, d, c, j = args[0]
            if kind == "end":
                e = lib.obj[d]["эндоморфизмы"][j]
                return ("sub", d, e["ker"]) if t.op == "ker" else ("sub", c, e["im"])
            if kind == "cayley":
                return ("sub", d, self._one(d)) if t.op == "ker" and self._one(d) is not None else None
            if t.op == "ker":
                idx = {"zero": self._all(d), "id": self._one(d), "isoprof": self._one(d), "proj": j,
                       "incl": self._one(d)}[kind]
                return ("sub", d, idx) if idx is not None else None
            idx = {"zero": self._one(c), "id": self._all(c), "isoprof": self._all(c), "proj": self._all(c),
                   "incl": j}[kind]
            return ("sub", c, idx) if idx is not None else None
        if t.op == "whole-sub" and self._obj(args[0]):
            idx = self._all(self._obj(args[0]))
            return ("sub", self._obj(args[0]), idx) if idx is not None else None
        if t.op in ("meet", "join", "comm") and len(args) == 3 and all(a and a[0] == "sub" for a in args[1:]):
            n, m = args[1], args[2]
            if n[1] != m[1]:
                return None
            key = n[1]
            one, whole = self._one(key), self._all(key)
            if t.op != "comm":
                meet = t.op == "meet"
                if n[2] == m[2] and n[3:] == m[3:] and "?" not in n[3:]:
                    return n
                for a, b in ((n, m), (m, n)):
                    if a[2] == one:
                        return a if meet else b
                    if a[2] == whole:
                        return b if meet else a
            return self._hk(t, key, n, m)
        if t.op in ("centralizer", "normalizer", "normal-closure") and len(args) == 2 and args[1] and args[1][0] == "sub":
            key, j = args[1][1], args[1][2]
            x = lib.obj[key]["подгруппы"][j]
            pr = x["свойства"]
            if t.op == "normalizer" and pr.get("normal"):
                return ("sub", key, self._all(key))
            if t.op == "normal-closure" and pr.get("normal"):
                return args[1]
            if t.op == "centralizer":
                if pr.get("whole"):
                    c = lib.obj[key].get("центр")
                    idx = self._sub_index(key, lambda s: s["id"] == c) if c is not None else None
                    return ("sub", key, idx) if idx is not None else None
                if x["≅"] == "1:1" or pr.get("central") and lib.obj[key]["свойства"].get("abelian"):
                    return ("sub", key, self._all(key))
            f = {"centralizer": "централизатор", "normalizer": "нормализатор",
                 "normal-closure": "нормальное замыкание"}[t.op]
            if x.get(f) is not None:
                idx = self._sub_index(key, lambda s: s["id"] == x[f])
                return ("sub", key, idx) if idx is not None else None
            return None
        return None

    def _exact_sub(self, t, im):
        """Образ im подгруппы-терма t — сама подгруппа-представитель своего класса
        (а не какая-то сопряжённая): переменная, нормальная подгруппа или точный
        результат таблицы H ∩ K, ⟨H, K⟩, [H, K]."""
        if im is None or im[0] != "sub" or len(im) > 3:
            return False
        if self.lib.obj[im[1]]["подгруппы"][im[2]]["свойства"].get("normal"):
            return True
        return isinstance(t, Var) or isinstance(t, App) and t.op in ("meet", "join", "comm")

    def _hk(self, t, key, n, m):
        """H ∩ K, ⟨H, K⟩, [H, K] по таблице GAP (grp-hk.jsonl): только для точных H и K."""
        tab = self.lib.obj[key].get("hk")
        if tab is None or not (self._exact_sub(t.args[1], n) and self._exact_sub(t.args[2], m)):
            return None
        size, flat = tab
        i, j = sorted((n[2], m[2]))
        off = i * size - i * (i - 1) // 2 + (j - i)
        c = flat[3 * off + ("meet", "join", "comm").index(t.op)]
        return ("sub", key, c) if c >= 0 else ("sub", key, -c - 1, "?")

    def _im_order(self, im):
        """Порядок группы образа: число, INF или None."""
        k = self._obj(im)
        if k is None:
            return None
        o = self.lib.obj[k]
        if o.get("порядок") is not None:  # синтетические Sₙ
            return o["порядок"]
        if o.get("конечная"):
            head = k.split(":")[0]
            return int(head) if head.isdigit() else None
        fin = o["свойства"].get("finite")
        return INF if fin is False else None

    def _im_exponent(self, im):
        """exp(G): число, INF (экспонента не ограничена) или None (неизвестно)."""
        k = self._obj(im)
        if k is None:
            return None
        o = self.lib.obj[k]
        if o.get("экспонента") is not None:  # GAP props2, сверено с классами
            return o["экспонента"]
        els, n = o.get("элементы"), self._im_order(("obj", k))
        if o.get("конечная") and els and isinstance(n, int) and sum(c["size"] for c in els) == n:
            lcm = 1  # только по полному списку классов (сумма размеров = |G|)
            for c in els:
                if not c.get("ord"):
                    return None
                lcm = lcm * c["ord"] // gcd(lcm, c["ord"])
            return lcm
        pr = o.get("свойства", {})
        if pr.get("trivial") is True:
            return 1
        if pr.get("trivial") is False and pr.get("exponent-2") is True:
            return 2
        if pr.get("bounded-exponent") is False or (pr.get("trivial") is False and pr.get("torsion-free") is True):
            return INF  # нетривиальная без кручения — экспонента не ограничена
        return None

    def _im_classes(self, im):
        """k(G), число классов сопряжённости: число, INF или None (неизвестно).
        У конечной группы — по полному списку классов GAP (сумма размеров = |G|)."""
        k = self._obj(im)
        if k is None:
            return None
        o = self.lib.obj[k]
        pr = o.get("свойства", {})
        if pr.get("trivial") is True:
            return 1
        if o.get("конечная"):
            els, n = o.get("элементы"), self._im_order(("obj", k))
            if els and isinstance(n, int) and sum(c["size"] for c in els) == n:
                return len(els)
            if pr.get("abelian") is True and isinstance(n, int):
                return n
            return None
        if pr.get("abelian") is True and pr.get("finite") is False:
            return INF  # у бесконечной абелевой каждый класс — один элемент
        return None

    def _num_image(self, t, args, env):
        lib = self.lib
        if t.op == "exponent":
            n = self._im_exponent(args[0])
            return ("num", n) if n is not None else None
        if t.op == "num-classes":
            n = self._im_classes(args[0])
            return ("num", n) if n is not None else None
        if t.op == "ord":
            n = self._im_order(args[0])
            return ("num", n) if n is not None else None
        if t.op == "rank":
            n = self._key_rank(self._obj(args[0]))
            return ("num", n) if n is not None else None
        if t.op == "index" and args[1] and args[1][0] == "sub":
            key, j = args[1][1], args[1][2]
            x = lib.obj[key]["подгруппы"][j]
            if x["свойства"].get("finite-index") is False:
                return ("num", INF)
            a, b = self._im_order(("obj", key)), self._im_order(args[1])
            if isinstance(a, int) and isinstance(b, int):
                return ("num", a // b)
            return None
        if t.op == "num-mul" and all(a and a[0] == "num" for a in args):
            a, b = args[0][1], args[1][1]
            return ("num", INF if INF in (a, b) else a * b)
        if t.op == "prod-card" and args[1] and args[2] and args[1][0] == args[2][0] == "sub":
            # |HK| = |H| |K| / |H ∩ K|
            m = self._image(App("meet", t.args), env)
            h, k, w = self._im_order(args[1]), self._im_order(args[2]), self._im_order(m)
            if INF in (h, k):
                return ("num", INF)
            if all(isinstance(x, int) for x in (h, k, w)):
                return ("num", h * k // w)
            return None
        if t.op == "bs" and all(a and a[0] == "num" for a in args):
            k = BS.get((args[0][1], args[1][1]))
            return ("obj", k) if k and k in lib.obj else None
        return None

    def _mor_facts(self, f):
        _, kind, d, c, j = f
        td = self.lib.obj[d]["свойства"].get("trivial")
        tc = self.lib.obj[c]["свойства"].get("trivial")
        if kind == "id":
            return {"injective": True, "surjective": True, "iso": True, "zero-mor": td,
                    "idempotent": True, "inner-aut": True}
        if kind == "isoprof":  # X → X̂ конечной X: изоморфизм на другой объект
            return {"injective": True, "surjective": True, "iso": True, "zero-mor": td,
                    "idempotent": False, "inner-aut": False}
        if kind == "zero":
            return {"zero-mor": True, "injective": td, "surjective": tc,
                    "iso": (td and tc) if td is not None and tc is not None else None,
                    "idempotent": True if d == c else None, "inner-aut": td if d == c else None}
        if kind == "cayley":
            # инъективен (сдвиги различны); сюръективен ⇔ |X| = |Sym(X)| ⇔ |X| ⩽ 2
            # (n ⩽ n! ⇔ n ⩽ 2; для бесконечной |Sym(X)| = 2^|X| > |X|); нулевой ⇔ X = 1
            n = self._key_order(d)
            surj = (n <= 2) if isinstance(n, int) else (False if n == "inf" else None)
            return {"injective": True, "surjective": surj, "iso": surj, "zero-mor": td}
        if kind == "end":
            e = self.lib.obj[d]["эндоморфизмы"][j]
            return {"injective": e["inj"], "surjective": e["surj"], "iso": e["inj"] and e["surj"],
                    "zero-mor": False, "idempotent": e["idem"], "inner-aut": e["inner"]}
        x = (self.lib.obj[d] if kind == "proj" else self.lib.obj[c])["подгруппы"][j]
        if kind == "proj":  # j — ядро, собственное и нетривиальное
            return {"injective": False, "surjective": True, "iso": False, "zero-mor": tc}
        return {"injective": True, "surjective": False, "iso": False, "zero-mor": td}

    def facts(self, env, terms=None):
        """{атом: значение} по записям библиотеки и {атом: (пометка, значение)}
        для значений с пометками из MARKS."""
        out, hard, subs, elts, nums = {}, {}, {}, {}, {}
        for t in terms or self.g.terms:
            im = self._image(t, env)
            if im is None:
                continue
            if im[0] in ("fam", "diag"):
                for p, v in (self.lib.fam if im[0] == "fam" else self.lib.diag)[im[1]]["свойства"].items():
                    if self.g.v.prop_fits(p, self.g.terms[t].sort):
                        out[("p", p, t)] = v
                continue
            if im[0] == "num":
                n = im[1]
                fin = n != INF
                for p, v in (("num-finite", fin), ("num-one", n == 1), ("num-two", n == 2),
                             ("num-prime", fin and n > 1 and all(n % d for d in range(2, n))),
                             ("num-even", n % 2 == 0 if fin else None)):
                    if v is not None and p in self.g.v.props:
                        out[("p", p, t)] = v
                nums[t] = n
                continue
            if im[0] == "pt":
                continue
            if im[0] == "elt":
                c = self.lib.obj[im[1]]["элементы"][im[2]]
                for p, v in (("identity-elt", c["ord"] == 1), ("involution", c["ord"] == 2),
                             ("central-elt", c["size"] == 1), ("torsion-elt", c["ord"] != 0),
                             ("real-elt", c.get("real")), ("commutator-elt", c.get("comm")),
                             ("generator", self.lib.obj[im[1]]["подгруппы"][c["gen"]]["свойства"].get("whole"))):
                    if v is not None and p in self.g.v.props:
                        out[("p", p, t)] = v
                elts[t] = im
                continue
            if im[0] == "act":
                for p, v in self._act_facts(im).items():
                    if v is not None and self.g.v.prop_fits(p, self.g.terms[t].sort):
                        out[("p", p, t)] = v
                continue
            if im[0] == "mor":
                for p, v in self._mor_facts(im).items():
                    if v is not None and self.g.v.prop_fits(p, self.g.terms[t].sort):
                        out[("p", p, t)] = v
                continue
            if im[0] == "obj":
                rec, rel = self.lib.obj[im[1]], {}
            else:
                s = self.lib.obj[im[1]]["подгруппы"][im[2]]
                rec, rel = self.lib.obj[s["≅"]], s["свойства"]
                subs[t] = im
            for p, v in list(rec["свойства"].items()) + list(rel.items()):
                if self.g.v.prop_fits(p, self.g.terms[t].sort) or p in rel:
                    out[("p", p, t)] = v
                    for m in MARKS:
                        if p in rec.get(m, ()) and p not in rel:
                            hard[("p", p, t)] = (m, f"{p}({rec.get('имя', rec['key'])})")
        items = list(subs.items())
        for i, (a, ia) in enumerate(items):
            for b, ib in items[i + 1:]:
                if ia[1] == ib[1] and self.g.terms[a].links.get("ambient") == self.g.terms[b].links.get("ambient"):
                    if ia[2] == ib[2] and (ia[3:] != ib[3:] or "?" in ia[3:]):
                        out[("r", "conj-sub", *sorted((a, b), key=str))] = True
                        if "?" in ia[3:] + ib[3:]:
                            continue  # сопряжённые, может быть, и равные
                        # разные сопряжённые одного класса (стабилизаторы двух точек орбиты)
                        out[("r", "eq-sub", *sorted((a, b), key=str))] = False
                        if self.lib.obj[ia[1]].get("конечная"):
                            out[("r", "le", a, b)] = out[("r", "le", b, a)] = False
                        continue
                    out[("r", "eq-sub", *sorted((a, b), key=str))] = ia[2] == ib[2]
                    perm = self._permutes(a, ia, b, ib)
                    if perm is not None and "permutes" in self.g.v.rels:
                        out[("r", "permutes", *sorted((a, b), key=str))] = perm
                    if self.lib.obj[ia[1]].get("конечная"):
                        # классы сопряжённости таблицы различны
                        out[("r", "conj-sub", *sorted((a, b), key=str))] = ia[2] == ib[2]
                    # ⩽ в очевидных случаях: равные, 1 ⩽ всё, всё ⩽ всей группы
                    for x, ix, y, iy in ((a, ia, b, ib), (b, ib, a, ia)):
                        sx = self.lib.obj[ix[1]]["подгруппы"][ix[2]]
                        sy = self.lib.obj[iy[1]]["подгруппы"][iy[2]]
                        o = self.lib.obj[ix[1]]
                        rec = {(u, v): w for u, v, w in o.get("⩽", [])}
                        if ix[2] == iy[2] or sx["≅"] == "1:1" or sy["свойства"].get("whole"):
                            out[("r", "le", x, y)] = True
                        elif sx["свойства"].get("whole") or sy["≅"] == "1:1":
                            out[("r", "le", x, y)] = False
                        elif (sx["id"], sy["id"]) in rec:
                            out[("r", "le", x, y)] = rec[sx["id"], sy["id"]]
                        elif o.get("конечная") and "над" in sx and sx["свойства"].get("normal") \
                                and sy["свойства"].get("normal"):
                            # у нормальных подгрупп класс сопряжённости из одной подгруппы: таблица точна
                            out[("r", "le", x, y)] = sy["id"] in sx["над"]
        # элементы: сопряжённость — по классам; равенство и перестановочность — в очевидных случаях
        items = list(elts.items())
        for i, (a, ia) in enumerate(items):
            for b, ib in items[i + 1:]:
                if ia[1] != ib[1] or self.g.terms[a].links.get("ambient") != self.g.terms[b].links.get("ambient"):
                    continue
                x, y = sorted((a, b), key=str)
                same = ia == ib
                out[("r", "conjugate", x, y)] = ia[2] == ib[2]
                out[("r", "eq-elt", x, y)] = same
                cls = self.lib.obj[ia[1]]["элементы"]
                if same or cls[ia[2]]["size"] == 1 or cls[ib[2]]["size"] == 1:
                    out[("r", "commute", x, y)] = True
                elif ia[2] == ib[2] and cls[ia[2]].get("nc"):
                    # «другой элемент класса» берётся не перестановочным с x
                    out[("r", "commute", x, y)] = False
        # числа: равенство, делимость, взаимная простота, порядок (∞ — бесконечная мощность,
        # мощности ∞ между собой не сравниваются)
        for a, x in nums.items():
            for b, y in nums.items():
                if a == b:
                    continue
                fin = INF not in (x, y)
                rels = {"num-le": (x <= y) if fin else (True if y == INF and x != INF else None),
                        "num-divides": (y % x == 0) if fin else None}
                if str(a) < str(b):
                    rels["num-eq"] = (x == y) if fin else (False if x != y else None)
                    rels["num-coprime"] = (gcd(x, y) == 1) if fin else None
                for r, v in rels.items():
                    if v is not None and r in self.g.v.rels:
                        out[("r", r, a, b)] = v
        # ≅ между группами: один ключ — изоморфны; разные ключи конечных таблиц — нет
        objs = {}
        for t in terms or self.g.terms:
            if self.g.v.fits(self.g.terms[t].sort, "Grp.obj"):
                k = self._obj(self._image(t, env))
                if k is not None:
                    objs[t] = k
        oi = list(objs.items())
        for i, (a, ka) in enumerate(oi):
            for b, kb in oi[i + 1:]:
                x, y = sorted((a, b), key=str)
                if ka == kb:
                    out[("r", "iso", x, y)] = True
                elif all(self.lib.obj[k].get("конечная") and not self.lib.obj[k].get("неканонический")
                         for k in (ka, kb)):
                    out[("r", "iso", x, y)] = False
                elif self._differ(ka, kb) or self._noniso(ka, kb):
                    out[("r", "iso", x, y)] = False  # свойство или запись «≇» различает: не изоморфны
        # Порядки: у термов без образа в библиотеке (C₈₅ × C₈₅, C₂ ≀ C₇, …) порядок
        # часто известен по множителям — разные порядки, значит, не изоморфны;
        # |A| ∤ |B| (или A бесконечна, B конечна) — A не вкладывается в B.
        ords = {}
        for t in terms or self.g.terms:
            if self.g.v.fits(self.g.terms[t].sort, "Grp.obj"):
                n = self._order(t, env)
                if n is not None:
                    ords[t] = n
        oi = list(ords.items())
        for i, (a, na) in enumerate(oi):
            for b, nb in oi[i + 1:]:
                x, y = sorted((a, b), key=str)
                if na != nb:
                    out.setdefault(("r", "iso", x, y), False)
                for u, nu, v, nv in ((a, na, b, nb), (b, nb, a, na)):
                    if nv != "inf" and (nu == "inf" or nv % nu):
                        out.setdefault(("r", "embeds", u, v), False)
        # A ↪ B: та же группа; конечные — по таблице подгрупп B; бесконечная не вкладывается
        # в конечную, большая конечная — в меньшую; запись «подгруппы» бесконечной B
        for atom in [a for a in self.T.atoms if a[0] == "r" and a[1] == "embeds"] if terms is None else []:
            a, b = atom[2], atom[3]
            ka, kb = objs.get(a), objs.get(b)
            if ka is None or kb is None:
                continue
            v = self._embeds(ka, kb)
            if v is not None:
                out[atom] = v
        # Inn(X) как подгруппа Aut(X): вся (полная группа) и центральна ли — по таблице GAP
        for t in terms or self.g.terms:
            if isinstance(t, App) and t.op == "inn":
                x = self._obj(self._image(t.args[0], env))
                rec = self.lib.obj[x] if x else {}
                if "inn = aut" in rec:
                    out[("p", "whole", t)] = rec["inn = aut"]
                    out[("p", "central", t)] = rec["inn центральна"]
                    out[("p", "finite-index", t)] = True
                    n, i = rec["|Aut|"], rec["|Out|"]
                    for p, v in arith_sub_props(n, n // i).items():
                        out[("p", p, t)] = v
                    # Inn ⊴ Aut максимальна ⇔ Out не имеет собственных нетривиальных подгрупп ⇔ |Out| простое
                    out[("p", "maximal", t)] = arith_sub_props(n, n // i)["prime-index"]
        return out, hard

    def _key_rank(self, k, depth=0):
        """d(G) группы записи k: поле «ранг» (GAP), 0 у 1, 1 у циклической ≠ 1, INF у
        не конечно порождённой; у построенного A × B — max(d A, d B) при взаимно
        простых конечных порядках и d A + d B, если один множитель тривиален;
        иначе None."""
        if k is None or depth > 4:
            return None
        o = self.lib.obj.get(k)
        if o is None:
            return None
        if o.get("ранг") is not None:
            return o["ранг"]
        pr = o["свойства"]
        if pr.get("trivial"):
            return 0
        if pr.get("cyclic"):
            return 1
        if pr.get("fin-gen") is False:
            return INF
        rev = self.__dict__.setdefault("_prod_of", {v: kk for kk, v in self.lib.prod.items()})
        if k in rev:
            a, b = rev[k]
            ra, rb = self._key_rank(a, depth + 1), self._key_rank(b, depth + 1)
            na, nb = self._key_order(a), self._key_order(b)
            if None in (ra, rb) or INF in (ra, rb):
                return None
            if 0 in (ra, rb):
                return ra + rb
            if isinstance(na, int) and isinstance(nb, int) and math.gcd(na, nb) == 1:
                return max(ra, rb)
        return None

    def _key_order(self, k):
        """Порядок группы записи: n у «n:i», произведение у построенных A × B,
        "inf" у бесконечной, None — неизвестно."""
        o = self.lib.obj.get(k)
        if o is None:
            return None
        if o["свойства"].get("finite") is False:
            return "inf"
        if o.get("порядок") is not None:  # синтетические Sₙ (sym_key)
            return o["порядок"]
        head = k.split(":")
        if o.get("конечная") and len(head) == 2 and head[0].isdigit() and head[1].isdigit():
            return int(head[0])
        rev = self.__dict__.setdefault("_prod_of", {v: kk for kk, v in self.lib.prod.items()})
        if k in rev:
            a, b = (self._key_order(x) for x in rev[k])
            if None in (a, b):
                return None
            return "inf" if "inf" in (a, b) else a * b
        return None

    def _order(self, t, env, depth=0):
        """Порядок группы-терма t в строке env (как в _key_order) — по образу, а если
        образа нет, по множителям: |A × B| = |A||B|, |A ≀ B| = |A|^|B| |B|,
        A ∗ B бесконечна при нетривиальных, |G/N| = |G| / |N|."""
        im = self._image(t, env)
        k = self._obj(im) if im is not None else None
        if k is not None:
            return self._key_order(k)
        if depth > 3 or not isinstance(t, App):
            return None
        if t.op in ("prod", "wreath", "freeprod") and len(t.args) == 2:
            a, b = (self._order(x, env, depth + 1) for x in t.args)
            if None in (a, b):
                return None
            if t.op == "freeprod":
                return a * b if 1 in (a, b) and "inf" not in (a, b) else "inf"
            if "inf" in (a, b):
                return "inf" if 1 not in (a, b) else (b if a == 1 else a)
            if t.op == "prod":
                return a * b
            return a ** b * b if b < 64 else None
        if t.op == "quotient" and len(t.args) == 2:
            g = self._order(t.args[0], env, depth + 1)
            n = self._sub_order(t.args[1], env)
            if isinstance(g, int) and isinstance(n, int) and n and g % n == 0:
                return g // n
        return None

    def _sub_order(self, t, env):
        im = self._image(t, env)
        if im is None or im[0] != "sub":
            return None
        return self._key_order(self.lib.obj[im[1]]["подгруппы"][im[2]]["≅"])

    def _differ(self, ka, kb):
        """Есть свойство, известное у обеих групп записей и различающее их."""
        pa, pb = self.lib.obj[ka]["свойства"], self.lib.obj[kb]["свойства"]
        return any(pa.get(p) is not None and pb.get(p) is not None and pa[p] != pb[p] for p in GROUP_PROPS)

    def _permutes(self, a, ia, b, ib):
        """HK = KH: да, если H = K или одна из них нормальна; для двух подгрупп-переменных
        конечной группы (это представители классов) — по таблице GAP (grp-perm.jsonl).
        Подгруппа-терм (нормализатор, ⟨x⟩, …) — какой-то член своего класса, не обязательно
        представитель, поэтому для неё таблица не годится."""
        subs = self.lib.obj[ia[1]]["подгруппы"]
        if ia[2] == ib[2] and ia[3:] == ib[3:] and "?" not in ia[3:]:
            return True
        if subs[ia[2]]["свойства"].get("normal") or subs[ib[2]]["свойства"].get("normal"):
            return True
        bad = self.lib.obj[ia[1]].get("неперестановочны")
        if bad is None or len(ia) > 3 or len(ib) > 3 or a not in self.vars or b not in self.vars:
            return None
        return (min(ia[2], ib[2]), max(ia[2], ib[2])) not in bad

    def _noniso(self, ka, kb):
        """Запись «≇» у одной из групп: доказано, что они не изоморфны."""
        return kb in self.lib.obj[ka].get("≇", ()) or ka in self.lib.obj[kb].get("≇", ())

    def _embeds(self, ka, kb):
        lib = self.lib
        if ka == kb or ka == "1:1":
            return True
        oa, ob = lib.obj[ka], lib.obj[kb]
        if kb in oa.get("↪̸", ()):
            return False  # запись «↪̸»: доказано, что A не вкладывается в B
        # свойство, наследуемое подгруппами, есть у B и нет у A — A не вкладывается в B
        if any(ob["свойства"].get(p) and oa["свойства"].get(p) is False for p in Theory.SUB_CLOSED):
            return False
        if ob.get("конечная") and oa["свойства"].get("finite") is False:
            return False
        if oa.get("конечная") and ob.get("конечная") and ":" in ka and ":" in kb:
            try:
                if int(ka.split(":")[0]) > int(kb.split(":")[0]):
                    return False
            except ValueError:
                pass
        subs = ob.get("подгруппы")
        if subs is not None and any(x["≅"] == ka for x in subs):
            return True
        if ob.get("конечная") and subs is not None and oa.get("конечная") and not oa.get("неканонический") \
                and not ob.get("неканонический") and not ob.get("синтез") and not ob.get("подгруппы неполные"):
            return False  # у конечной B записаны все классы подгрупп
        return None

    def entails(self, assume, atom, value):
        l = self.T.lit(atom, value)
        if l is None:
            return True
        if l is False:
            return False
        return not self.s.solve(assumptions=assume + [-l])

    def witnesses(self, premises, goal, limit=3):
        out = []
        asked = {a[2] for a, _ in premises} | {goal[0][2]}
        for env in self._assign(0, {}):
            quick, _ = self.facts(env, asked)  # сначала только термы вопроса
            if any(quick.get(a, v) != v for a, v in premises) or quick.get(goal[0]) == goal[1]:
                continue
            facts, hard = self.facts(env)
            assume = [l for a, v in facts.items() if (l := self.T.lit(a, v)) not in (None, False)]
            if not self.s.solve(assumptions=assume):
                continue  # записи противоречат базе: это ловит сверка библиотеки
            if all(self.entails(assume, a, v) for a, v in premises) and self.entails(assume, goal[0], not goal[1]):
                names = {str(t): self._name(im) for t, im in env.items()}
                used = [hard[a] for a in [x for x, _ in premises] + [goal[0]] if a in hard]
                out.append({"подстановка": names, **{m: [x for k, x in used if k == m] for m in MARKS}})
                if len(out) >= limit:
                    break
        return out

    def _name(self, im):
        if im[0] == "num":
            return str(im[1])
        if im[0] == "mor":
            _, kind, d, c, j = im
            nd, nc = (self.lib.obj[x].get("имя", x) for x in (d, c))
            if kind == "proj":
                return f"{nd} ↠ {nc} (фактор по {self.lib.obj[d]['подгруппы'][j].get('id')})"
            if kind == "incl":
                return f"{nd} ↪ {nc} (подгруппа {self.lib.obj[c]['подгруппы'][j].get('id')})"
            if kind == "end":
                e = self.lib.obj[d]["эндоморфизмы"][j]
                subs = self.lib.obj[d]["подгруппы"]
                nm = lambda i: self._name(("obj", subs[i]["≅"]))
                return f"эндоморфизм {nd}: ядро ≅ {nm(e['ker'])}, образ ≅ {nm(e['im'])}"
            return {"id": f"id: {nd} → {nc}", "zero": f"1: {nd} → {nc}",
                    "isoprof": f"{nd} ≅ {nc}^ (проконечное пополнение)", "cayley": f"Кэли {nd} → {nc}"}[kind]
        if im[0] == "obj":
            o = self.lib.obj[im[1]]
            return o.get("имя", im[1])
        if im[0] == "fam":
            return self.lib.fam[im[1]].get("имя", im[1])
        if im[0] == "diag":
            return self.lib.diag[im[1]].get("имя", im[1])
        if im[0] == "act":
            subs = self.lib.obj[im[1]]["подгруппы"]
            g = self._name(("obj", im[1]))
            return " ⊔ ".join(f"{g}/{subs[j].get('имя') or self._name(('obj', subs[j]['≅']))}" for j in im[2])
        if im[0] == "elt":
            c = self.lib.obj[im[1]]["элементы"][im[2]]
            if c.get("имя"):
                return ("ещё один элемент класса " if im[3:] else "") + c["имя"]
            o = "бесконечного порядка" if c["ord"] == 0 else f"порядка {c['ord']}"
            return ("ещё один элемент" if im[3:] else "элемент") + f" {o} (класс из {c['size']})"
        if im[0] == "pt":
            subs = self.lib.obj[im[1][1]]["подгруппы"]
            h = subs[im[1][2][im[2]]]
            return ("другая точка" if im[3:] else "точка") + f" со стабилизатором ≅ {self._name(('obj', h['≅']))}"
        s = self.lib.obj[im[1]]["подгруппы"][im[2]]
        return s.get("имя", self.lib.obj[s["≅"]].get("имя"))


def _init():
    global _LIB, _SCENE
    _LIB = Library()
    _SCENE = Scene(Vocab.section("grp"))


def _init_scene():
    global _SCENE
    _SCENE = Scene(Vocab.section("grp"))


MARKS_ORDER = {None: 0, "короткий довод": 1, "трудно": 2}


def _saturate(job):
    """Выведенные значения пары (G, N): свойства G с пометкой (или None) и
    свойства вложения N без пометок."""
    key, sub = job
    S, lib = _SCENE, _LIB
    o = lib.obj[key]
    ga = [("p", p, S.G) for p in LIB_GROUP_PROPS if p not in o["свойства"]]
    s = o["подгруппы"][sub] if sub is not None else None
    na = [("p", p, S.N) for p in SUB_PROPS if s is not None and p not in s["свойства"]]
    if not ga and not na:
        return key, sub, {}, {}
    if S.check(S.facts(lib, key, sub)) is not None:
        return key, sub, {}, {}  # противоречие покажет сверка
    grp, emb = {}, {}
    for drop, mark in ((MARKS, None), (("трудно",), "короткий довод"), ((), "трудно")):
        vals = S.values(lib, key, sub, need=ga + (na if mark is None else []), drop=drop)
        for a in ga:
            if a in vals and a[1] not in grp:
                grp[a[1]] = (vals[a], mark)
        if mark is None:
            emb = {a[1]: vals[a] for a in na if a in vals}
    return key, sub, grp, emb


def _audit(job):
    key, sub = job
    facts = _SCENE.facts(_LIB, key, sub)
    core = _SCENE.check(facts)
    if core is not None:
        return {"группа": key, "подгруппа": sub, "противоречие": [
            (f"{'' if v else '¬'}{a[1]}({', '.join(map(str, a[2:]))})", where) for a, v, where in core]}
    atoms = [a for a in _SCENE.atoms() if sub is not None or a[2] == _SCENE.G]
    derived = _SCENE.derive(facts, atoms)
    return {"группа": key, "подгруппа": sub, "выведено": {
        f"{a[1]}({', '.join(map(str, a[2:]))})": v for a, v in derived.items()}}


def jobs(lib, keys):
    for k in keys:
        yield k, None
        for i in range(len(lib.obj[k]["подгруппы"] or [])):
            yield k, i


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--конечные", dest="finite", type=int, default=0,
                    help="вместо бесконечных сверить столько случайных пар (G, N) из конечных")
    ap.add_argument("--нитей", dest="jobs", type=int, default=None)
    ap.add_argument("--json", dest="as_json", action="store_true")
    a = ap.parse_args()
    lib = Library()
    if a.finite:
        pairs = [j for j in jobs(lib, [k for k, o in lib.obj.items() if o["конечная"]])]
        work = random.Random(0).sample(pairs, a.finite)
    else:
        work = list(jobs(lib, lib.infinite()))
    with Pool(a.jobs, initializer=_init) as pool:
        report = pool.map(_audit, work, chunksize=1)
    if a.as_json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        return
    bad = [r for r in report if "противоречие" in r]
    print(f"сцен {len(report)}, противоречий {len(bad)}, выведено значений "
          f"{sum(len(r.get('выведено', {})) for r in report)}")
    for r in bad:
        sub = "" if r["подгруппа"] is None else f", N = {lib.obj[r['группа']]['подгруппы'][r['подгруппа']]['id']}"
        print(f"\n{r['группа']}{sub}:")
        for lit, where in r["противоречие"]:
            print(f"    {lit:40} ← {where}")


if __name__ == "__main__":
    main()


# --- кэш библиотеки -------------------------------------------------------------

CACHE = Path(__file__).resolve().parents[2] / "кэш"


def _fingerprint():
    """Хэш всего, от чего зависит построенная библиотека: данные и код."""
    import hashlib
    root = Path(__file__).resolve().parents[2]
    files = sorted([*(root / "data" / "finite").glob("*.json*"), root / "data" / "infinite" / "grp.json",
                    root / "data" / "infinite" / "countable.json",
                    root / "data" / "infinite" / "values.json",
                    root / "data" / "new" / "grp.json", root / "data" / "vocab" / "grp.json",
                    *(Path(__file__).parent / f for f in ("library.py", "logic.py", "finite.py"))])
    h = hashlib.sha256()
    for f in files:
        if f.exists():
            h.update(f.name.encode())
            h.update(f.read_bytes())
    return h.hexdigest()[:16]


def built_library(vocab=None):
    """Library с saturate() и synthesize_products(), из кэша на диске, если данные
    и код не менялись. Построение — пара минут, загрузка из кэша — секунды."""
    import pickle
    vocab = vocab or Vocab.section("grp")
    path = CACHE / f"библиотека-{_fingerprint()}.pickle"
    if path.exists():
        try:
            with open(path, "rb") as f:
                return pickle.load(f)
        except Exception:
            pass
    lib = Library()
    lib.saturate()
    lib.synthesize_products(vocab)
    lib.rank_products()
    try:
        CACHE.mkdir(exist_ok=True)
        for old in CACHE.glob("библиотека-*.pickle"):
            old.unlink()
        with open(path, "wb") as f:
            pickle.dump(lib, f, protocol=pickle.HIGHEST_PROTOCOL)
    except Exception as e:  # кэш — только ускорение
        print(f"кэш библиотеки не записан: {e}", file=sys.stderr)
    return lib
