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

import argparse
import json
import random
import sys
from pathlib import Path
from multiprocessing import Pool

from .finite import FINITE_DERIVED, arith_props, arith_sub_props, load as load_finite, load_aut, load_compl, load_endo, load_elts, load_products
from .logic import DATA, App, Graph, Theory, Var, Vocab

INFINITE = DATA / "infinite" / "grp.json"
# Конечные множители произведений сверх малых и простых: A₄, S₄, SL(2, 3) (коммутант Q₈
# неабелев нильпотентен), SL(2, 5) (совершенная с центром).
EXTRA_FINITE = ("12:3", "24:12", "24:3", "120:5")
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
        compl, endo, elts = load_compl(), load_endo(), load_elts()
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
        self._aut_out()
        with open(infinite, encoding="utf-8") as f:
            raw = json.load(f)
            for r in raw["группы"]:
                self.obj[r["id"]] = {"key": r["id"], "конечная": False, **r}
        self.fam = {f["id"]: f for f in raw.get("семейства", [])}
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
        for o in self.obj.values():
            self._center_commutator(o)
        self._quantified_props()
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

    def _fam_props(self, f):
        """Свойство семейства — у всех членов: да, если у всех да; нет, если у
        кого-то нет; иначе неизвестно. finite-fam — конечно ли семейство."""
        ms = [self.obj[k] for k in f["члены"] if k in self.obj]
        props = {"finite-fam": not f["бесконечное"]}
        for p in GROUP_PROPS:
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
        if o.get("кручение") is None and p.get("abelian"):
            o["кручение"] = whole if p.get("periodic") else one if p.get("torsion-free") else None
        for f in ("центр", "коммутант", "кручение"):
            if f in o and o[f] is None:
                del o[f]

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
            for p in GROUP_PROPS:
                l = T.lit(("p", p, P))
                if not s.solve(assumptions=assume + [-l]):
                    props[p] = True
                elif not s.solve(assumptions=assume + [l]):
                    props[p] = False
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

        for p in GROUP_PROPS:
            put(p, self.G, o["свойства"], key)
        if sub is None:
            return out
        s = o["подгруппы"][sub]
        n = lib.obj[s["≅"]]
        for p in SUB_PROPS:
            put(p, self.N, s["свойства"], f"{key}/{s['id']}")
        for p in GROUP_PROPS:
            put(p, self.N, n["свойства"], f"{key}/{s['id']} ≅ {s['≅']}")
        if s.get("фактор"):
            q = lib.obj[s["фактор"]]
            for p in GROUP_PROPS:
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
        out = {}
        for a in atoms:
            if a in facts:
                continue
            l = self.T.lit(a)
            if not self.s.solve(assumptions=assume + [-l]):
                out[a] = True
            elif not self.s.solve(assumptions=assume + [l]):
                out[a] = False
        return out

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
        return ([("p", p, t) for t in (self.G, self.N, self.Q) for p in GROUP_PROPS]
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
               "exponent-2", "exponent-3", "clt",
               # 30.10: дедекиндовы, метабелевы, ступени ⩽ 2, аменабельные, левоупорядочиваемые
               "dedekind", "metabelian", "class-2", "amenable", "left-orderable")

_LIB = _SCENE = None


# --- поиск контрпримера на произвольной схеме -----------------------------------


# Множители построенных произведений для схем с несколькими группами.
CORE = ["2:1", "6:1", "60:5", "Z", "Q", "QmodZ", "Pruf2", "F2", "Foo", "UT3Z", "PSL2R", "BS23", "Ainf",
        "SumC2", "Tarski", "SL2Rcov"]


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
                or len(self.vars) > 2)
        # Для схем с несколькими группами — бесконечные и малые конечные.
        # Неразрешимые конечные порядка ⩽ 120 (A₅, S₅, SL(2, 5), …) нужны всегда.
        self.objects = [k for k, o in lib.obj.items()
                        if not many or (not o.get("синтез") and (
                            not o["конечная"] or int(k.split(":")[0]) <= max_order
                            or (o["свойства"].get("solvable") is False and int(k.split(":")[0]) <= 120)))]
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
            p = {"prod": lib.prod, "freeprod": lib.fprod, "wreath": lib.wreath}[t.op].get((ks[0], ks[1]))
            return ("obj", p) if p else None
        if t.op in ("aut", "ab", "inn") and self._obj(args[0]):
            o = lib.obj[self._obj(args[0])]
            k = o.get({"aut": "aut", "ab": "абелианизация", "inn": "inn"}[t.op])
            if not k and t.op in ("ab", "inn"):
                # Gᵃᵇ = G/G′, Inn(G) ≅ G/Z(G): фактор записанной подгруппы.
                sid = o.get("коммутант" if t.op == "ab" else "центр")
                s = next((x for x in o["подгруппы"] or [] if x["id"] == sid), None)
                k = s.get("фактор") if s else None
            return ("obj", k) if k else None
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
            if t.op == "ker":
                idx = {"zero": self._all(d), "id": self._one(d), "proj": j, "incl": self._one(d)}[kind]
                return ("sub", d, idx) if idx is not None else None
            idx = {"zero": self._one(c), "id": self._all(c), "proj": self._all(c), "incl": j}[kind]
            return ("sub", c, idx) if idx is not None else None
        if t.op in ("meet", "join") and len(args) == 3 and all(a and a[0] == "sub" for a in args[1:]):
            n, m = args[1], args[2]
            if n[1] != m[1]:
                return None
            key = n[1]
            one, whole = self._one(key), self._all(key)
            meet = t.op == "meet"
            if n[2] == m[2]:
                return n
            for a, b in ((n, m), (m, n)):
                if a[2] == one:
                    return a if meet else b
                if a[2] == whole:
                    return b if meet else a
            return None
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

    def _mor_facts(self, f):
        _, kind, d, c, j = f
        td = self.lib.obj[d]["свойства"].get("trivial")
        tc = self.lib.obj[c]["свойства"].get("trivial")
        if kind == "id":
            return {"injective": True, "surjective": True, "iso": True, "zero-mor": td}
        if kind == "zero":
            return {"zero-mor": True, "injective": td, "surjective": tc,
                    "iso": (td and tc) if td is not None and tc is not None else None}
        x = (self.lib.obj[d] if kind == "proj" else self.lib.obj[c])["подгруппы"][j]
        if kind == "proj":  # j — ядро, собственное и нетривиальное
            return {"injective": False, "surjective": True, "iso": False, "zero-mor": tc}
        return {"injective": True, "surjective": False, "iso": False, "zero-mor": td}

    def facts(self, env, terms=None):
        """{атом: значение} по записям библиотеки и {атом: (пометка, значение)}
        для значений с пометками из MARKS."""
        out, hard, subs, elts = {}, {}, {}, {}
        for t in terms or self.g.terms:
            im = self._image(t, env)
            if im is None:
                continue
            if im[0] in ("fam", "diag"):
                for p, v in (self.lib.fam if im[0] == "fam" else self.lib.diag)[im[1]]["свойства"].items():
                    if self.g.v.prop_fits(p, self.g.terms[t].sort):
                        out[("p", p, t)] = v
                continue
            if im[0] == "pt":
                continue
            if im[0] == "elt":
                c = self.lib.obj[im[1]]["элементы"][im[2]]
                for p, v in (("identity-elt", c["ord"] == 1), ("involution", c["ord"] == 2),
                             ("central-elt", c["size"] == 1), ("torsion-elt", True),
                             ("real-elt", c["real"]), ("commutator-elt", c["comm"]),
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

    def _embeds(self, ka, kb):
        lib = self.lib
        if ka == kb or ka == "1:1":
            return True
        oa, ob = lib.obj[ka], lib.obj[kb]
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
        if im[0] == "mor":
            _, kind, d, c, j = im
            nd, nc = (self.lib.obj[x].get("имя", x) for x in (d, c))
            if kind == "proj":
                return f"{nd} ↠ {nc} (фактор по {self.lib.obj[d]['подгруппы'][j].get('id')})"
            if kind == "incl":
                return f"{nd} ↪ {nc} (подгруппа {self.lib.obj[c]['подгруппы'][j].get('id')})"
            return {"id": f"id: {nd} → {nc}", "zero": f"1: {nd} → {nc}"}[kind]
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
            return ("ещё один элемент" if im[3:] else "элемент") + f" порядка {c['ord']} (класс из {c['size']})"
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
    ga = [("p", p, S.G) for p in GROUP_PROPS if p not in o["свойства"]]
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
    try:
        CACHE.mkdir(exist_ok=True)
        for old in CACHE.glob("библиотека-*.pickle"):
            old.unlink()
        with open(path, "wb") as f:
            pickle.dump(lib, f, protocol=pickle.HIGHEST_PROTOCOL)
    except Exception as e:  # кэш — только ускорение
        print(f"кэш библиотеки не записан: {e}", file=sys.stderr)
    return lib
