"""Старый банк (словарь Python-чисел) против нового (numpy) на случайных теориях:
одинаковые ответы sat, первые свидетели и значения в моделях."""
import random
import unittest
from pysat.solvers import Solver
from algen import fast

class OldBank:
    def __init__(self, clauses, s, nclause):
        self.s, self.pos, self.neg, self.n, self.full, self.nclause, self.unsat = s, {}, {}, 0, 0, nclause, {}
    def _add(self, model):
        bit = 1 << self.n; self.n += 1; self.full |= bit
        for l in model:
            v = abs(l)
            if l > 0: self.pos[v] = self.pos.get(v, 0) | bit
            else: self.neg[v] = self.neg.get(v, 0) | bit
    def witness(self, lits):
        w = self.full
        for l in lits:
            v = abs(l)
            if v > self.nclause: continue
            w &= self.pos.get(v, 0) if l > 0 else self.neg.get(v, 0)
            if not w: return 0
        return w

class T:  # минимальная «теория» для Bank
    def __init__(self, clauses): self.clauses = clauses



class FastBankTest(unittest.TestCase):
    def test_numpy_bank_matches_dict_bank(self):
        """Новый банк (numpy) отвечает как прежний (словарь Python-чисел): есть ли
        свидетель, номер первого свидетеля, значение переменной в модели."""
        bad = 0
        for case in range(60):
            rnd = random.Random(case)
            nv = rnd.randint(5, 40)
            cl = [[rnd.choice([1, -1]) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 3))] for _ in range(rnd.randint(5, 80))]
            s1, s2 = Solver(name="g4", bootstrap_with=cl), Solver(name="g4", bootstrap_with=cl)
            new = fast.Bank(T(cl), s1)
            old = OldBank(cl, s2, new.nclause)
            for q in range(300):
                lits = [rnd.choice([1, -1]) * rnd.randint(1, nv + 3) for _ in range(rnd.randint(1, 4))]
                # одинаковая последовательность моделей: добавляем модель решателя в оба
                if rnd.random() < 0.2 and s1.solve(assumptions=[l for l in lits if abs(l) <= nv]):
                    m = s1.get_model(); new._add(m); old._add(m)
                w_old = old.witness(lits)
                if bool(w_old) != new.witness(lits): bad += 1
                if w_old and ((w_old & -w_old).bit_length() - 1) != new.first_witness(lits): bad += 1
                if new.n:
                    k = rnd.randrange(new.n); v = rnd.randint(1, nv + 3)
                    if bool((old.pos.get(v, 0) >> k) & 1) != new.value(v, k): bad += 1
        self.assertEqual(bad, 0)


    def test_ring_keeps_last_models(self):
        """Кольцо из cap моделей: свидетель есть ⇔ он есть среди последних cap
        добавленных; first_witness — место модели, где верны все литералы;
        value — значение в модели на этом месте. Строки, заведённые до и после
        вытеснения, одинаковы."""
        bad = 0
        for case in range(40):
            rnd = random.Random(1000 + case)
            nv = rnd.randint(5, 70)
            cl = [[rnd.choice([1, -1]) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 3))] for _ in range(rnd.randint(5, 80))]
            s = Solver(name="g4", bootstrap_with=cl)
            cap = rnd.choice([1, 3, 8, 64, 65, 130])
            b = fast.Bank(T(cl), s, cap=cap)
            slots = {}
            for q in range(400):
                lits = [rnd.choice([1, -1]) * rnd.randint(1, nv + 3) for _ in range(rnd.randint(1, 4))]
                if rnd.random() < 0.3:
                    s.set_phases([rnd.choice([1, -1]) * v for v in range(1, nv + 1)])
                    if s.solve(assumptions=[l for l in lits if abs(l) <= b.nclause]):
                        m = s.get_model()
                        slots[b.n % cap] = set(m)
                        b._add(m)
                live = [l for l in lits if abs(l) <= b.nclause]
                want = [k for k in sorted(slots) if all(l in slots[k] for l in live)]
                if bool(want) != b.witness(lits): bad += 1
                k = b.first_witness(lits)
                if (k is None) != (not want) or (k is not None and k != want[0]): bad += 1
                if slots:
                    k = rnd.choice(sorted(slots)); v = rnd.randint(1, nv + 3)
                    if (v in slots[k]) != b.value(v, k): bad += 1
            s.delete()
        self.assertEqual(bad, 0)


    def test_bank_outlives_its_solver(self):
        """Банк создан с временным решателем, решатель удалён (как в class_ok):
        следующий вопрос с живым решателем отвечается верно, а не «невыполнимо»
        от удалённого; без живого решателя — ошибка, а не ложный ответ."""
        cl = [[1, 2], [-1, 3], [-2, 3]]
        th = T(cl)
        fast._BANKS.pop(id(th), None)
        s1 = Solver(name="g4", bootstrap_with=cl)
        b = fast.bank(th, s1)
        s1.delete()
        s2 = Solver(name="g4", bootstrap_with=cl)
        self.assertEqual(fast.bank(th, s2).sat([3, -1])[0], True)  # банк пуст: отвечает решатель
        self.assertEqual(fast.bank(th, s2).sat([-3])[0], False)
        s2.delete()
        with self.assertRaises(RuntimeError):
            b.sat([1, 2, -3, 3])  # нет свидетеля, решатель удалён
        fast._BANKS.pop(id(th), None)


class LocalTest(unittest.TestCase):
    def test_local_unsat_is_sound_and_matches_subtheory(self):
        """Локальная теория — ровно клаузы над атомами термов схемы (с подтермами);
        «невыполнимо» локально ⇒ ядро невыполнимо и в полной теории; литералы вне
        локальной теории отбрасываются (запрос слабее)."""
        from algen.logic import App, Var, ClauseStore
        G = Var("G")
        A, B = App("f", (G,)), App("g", (G,))
        C2 = App("h", (A,))  # подтерм A входит в замыкание C2
        terms = [G, A, B, C2]
        for case in range(80):
            rnd = random.Random(case)
            atoms = [("p", f"q{i}", rnd.choice(terms)) for i in range(rnd.randint(4, 14))]
            th = T([])
            th.atoms, th.var = atoms, {a: i + 1 for i, a in enumerate(atoms)}
            nv = len(atoms)
            cl = [[rnd.choice([1, -1]) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 3))]
                  for _ in range(rnd.randint(3, 40))]
            th.clauses = ClauseStore(cl) if case % 2 else cl
            scheme = rnd.choice([[G, A], [G, C2], [G, B], [G]])
            loc = fast.Local(th, scheme)
            clos = set(scheme) | ({A} if C2 in scheme else set())
            inside = {i + 1 for i, a in enumerate(atoms) if a[2] in clos}
            want = [c for c in cl if all(abs(l) in inside for l in c)]
            self.assertEqual(sorted(map(sorted, ([int(loc.l2g[abs(x)]) * (1 if x > 0 else -1) for x in c] for c in loc.clauses))),
                             sorted(map(sorted, want)), case)
            full = Solver(name="g4", bootstrap_with=cl)
            for _ in range(40):
                lits = [rnd.choice([1, -1]) * rnd.randint(1, nv) for _ in range(rnd.randint(1, 4))]
                core = loc.unsat_core(lits)
                if core is not None:
                    self.assertTrue(set(core) <= set(lits))
                    self.assertFalse(full.solve(assumptions=core), (case, lits, core))
            full.delete()
            loc.delete()


class PackedColsTest(unittest.TestCase):
    def test_packed_matches_dense(self):
        """Таблица базы, упакованная по столбцам, отдаёт те же столбцы, строки и срезы."""
        import numpy as np
        from algen.table import PackedCols
        rng = np.random.default_rng(0)
        for _ in range(40):
            r, c = int(rng.integers(1, 300)), int(rng.integers(1, 200))
            d = rng.random((r, c)) < 0.3
            P = PackedCols(d)
            idx = rng.integers(0, c, size=int(rng.integers(1, 20)))
            self.assertTrue(np.array_equal(P[:, list(idx)], d[:, idx]))
            self.assertTrue(np.array_equal(P.cols(idx), d[:, idx]))
            j = int(rng.integers(0, c))
            self.assertTrue(np.array_equal(P[:, j], d[:, j]))
            self.assertTrue(np.array_equal(P[:, 1::2], d[:, 1::2]))
            self.assertTrue(np.array_equal(np.asarray(P), d))
            rows = rng.integers(0, r, size=5)
            self.assertTrue(np.array_equal(P[rows, list(idx)], d[rows][:, idx]))


if __name__ == "__main__":
    unittest.main()
