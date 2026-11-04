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


if __name__ == "__main__":
    unittest.main()
