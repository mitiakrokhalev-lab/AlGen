"""Быстрый вывод: банк моделей теории вместо SAT на каждый вопрос.

Каждый вопрос `decide` сводится к вопросам выполнимости: «совместны ли
литералы L с теорией?». Если в банке есть модель, где верны все L, ответ «да»
получается без решателя: это AND битовых столбцов банка. Решатель
вызывается, только когда свидетеля в банке нет. Если ответ решателя «да», его
модель идёт в банк, и она закрывает потом тысячи других вопросов. Ответ
«нет» кэшируется вместе с ядром.

Ответы те же, что у `logic.decide`: модель из банка — настоящая модель
теории. Отличаться могут только ядра выводов, если решатель найдёт другое
ядро.

    from algen import fast; fast.install()   # E.decide → банк
"""

import random

from .logic import Verdict
from . import logic

_BANKS = {}  # id(теории) → Bank
STATS = {"вопросов": 0, "из банка": 0, "решатель": 0, "кэш": 0, "моделей": 0}


class Bank:
    """Модели — столбцами битов: строка матрицы на переменную, бит на модель
    (numpy uint64; прежде — словарь Python-чисел, и добавление модели обходило
    все переменные циклом Python: у базы n 0,47 с на модель). Модели и ответы те же."""

    def __init__(self, theory, solver):
        import numpy as np
        self.np = np
        self.T = theory
        self.s = solver
        self.n = 0
        self.unsat = {}  # frozenset литералов → ядро
        self.nclause = logic.clause_max_var(theory.clauses)
        self.P = np.zeros((self.nclause + 1, 1), dtype=np.uint64)  # переменная верна в модели
        self.N = np.zeros((self.nclause + 1, 1), dtype=np.uint64)  # переменная ложна
        rng = random.Random(1)
        self.phases = [[v if rng.random() < 0.5 else -v for v in range(1, self.nclause + 1)] for _ in range(4)]
        self.calls = 0

    def _add(self, model):
        np = self.np
        word, bit = divmod(self.n, 64)
        if word >= self.P.shape[1]:
            grow = self.P.shape[1]
            self.P = np.hstack([self.P, np.zeros_like(self.P[:, :grow])])
            self.N = np.hstack([self.N, np.zeros_like(self.N[:, :grow])])
        m = np.asarray(model, dtype=np.int64)
        top = int(np.abs(m).max()) if len(m) else 0
        if top >= self.P.shape[0]:  # переменные вне клауз тоже храним (их значение нужно value)
            extra = top + 1 - self.P.shape[0]
            self.P = np.vstack([self.P, np.zeros((extra, self.P.shape[1]), dtype=np.uint64)])
            self.N = np.vstack([self.N, np.zeros((extra, self.N.shape[1]), dtype=np.uint64)])
        b = np.uint64(1 << bit)
        self.P[m[m > 0], word] |= b
        self.N[-m[m < 0], word] |= b
        self.n += 1
        STATS["моделей"] += 1

    def _witness_words(self, lits):
        np = self.np
        nw = (self.n + 63) // 64
        if not nw:
            return None
        w = np.full(nw, np.uint64(0xFFFFFFFFFFFFFFFF))
        r = self.n % 64
        if r:
            w[-1] = np.uint64((1 << r) - 1)
        for l in lits:
            v = abs(l)
            if v > self.nclause:
                continue
            w &= (self.P if l > 0 else self.N)[v, :nw]
            if not w.any():
                return None
        return w

    def witness(self, lits):
        """Есть ли в банке модель, где верны все lits (переменные вне клауз свободны)."""
        return self._witness_words(lits) is not None

    def first_witness(self, lits):
        """Номер первой модели банка, где верны все lits, или None."""
        w = self._witness_words(lits)
        if w is None:
            return None
        i = int(self.np.flatnonzero(w)[0])
        x = int(w[i])
        return 64 * i + (x & -x).bit_length() - 1

    def value(self, v, k):
        """Значение переменной v в модели k (нет в модели — False, как прежде)."""
        if v >= self.P.shape[0]:
            return False
        return bool((int(self.P[v, k // 64]) >> (k % 64)) & 1)

    def sat(self, lits):
        """(выполнимо?, ядро при «нет»)."""
        STATS["вопросов"] += 1
        lits = [l for l in lits if abs(l) <= self.nclause]
        if self.witness(lits):
            STATS["из банка"] += 1
            return True, None
        key = frozenset(lits)
        if key in self.unsat:
            STATS["кэш"] += 1
            return False, self.unsat[key]
        STATS["решатель"] += 1
        # разнообразие моделей: случайная фаза у решателя
        if self.calls % 8 == 0:  # фаза меняется раз в 8 вызовов: список дорог
            try:
                self.s.set_phases(self.phases[(self.calls // 8) % len(self.phases)])
            except Exception:
                pass
        self.calls += 1
        if self.s.solve(assumptions=lits):
            self._add(self.s.get_model())
            return True, None
        core = self.s.get_core() or []
        self.unsat[key] = core
        return False, core


def bank(theory, solver):
    b = _BANKS.get(id(theory))
    if b is None or b.T is not theory:
        b = _BANKS[id(theory)] = Bank(theory, solver)
    return b


def decide(theory, premises, goal, solver=None):
    """То же, что `logic.decide`, но через банк моделей."""
    own = solver is None
    s = solver or theory.solver()
    try:
        b = bank(theory, s)
        assume = {}
        for a, v in premises:
            l = theory.lit(a, v)
            if l is None:
                continue
            if l is False:
                return Verdict("противоречие", [(a, v)])
            assume[l] = (a, v)
        lits = list(assume)
        ok, core = b.sat(lits)
        if not ok:
            return Verdict("противоречие", [assume[l] for l in core if l in assume])
        g = theory.lit(*goal)
        if g is None:
            return Verdict("выводится", [])
        if g is False:
            return Verdict("опровергается", [])
        ok, core = b.sat(lits + [-g])
        if not ok:
            return Verdict("выводится", [assume[l] for l in core if l in assume])
        ok, core = b.sat(lits + [g])
        if not ok:
            return Verdict("опровергается", [assume[l] for l in core if l in assume])
        return Verdict("неизвестно")
    finally:
        if own:
            _BANKS.pop(id(theory), None)
            s.delete()


def install():
    """Подменить decide во всех модулях перебора."""
    from . import enumerate as E
    E.decide = decide
    logic.decide_slow = logic.decide
