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
    def __init__(self, theory, solver):
        self.T = theory
        self.s = solver
        self.pos = {}  # переменная → битовое множество моделей, где она верна
        self.neg = {}
        self.n = 0
        self.full = 0
        self.unsat = {}  # frozenset литералов → ядро
        self.nclause = max((abs(l) for c in theory.clauses for l in c), default=0)
        rng = random.Random(1)
        self.phases = [[v if rng.random() < 0.5 else -v for v in range(1, self.nclause + 1)] for _ in range(4)]
        self.calls = 0

    def _add(self, model):
        bit = 1 << self.n
        self.n += 1
        self.full |= bit
        for l in model:
            v = abs(l)
            if l > 0:
                self.pos[v] = self.pos.get(v, 0) | bit
            else:
                self.neg[v] = self.neg.get(v, 0) | bit
        STATS["моделей"] += 1

    def witness(self, lits):
        """Битовое множество моделей банка, где верны все lits (переменные
        вне клауз свободны и не ограничивают)."""
        w = self.full
        for l in lits:
            v = abs(l)
            if v > self.nclause:
                continue
            w &= self.pos.get(v, 0) if l > 0 else self.neg.get(v, 0)
            if not w:
                return 0
        return w

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
