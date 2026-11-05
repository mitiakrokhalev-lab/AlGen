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


import os

BANK_MODELS = int(os.environ.get("ALGEN_BANK_MODELS", "4096"))  # моделей в банке (кольцо)


class Bank:
    """Модели теории. Каждая модель хранится целиком: бит на переменную
    (переменные — атомы каркаса, у G их 1,24 млн; модель решателя полная, так
    что «ложно» = «не верно» и отдельная матрица N не нужна). Для переменных,
    о которых спрашивали, держатся строки: бит на модель (numpy uint64),
    вопрос «есть ли модель с L» — AND строк. Строка новой переменной
    собирается из сохранённых моделей. Моделей не больше BANK_MODELS: дальше
    новая модель занимает место самой старой. Прежде строки шли на все
    переменные (P и N) и росли удвоением с копией — в пилоте 10 банк падал по
    памяти уже на одной схеме. Ответы sat те же; first_witness до заполнения
    кольца — та же модель, после — какая-то модель с L (банк ей и служит)."""

    def __init__(self, theory, solver, cap=None):
        import numpy as np
        self.np = np
        self.T = theory
        self.s = solver
        self.n = 0  # моделей добавлено всего
        self.cap = cap or BANK_MODELS
        self.W = (self.cap + 63) // 64
        self.unsat = {}  # frozenset литералов → ядро
        self.nclause = max((abs(l) for c in theory.clauses for l in c), default=0)
        self.nb = (self.nclause + 1 + 7) // 8
        self.M = np.zeros((self.cap, self.nb), dtype=np.uint8)  # модели (страницы памяти — по мере записи)
        self.extra = [frozenset()] * self.cap  # верные переменные вне клауз (нужны value)
        self.idx = {}  # переменная → строка R
        self.vars = np.zeros(0, dtype=np.int64)  # переменные строк R по порядку
        self.R = np.zeros((0, self.W), dtype=np.uint64)  # строка: бит k — переменная верна в модели k
        rng = random.Random(1)
        self.phases = [[v if rng.random() < 0.5 else -v for v in range(1, self.nclause + 1)] for _ in range(4)]
        self.calls = 0

    @property
    def valid(self):
        return min(self.n, self.cap)

    def _row(self, v):
        r = self.idx.get(v)
        if r is not None:
            return r
        np = self.np
        r = self.idx[v] = len(self.vars)
        if r >= self.R.shape[0]:
            self.R = np.vstack([self.R, np.zeros((max(64, self.R.shape[0]), self.W), dtype=np.uint64)])
        self.vars = np.append(self.vars, v)
        k = self.valid
        if k:
            bits = (self.M[:k, v >> 3] >> np.uint8(7 - (v & 7))) & np.uint8(1)
            words = np.zeros(self.W * 64, dtype=np.uint8)
            words[:k] = bits
            self.R[r] = np.packbits(words, bitorder="little").view(np.uint64)
        return r

    def _add(self, model):
        np = self.np
        m = np.asarray(model, dtype=np.int64)
        if len(m) < self.nclause:
            raise RuntimeError("неполная модель решателя: банк требует значения всех переменных клауз")
        slot = self.n % self.cap
        pos = m[m > 0]
        inside = pos[pos <= self.nclause]
        row = np.zeros(self.nb * 8, dtype=bool)
        row[inside] = True
        self.M[slot] = np.packbits(row)  # бит v — старший-первый: (byte v>>3) >> (7 - v&7)
        self.extra[slot] = frozenset(pos[pos > self.nclause].tolist())
        nr = len(self.vars)
        if nr:
            word, bit = divmod(slot, 64)
            b = np.uint64(1 << bit)
            col = self.R[:nr, word] & ~b
            self.R[:nr, word] = col | (row[self.vars].astype(np.uint64) * b)
        self.n += 1
        STATS["моделей"] += 1

    def _witness_words(self, lits):
        np = self.np
        k = self.valid
        if not k:
            return None
        nw = (k + 63) // 64
        w = np.full(nw, np.uint64(0xFFFFFFFFFFFFFFFF))
        r = k % 64
        if r:
            w[-1] = np.uint64((1 << r) - 1)
        for l in lits:
            v = abs(l)
            if v > self.nclause:
                continue
            r = self._row(v)  # до чтения self.R: _row может его заменить
            row = self.R[r, :nw]
            w &= row if l > 0 else ~row
            if not w.any():
                return None
        return w

    def witness(self, lits):
        """Есть ли в банке модель, где верны все lits (переменные вне клауз свободны)."""
        return self._witness_words(lits) is not None

    def first_witness(self, lits):
        """Номер (место в кольце) первой модели банка, где верны все lits, или None."""
        w = self._witness_words(lits)
        if w is None:
            return None
        i = int(self.np.flatnonzero(w)[0])
        x = int(w[i])
        return 64 * i + (x & -x).bit_length() - 1

    def value(self, v, k):
        """Значение переменной v в модели k (нет в модели — False, как прежде)."""
        if v > self.nclause:
            return v in self.extra[k]
        if v <= 0:
            return False
        return bool((int(self.M[k, v >> 3]) >> (7 - (v & 7))) & 1)

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
        ans = self.s.solve(assumptions=lits)
        if ans is None:  # pysat на удалённом решателе молча отвечает None — это не «невыполнимо»
            raise RuntimeError("решатель банка не ответил (удалён?)")
        if ans:
            self._add(self.s.get_model())
            return True, None
        core = self.s.get_core() or []
        self.unsat[key] = core
        return False, core


def bank(theory, solver):
    b = _BANKS.get(id(theory))
    if b is None or b.T is not theory:
        b = _BANKS[id(theory)] = Bank(theory, solver)
    elif solver is not None and b.s is not solver:
        # Банк живёт дольше решателя, с которым создан (generic_filter.class_ok
        # заводит временный решатель и удаляет его): спрашивать всегда тот
        # решатель, что передан сейчас. Модели банка — модели теории, им всё равно.
        b.s = solver
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
