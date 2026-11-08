"""Минимальность на месте: та же выдача, что прежний minimal, без копии условий."""
from itertools import product
import signal
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E, native_enum as N
from algen.conditions import PackedConditions
from test_enumerate import RandomForm


def snapshot(alive):
    return (list(alive.items()), len(alive), list(alive.blocks),
            {d: (k.typecode, v.typecode) for d, (k, v) in alive.blocks.items()})


def random_packed(rng, literals, max_premises, max_support, density):
    alive = PackedConditions(literals, max_premises, max_support)
    for depth in rng.permutation(max_premises + 1).tolist():
        for prem in product(range(min(literals, 10)), repeat=depth):
            for goal in range(min(literals, 10)):
                if rng.random() < density:
                    alive[prem, goal] = int(rng.integers(max_support + 1))
    return alive


class InplaceMinimalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if N.library() is None:
            raise unittest.SkipTest(N._unavailable)

    def check(self, make):
        with patch.object(E, "NATIVE_MINIMAL", False):
            expected = snapshot(E.minimal(make()))
        with patch.object(E, "NATIVE_MINIMAL", True):
            expected_native = snapshot(E.minimal(make()))
        self.assertEqual(expected, expected_native)
        for native in (True, False):
            alive = make()
            with patch.object(E, "NATIVE_MINIMAL", native):
                out = E.minimal(alive, inplace=True)
            self.assertIs(out, alive)
            self.assertEqual(snapshot(out), expected, msg=f"native={native}")

    def test_random_blocks_all_key_and_support_types(self):
        # 8 литералов -> ключ B/H; 40 -> I; поддержка B/H/I
        for case in range(60):
            literals = (8, 12, 40)[case % 3]
            max_premises = (1, 2, 3, 3)[case % 4]
            max_support = (200, 65_535, 70_000)[(case // 3) % 3]
            density = (0.05, 0.3, 0.9)[(case // 9) % 3]
            make = lambda seed=500 + case: random_packed(np.random.default_rng(seed), literals,
                                                         max_premises, max_support, density)
            self.check(make)

    def test_wide_keys_use_uint64(self):
        def make():
            rng = np.random.default_rng(9)
            alive = PackedConditions(20_000, 3, 9)
            for depth in (0, 1, 2, 3):
                seen = set()
                for _ in range(400):
                    prem = tuple(sorted(rng.choice(40, size=depth, replace=False).tolist()))
                    seen.add((prem, int(rng.integers(40))))
                for prem, goal in sorted(seen, key=lambda x: (x[0], x[1])):
                    alive[prem, goal] = int(rng.integers(10))
            # заведомо неминимальные: надмножества уже имеющихся
            return alive
        self.assertEqual(make().key_type, "Q")
        self.check(make)

    def test_real_enumeration_outputs(self):
        for case in range(40):
            def make(case=case):
                f = RandomForm(np.random.default_rng(3100 + case), 4 + case % 7, (1, 7, 65, 640)[case % 4],
                               req=case % 3 == 0, need=case % 4 == 0)
                with patch.object(E, "NATIVE_ENUM", True), patch.object(E, "VEC", True):
                    alive, _ = E.enumerate_form(f, case % 4)
                return alive
            self.check(make)

    def test_interrupt_leaves_conditions_unchanged(self):
        class Deadline(Exception):
            pass
        lib = N.library()
        original = lib.algen_minimal_inplace

        def timed(*args):
            signal.setitimer(signal.ITIMER_REAL, .002)
            try:
                return original(*args)
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)

        def stop(*_):
            raise Deadline("deadline")
        alive = big_packed()
        before = snapshot(alive)
        old = signal.signal(signal.SIGALRM, stop)
        try:
            with patch.object(lib, "algen_minimal_inplace", timed):
                with self.assertRaises(Deadline):
                    E.minimal(alive, inplace=True)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)
        self.assertEqual(snapshot(alive), before)
        # после прерывания тот же объект досчитывается верно
        with patch.object(E, "NATIVE_MINIMAL", False):
            expected = snapshot(E.minimal(big_packed()))
        self.assertEqual(snapshot(E.minimal(alive, inplace=True)), expected)


    def test_signal_after_compaction_waits_for_consistent_arrays(self):
        """Сигнал в окне между сжатием и обрезкой доставляется только после обрезки."""
        class Deadline(Exception):
            pass
        lib = N.library()
        original = lib.algen_minimal_inplace

        def late(mode, *args):
            result = original(mode, *args)
            if mode == 1:
                signal.raise_signal(signal.SIGALRM)  # сразу после сжатия, до обрезки
            return result

        def stop(*_):
            raise Deadline("deadline")
        with patch.object(E, "NATIVE_MINIMAL", False):
            expected = snapshot(E.minimal(big_packed()))
        alive = big_packed()
        old = signal.signal(signal.SIGALRM, stop)
        try:
            with patch.object(lib, "algen_minimal_inplace", late):
                with self.assertRaises(Deadline):
                    E.minimal(alive, inplace=True)
        finally:
            signal.signal(signal.SIGALRM, old)
        self.assertEqual(snapshot(alive), expected)

def big_packed():
    """~1 млн условий длины 3 и 20 тыс. длины 2 (часть третьих — их надмножества)."""
    from array import array
    rng = np.random.default_rng(77)
    alive = PackedConditions(200, 3, 1000)
    w = alive.width
    def codes(depth, count):
        prem = np.sort(rng.integers(0, 200, size=(count, depth)), axis=1)
        goal = rng.integers(0, 200, size=count)
        c = np.ones(count, dtype=np.uint64)
        for j in range(depth):
            c = (c << np.uint64(w)) | prem[:, j].astype(np.uint64)
        return np.unique((c << np.uint64(w)) | goal.astype(np.uint64))
    two = codes(2, 20_000)
    three = codes(3, 1_000_000)
    for depth, c in ((2, two), (3, three)):
        keys = array(alive.key_type); keys.frombytes(c.astype(np.dtype(alive.key_type)).tobytes())
        vals = array(alive.support_type); vals.frombytes(rng.integers(0, 1001, size=len(c)).astype(
            np.dtype(alive.support_type)).tobytes())
        alive.blocks[depth] = (keys, vals)
        alive.size += len(c)
    return alive

if __name__ == "__main__":
    unittest.main()
