"""Exact compiled/Python comparisons and cancellation inside the native kernel."""
from itertools import product
import signal
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E, native_enum as N
from algen.conditions import PackedConditions
from test_enumerate import RandomForm


class NativeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if N.library() is None:
            raise unittest.SkipTest(N._unavailable)

    def test_all_outputs_and_repacking_match(self):
        for case in range(110):
            n = 35 if case == 109 else 4 + case % 7
            rows = (0, 1, 7, 65, 640)[case % 5]
            results = []
            for native in (False, True):
                f = RandomForm(np.random.default_rng(1100+case), n, rows,
                               req=case % 3 == 0, need=case % 4 == 0)
                if case % 6 == 0:
                    f.fixed = [0]
                if case % 11 == 0:
                    f.req = {1: {4}, 2: {2}}
                if case % 7 == 0:
                    f.pair_atoms = {0: {1, 2}}
                f.drop = {3} if case % 9 == 0 else set()
                with patch.object(E, "NATIVE_ENUM", native), patch.object(E, "VEC", True), \
                     patch.object(E, "PRUNE_FREE", case % 8 != 0), patch.object(E, "ZERO_PREMISES", case % 10 != 0):
                    alive, empty = E.enumerate_form(f, 2 if n == 35 else (case // 4) % 4)
                if native:
                    self.assertTrue(f.enumeration_engine.startswith("cpp:"))
                results.append((list(alive.items()), empty, f.n_alive))
            self.assertEqual(*results, msg=f"case {case}")

    def test_arbitrary_minimal_order_duplicates_and_independent_arrays(self):
        rng = np.random.default_rng(81)
        for case in range(30):
            alive = PackedConditions(8, 3, 65_536)
            for depth in rng.permutation(4).tolist():
                for prem in product(range(4), repeat=depth):
                    for goal in range(4):
                        if rng.integers(5) == 0:
                            alive[prem, goal] = int(rng.integers(65_537))
            source = list(alive.items())
            with patch.object(E, "NATIVE_MINIMAL", False):
                old = E.minimal(alive)
            with patch.object(E, "NATIVE_MINIMAL", True):
                new = E.minimal(alive)
            self.assertEqual(list(old.items()), list(new.items()))
            for depth, arrays in new.blocks.items():
                for a, original in zip(arrays, alive.blocks[depth]):
                    self.assertIsNot(a, original)
                if arrays[1]:
                    arrays[1][0] = (arrays[1][0]+1) % 65_537
            self.assertEqual(list(alive.items()), source)

    def test_custom_goals_and_missing_compiler_keep_python(self):
        for goals in ([0, 2, 4], [4, 2, 4], None):
            f = RandomForm(np.random.default_rng(8), 5, 8)
            with patch.object(E, "NATIVE_ENUM", True), patch.object(N, "library", return_value=None):
                actual, empty = E.enumerate_form(f, 2, goals=goals)
            self.assertEqual(f.enumeration_engine, "python")
            g = RandomForm(np.random.default_rng(8), 5, 8)
            with patch.object(E, "NATIVE_ENUM", False):
                expected, expected_empty = E.enumerate_form(g, 2, goals=goals)
            self.assertEqual((list(actual.items()), empty), (list(expected.items()), expected_empty))

    def test_python_alarm_interrupts_cpp_and_following_call_works(self):
        class Deadline(Exception):
            pass
        lib = N.library()
        original = lib.algen_enum
        entered = []
        def stop(*_):
            raise Deadline("native deadline")
        def timed(*args):
            entered.append(True)
            signal.setitimer(signal.ITIMER_REAL, .01)
            try:
                return original(*args)
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
        old_handler = signal.signal(signal.SIGALRM, stop)
        try:
            f = RandomForm(np.random.default_rng(21), 180, 640)
            with patch.object(E, "NATIVE_ENUM", True), patch.object(E, "VEC", True), patch.object(lib, "algen_enum", timed):
                with self.assertRaisesRegex(Deadline, "native deadline"):
                    E.enumerate_form(f, 3)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
        self.assertEqual(entered, [True])
        f = RandomForm(np.random.default_rng(2), 5, 8)
        with patch.object(E, "NATIVE_ENUM", True):
            E.enumerate_form(f, 2)
        self.assertTrue(f.enumeration_engine.startswith("cpp:"))
