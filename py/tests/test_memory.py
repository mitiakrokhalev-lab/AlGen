"""Потоковая перепаковка и пропуск пустой проверки сохраняют весь результат."""

import io
import json
from pathlib import Path
import pickle
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np

from algen import enumerate as E, table
from algen.library import Library
from algen.logic import Vocab


class PackedTableTest(unittest.TestCase):
    def test_all_bits_across_unaligned_parts_and_blocks(self):
        rng = np.random.default_rng(241)
        for width in (0, 1, 7, 8, 9, 17, 64, 65, 97):
            for count in (0, 1, 7, 8, 9, 31, 129):
                dense = rng.integers(0, 2, size=(count, width), dtype=np.uint8).view(bool)
                cuts = sorted({0, min(1, count), min(7, count), min(11, count), count})
                parts = [np.packbits(dense[a:b], axis=1) for a, b in zip(cuts, cuts[1:])]
                if not parts:
                    parts = [np.empty((0, (width+7)//8), dtype=np.uint8)]
                parts.insert(1, np.empty((0, (width+7)//8), dtype=np.uint8))
                original = [p.copy() for p in parts]
                old = table.PackedCols(dense)
                new = table.PackedCols.from_packed_rows(parts, width, block_bytes=max(1, width*16))
                self.assertEqual(new.shape, old.shape)
                self.assertEqual(new.dtype, old.dtype)
                np.testing.assert_array_equal(new.bits, old.bits)
                np.testing.assert_array_equal(table.PackedCols.from_packed_rows(iter(parts), width).bits, old.bits)
                np.testing.assert_array_equal(np.asarray(new), dense)
                if width:
                    np.testing.assert_array_equal(new.cols([width-1, 0, 0]), old.cols([width-1, 0, 0]))
                    np.testing.assert_array_equal(new.cols(0), dense[:, 0])
                    np.testing.assert_array_equal(new.cols(slice(0, width, 2)), old.cols(slice(0, width, 2)))
                for p, saved in zip(parts, original):
                    np.testing.assert_array_equal(p, saved)

    def test_unpack_is_bounded_instead_of_whole_dense_table(self):
        dense = np.random.default_rng(15).integers(0, 2, size=(1003, 97), dtype=np.uint8)
        packed = np.packbits(dense, axis=1)
        with patch.object(np, "unpackbits", wraps=np.unpackbits) as unpack:
            result = table.PackedCols.from_packed_rows([packed[:37], packed[37:38], packed[38:]], 97, block_bytes=97*16)
        self.assertGreater(unpack.call_count, 1)
        self.assertLessEqual(max(c.args[0].shape[0] for c in unpack.call_args_list), 16)
        np.testing.assert_array_equal(np.asarray(result), dense)

    def test_real_table_loader_keeps_all_three_matrices_and_metadata(self):
        rng = np.random.default_rng(26)
        dense = {k: rng.integers(0, 2, size=(29, 18), dtype=np.uint8) for k in "mse"}
        with tempfile.TemporaryDirectory() as tmp:
            for i, (a, b) in enumerate(((0, 3), (3, 14), (14, 29)), 1):
                data = dict(отпечаток="fp", атомов=9, envs=list(range(a, b)), skipped=[])
                data.update({k: np.packbits(mat[a:b], axis=1) for k, mat in dense.items()})
                with open(Path(tmp) / f"G.{i}-3.pickle", "wb") as f:
                    pickle.dump(data, f)
            forms = []
            for streaming in (False, True):
                with patch.object(table, "skeleton", side_effect=lambda *a: SimpleNamespace(atoms=[None]*9)), \
                        patch.object(table, "_fp", return_value="fp"), patch.object(table, "PACKED", True), \
                        patch.object(table, "STREAM_TABLE", streaming):
                    forms.append(table.load(None, None, "G", tmp))
            self.assertEqual(forms[0].envs, forms[1].envs)
            self.assertEqual(forms[0].names, forms[1].names)
            for k, mat in dense.items():
                np.testing.assert_array_equal(getattr(forms[0], k).bits, getattr(forms[1], k).bits)
                np.testing.assert_array_equal(np.asarray(getattr(forms[1], k)), mat)


class DegenerationCacheTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib, cls.vocab = Library(), Vocab.section("grp")

    def make_form(self, decl, terms):
        f = E.SchemeForm(self.lib, self.vocab, decl, terms, with_rows=False)
        f.search.objects = ["1:1", "2:1", "6:1"]
        f.fill_rows()
        self.addCleanup(f.sc.s.delete)
        self.addCleanup(f.search.s.delete)
        return f

    def test_real_reports_and_cores_identical_with_empty_or_nonempty_targets(self):
        for decl, terms, k, empty in (("∀ G : Grp", ["center(G)"], 1, True),
                                       ("∀ G : Grp; ∀ N : Sub(G)", [], 1, False)):
            outcomes, target_calls = [], []
            for legacy in (True, False):
                form = self.make_form(decl, terms)
                with patch.object(E, "LEGACY_EMPTY_DEGEN_CACHE", legacy), \
                        patch.object(E, "none_derivable", wraps=E.none_derivable) as check:
                    _, alive, no_example, report = E.run(k, self.lib, self.vocab, form)
                    summary = E.render(form, alive, no_example, report, out=io.StringIO(), err=io.StringIO())
                outcomes.append((list(alive.items()), no_example, json.dumps(report, ensure_ascii=False, sort_keys=True), summary))
                target_calls.append(check.call_count)
            self.assertEqual(outcomes[0], outcomes[1])
            if empty:
                self.assertGreater(target_calls[0], 0)
                self.assertEqual(target_calls[1], 0)
            else:
                self.assertGreater(target_calls[0], 0)
                self.assertEqual(target_calls[0], target_calls[1])


class ProfilerTest(unittest.TestCase):
    def test_relative_paths_and_budget_stop_are_recorded_without_leaking_child(self):
        from tools import profile_memory as P
        captured = []
        class Process:
            pid = 12345
            returncode = None
            def __init__(self, cmd, **kwargs):
                captured.append(cmd)
                destination = Path(cmd[cmd.index("--out")+1]) / "results"
                destination.mkdir()
                (destination / "S.json").write_text('{"статус":')  # остановлен посреди записи
            def poll(self):
                return self.returncode
            def terminate(self):
                self.terminated = True
            def wait(self, timeout=None):
                if timeout:
                    raise subprocess.TimeoutExpired("test", timeout)
                return self.returncode
            def kill(self):
                self.returncode = -9
        with tempfile.TemporaryDirectory() as tmp:
            argv = ["profile", "--tables", "tabs", "--skel", "skel", "--library-cache", "cache", "--scheme", "S",
                    "--out", "profile", "--rss-gib", "0.001", "--table-only"]
            with patch.object(sys, "argv", argv), patch("os.getcwd", return_value=tmp), \
                    patch.object(P.subprocess, "Popen", Process), patch.object(P, "rss", return_value={"VmRSS": 99999}), \
                    patch.object(P.resource, "getrusage", return_value=SimpleNamespace(ru_utime=0, ru_stime=0, ru_maxrss=99999)), \
                    patch("sys.stdout", io.StringIO()):
                P.main()
            for flag, folder in (("--tables", "tabs"), ("--skel", "skel"), ("--library-cache", "cache"), ("--out", "profile")):
                self.assertEqual(captured[0][captured[0].index(flag)+1], str(Path(tmp)/folder))
            result = json.loads((Path(tmp)/"profile/measurement.json").read_text())
            self.assertEqual(result["returncode"], -9)
            self.assertEqual(result["stop_reason"], "rss_budget:forced_kill")
            self.assertFalse(result["complete"])
            self.assertIn("summary_error", result)


if __name__ == "__main__":
    unittest.main()
