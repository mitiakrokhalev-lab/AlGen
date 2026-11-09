"""Долг закрывается только полным текущим поколением и проверенным базисом."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from algen import live_worker as W
from algen.compress_base import archive_questions, questions_hash
from algen.live import LiveArchive, dumps, write_report
from test_live import header, question, packet


GENERATION = dict(size=2, fast=True, k_spec="1", term_limit=None, skip=[], defer=0,
                  close_marked=True, compress=True, k=1, terms=["center(G)"])


class WorkerTest(unittest.TestCase):
    def test_native_source_change_invalidates_implementation(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            worker = root / "live_worker.py"
            worker.write_text("# worker\n")
            native = root / "native_enum.cpp"
            native.write_text("// version 1\n")
            with patch.object(W, "__file__", str(worker)):
                before = W.implementation_hash()
                native.write_text("// version 2\n")
                after = W.implementation_hash()
                self.assertNotEqual(before, after)
                (root / "native_enum.so").write_bytes(b"platform-specific compiled cache")
                self.assertEqual(after, W.implementation_hash())

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.db = self.root / "archive.sqlite"
        self.tables = self.root / "tables"
        self.tables.mkdir()
        (self.tables / "G.1-1.pickle").write_bytes(b"test table")
        with LiveArchive(self.db) as a:
            self.ctx = a.import_report(header(generation=GENERATION), [question("old", ["p", "¬q"])])
            a.apply_example(self.ctx, packet("C2", {"p": True, "q": False, "r": False}))
        self.m = W.create_plan(self.db, self.ctx, self.tables, self.root / "run")
        self.mode = "ok"

    def tearDown(self):
        self.tmp.cleanup()

    def runner(self, argv, env, log):
        root = Path(self.m["directory"])
        if "algen.table" in argv:
            sid = "S"
            # Старое p⇒q уже опровергнуто. Полный пересчёт нашёл p&r⇒q.
            rows = [question("new", ["p", "r", "¬q"]), question("same", ["p", "r", "¬q"])]
            rows[1]["класс"] = ["different", "class"]
            if self.mode == "missing":
                return
            if self.mode == "error_verdict":
                rows[0]["вердикт"] = "ОШИБКА: test"
            if self.mode == "error_compress":
                rows[0]["ОШИБКА сжатия"] = "test"
            if self.mode == "old_folded":
                rows[1].update({"свёрнута": True, "следует из": ["new"]})
            h = header(generation=GENERATION, library="L:dynamic:updated", worker_run=self.m["id"],
                       dynamic={"context": self.ctx, "revision": 1, "rows": 1})
            write_report(root / "results/S.archive.jsonl.gz", h, rows)
            summary = {"статус": "ok", "строк противоречат базе": 0, "отпечаток": h["library"],
                       "вердикты": {"неизвестно": 2}, "факты без посылок": []}
            if self.mode == "error_status":
                summary["статус"] = "ошибка"
            if self.mode == "wrong_counts":
                summary["вердикты"] = {"неизвестно": 3}
            (root / "results/S.json").write_text(dumps(summary))
            if self.mode == "truncated":
                p = root / "results/S.archive.jsonl.gz"
                p.write_bytes(p.read_bytes()[:-8])
            if self.mode == "changed":
                with LiveArchive(self.db) as a:
                    a.apply_example(self.ctx, packet("C3", {"p": False}))
            if self.mode == "new_scope":
                with LiveArchive(self.db) as a:
                    a.import_report(header("S2", generation=GENERATION), [])
        else:
            staged = argv[argv.index("--live-db") + 1]
            ctx = argv[argv.index("--live-context") + 1]
            with LiveArchive(staged) as a:
                qs = archive_questions(a, ctx)
            # Одинаковые запреты, но разные классы: этот шаг проверяет протокол;
            # настоящая SAT-проверка проверяется отдельно в test_compress.
            kept = [qs[0]["id"]]
            folded = {q["id"]: kept for q in qs[1:]}
            out = dict(context=ctx, theory="T", input_hash=questions_hash(qs), input_count=len(qs),
                       verify={"full": True, "checked": len(folded), "нарушений": 0},
                       **{"оставлено": kept, "свёрнуто": folded})
            if self.mode == "sampled":
                out["verify"]["full"] = False
            if self.mode == "incomplete_basis":
                out["свёрнуто"] = {}
                out["verify"]["checked"] = 0
            if self.mode == "bad_source":
                out["свёрнуто"][qs[1]["id"]] = ["not a question"]
            if self.mode == "theory_error":
                out["особые"] = {qs[0]["id"]: "ОШИБКА: следует из одной теории"}
            (root / "basis.json").write_text(dumps(out))

    def run_worker(self):
        return W.execute(self.db, self.m["id"], runner=self.runner)

    def test_complete_publish_retains_old_and_reopens_after_next_example(self):
        receipt = self.run_worker()
        target = receipt["target"]
        with LiveArchive(self.db) as a:
            self.assertEqual(a.stats(self.ctx)["states"], {"refuted": 1})
            self.assertEqual(a.stats(self.ctx)["successor"], target)
            self.assertEqual(a.stats(self.ctx)["pending"], [])
            self.assertEqual(a.stats(target)["pending"], [])
            self.assertEqual(a.stats(target)["states"], {"open": 1, "folded": 1})
            self.assertEqual(len(list(a.records(target, "S"))), 2)
            with self.assertRaisesRegex(ValueError, target):
                a.apply_example(self.ctx, packet("C3", {"p": False}))
            a.apply_example(target, packet("C3", {"p": True, "q": False, "r": True}))
            self.assertEqual(a.stats(target)["states"], {"refuted": 2})
            self.assertTrue(a.stats(target)["pending"])
            self.assertGreater(len(a.source_history(next(a.active_examples(target))["id"])), 1)
        self.assertEqual(self.run_worker(), receipt)  # идемпотентное завершение

    def test_failures_never_acknowledge_queue_or_publish_partial_context(self):
        for mode in ("missing", "error_status", "wrong_counts", "truncated", "error_verdict", "sampled",
                     "incomplete_basis", "bad_source", "error_compress", "theory_error"):
            with self.subTest(mode=mode):
                self.mode = mode
                with self.assertRaises((ValueError, EOFError, OSError)):
                    self.run_worker()
                with LiveArchive(self.db) as a:
                    self.assertTrue(a.stats(self.ctx)["pending"])
                    self.assertEqual(a.db.execute("SELECT count(*) FROM contexts").fetchone()[0], 1)
                    self.assertIsNone(a.stats(self.ctx)["successor"])
                    self.assertEqual(a.stats(self.ctx)["runs"][0]["status"], "failed")
        self.mode = "ok"
        self.run_worker()  # повтор после ошибок не требует удаления файлов

    def test_changed_input_and_new_scope_require_new_plan(self):
        self.mode = "changed"
        with self.assertRaisesRegex(ValueError, "изменилась"):
            self.run_worker()
        with LiveArchive(self.db) as a:
            self.assertEqual(a.stats(self.ctx)["revision"], 2)
            self.assertTrue(a.stats(self.ctx)["pending"])

    def test_new_scope_without_revision_change_invalidates_plan(self):
        self.mode = "new_scope"
        with self.assertRaisesRegex(ValueError, "изменилась"):
            self.run_worker()

    def test_existing_target_cannot_have_its_unplanned_updates_acknowledged(self):
        with LiveArchive(self.db) as a:
            target = a._context(header(library="L:dynamic:updated"))
            a.apply_example(target, packet("extra", {"p": False}))
        with self.assertRaisesRegex(ValueError, "уже существует"):
            self.run_worker()
        with LiveArchive(self.db) as a:
            self.assertTrue(a.stats(target)["pending"])
            self.assertTrue(a.stats(self.ctx)["pending"])
            self.assertEqual(list(a.records(target, "S")), [])

    def test_changed_table_or_code_and_snapshot_detected(self):
        with patch.object(W, "implementation_hash", return_value="different"):
            with self.assertRaisesRegex(ValueError, "код"):
                self.run_worker()
        with patch.object(W, "data_hash", return_value="different"):
            with self.assertRaisesRegex(ValueError, "данные"):
                self.run_worker()
        (self.tables / "G.1-1.pickle").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "таблицы"):
            self.run_worker()
        (self.tables / "G.1-1.pickle").write_bytes(b"test table")
        with open(self.root / "run/input.sqlite", "ab") as f:
            f.write(b"changed")
        with self.assertRaisesRegex(ValueError, "снимок"):
            self.run_worker()

    def test_lock_and_atomic_publish_rollback(self):
        with W.worker_lock(self.db):
            with self.assertRaisesRegex(ValueError, "другой worker"):
                self.run_worker()
        original = W.install_basis
        calls = []
        def fail_publish(a, ctx, basis):
            calls.append(ctx)
            original(a, ctx, basis)
            if len(calls) == 2:
                raise ValueError("publish failure")
        with patch.object(W, "install_basis", side_effect=fail_publish):
            with self.assertRaisesRegex(ValueError, "publish failure"):
                self.run_worker()
        with LiveArchive(self.db) as a:
            self.assertEqual(a.db.execute("SELECT count(*) FROM contexts").fetchone()[0], 1)
            self.assertTrue(a.stats(self.ctx)["pending"])

    def test_old_export_does_not_guess_generation(self):
        with LiveArchive(self.root / "old.sqlite") as a:
            ctx = a.import_report(header(), [])
            a.apply_example(ctx, packet("x", {}))
        with self.assertRaisesRegex(ValueError, "generation"):
            W.create_plan(self.root / "old.sqlite", ctx, self.tables, self.root / "old-run")

    def test_old_folded_are_in_full_verification_input(self):
        self.mode = "old_folded"
        self.assertEqual(self.run_worker()["basis_folded"], 1)

    def test_bad_export_moved_aside_for_real_producer_retry(self):
        root = self.root / "run"
        (root / "results").mkdir()
        self.mode = "truncated"
        self.runner(["algen.table"], {}, None)
        m = dict(self.m, example_count=1)
        W.prepare_resume(m, root / "results")
        self.assertFalse((root / "results/S.json").exists())
        self.assertEqual(len(list((root / "rejected").rglob("S.archive.jsonl.gz"))), 1)
        self.mode = "ok"
        self.runner(["algen.table"], {}, None)
        W.prepare_resume(m, root / "results")
        self.assertTrue((root / "results/S.json").exists())

    def test_receipt_disk_failure_does_not_revert_completed(self):
        original = Path.write_text
        def fail_receipt(p, *args, **kwargs):
            if p.name == "receipt.json":
                raise OSError("disk full")
            return original(p, *args, **kwargs)
        with patch.object(Path, "write_text", fail_receipt):
            receipt = self.run_worker()
            self.assertEqual(self.run_worker(), receipt)
        with LiveArchive(self.db) as a:
            self.assertEqual(a.stats(self.ctx)["runs"][0]["status"], "completed")

    def test_private_cache_wrapper_keeps_original_cache_and_cli_arguments(self):
        import os
        import sys
        from algen import library, live_exec
        original = self.root / "original-cache"
        private = self.root / "private-cache"
        original.mkdir()
        (original / "библиотека-fp.pickle").write_bytes(b"original")
        seen = []
        def entry(module, run_name):
            seen.append((module, run_name, sys.argv[1:], library.CACHE))
            self.assertEqual((library.CACHE / "библиотека-fp.pickle").read_bytes(), b"original")
        with patch.object(library, "CACHE", original), patch.object(library, "_fingerprint", return_value="fp"), \
                patch.dict(os.environ, ALGEN_WORKER_CACHE=str(private)), \
                patch.object(sys, "argv", ["live_exec", "algen.table", "перебор", "G"]), \
                patch.object(live_exec.runpy, "run_module", side_effect=entry):
            live_exec.main()
        self.assertEqual(seen, [("algen.table", "__main__", ["перебор", "G"], private)])
        self.assertEqual((original / "библиотека-fp.pickle").read_bytes(), b"original")


if __name__ == "__main__":
    unittest.main()
