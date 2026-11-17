"""tools.live_values: значение строки опровергает вопрос архива без перепрогона; снятие источника
возвращает его (динамический опыт 2б.4д)."""
import gzip
import json
import tempfile
import unittest
from pathlib import Path

from algen.live import LiveArchive, write_report
from tools.live_values import run

HEADER = {"base": "G", "class": "", "scheme": "S", "theory": "t", "library": "lib", "declaration": "∀ G : Grp",
          "variables": ["G"], "fixed": []}
REPORT = [
    {"вердикт": "неизвестно", "запрет": ["a(G)", "¬c(G)"], "класс": ["a(G)", "¬c(G)"], "№": "1", "вид": "A",
     "корни": ["c(G) у g0"]},
    {"вердикт": "неизвестно", "запрет": ["b(G)", "c(G)"], "класс": ["b(G)", "c(G)"], "№": "2", "вид": "C"},
]


class LiveValuesTest(unittest.TestCase):
    def test_value_refutes_and_withdraw_restores(self):
        with tempfile.TemporaryDirectory() as d:
            exp = Path(d) / "S.archive.jsonl.gz"
            write_report(exp, HEADER, REPORT)
            src = {"kind": "gap", "reference": "тест"}
            pkt = {"key": "g0", "assignment": {"G": "g0"}, "facts": {"a(G)": True, "c(G)": False}, "source": src}
            before, after, refuted = run(Path(d) / "a.db", exp, [pkt], out=lambda *_: None)
            self.assertEqual(before["states"], {"open": 2})
            self.assertEqual(after["states"], {"open": 1, "refuted": 1})
            self.assertEqual(refuted, [{"вопрос": "a(G) & ¬c(G)", "вид": "A", "строка": "g0"}])
            # значение, не делающее все литералы верными, не опровергает (неизвестное не опровергает)
            pkt2 = {"key": "g1", "assignment": {"G": "g1"}, "facts": {"b(G)": True}, "source": src}
            _, after2, refuted2 = run(Path(d) / "a.db", exp, [pkt2], out=lambda *_: None)
            self.assertEqual(after2["states"], {"open": 1, "refuted": 1})
            with LiveArchive(Path(d) / "a.db") as arc:
                ctx = arc.db.execute("SELECT id FROM contexts").fetchone()[0]
                self.assertEqual(arc.withdraw(ctx, "g0", src)["states"], {"open": 2})

    def test_row_facts_dump_and_packets_from_new_values(self):
        from types import SimpleNamespace
        import numpy as np
        from algen import table as T
        from algen.logic import Var
        from tools.live_values import packets_from_rows
        G = Var("G")
        atoms = [("p", x, G) for x in "abc"]

        def form(rows):
            m = np.zeros((len(rows), 6), dtype=bool)
            for r, row in enumerate(rows):
                for i, v in enumerate(row):
                    if v is not None:
                        m[r, 2 * i + (0 if v else 1)] = True
            return SimpleNamespace(atoms=atoms, m=m, envs=[{G: ("obj", f"g{r}")} for r in range(len(rows))],
                                   where=lambda r: f"G = g{r}")
        with tempfile.TemporaryDirectory() as d:
            old, new = Path(d) / "old.rows.jsonl.gz", Path(d) / "new.rows.jsonl.gz"
            T._write_row_facts(form([(True, None, None), (False, True, None)]), old, "fp0")
            T._write_row_facts(form([(True, None, False), (False, True, None)]), new, "fp1")
            packets, added, conflicts = packets_from_rows(old, new, "тест")
            self.assertEqual((len(packets), added, conflicts), (1, 1, []))
            self.assertEqual(packets[0]["facts"], {"a(G)": True, "c(G)": False})
            # значение «ложно» вместо «верно» — расхождение, пакета нет
            T._write_row_facts(form([(False, None, False), (False, True, None)]), new, "fp2")
            packets, added, conflicts = packets_from_rows(old, new, "тест")
            self.assertEqual((len(packets), len(conflicts)), (0, 1))

    def test_reclassify_by_new_rows(self):
        from types import SimpleNamespace
        import numpy as np
        from algen import table as T
        from algen.logic import Var
        from tools.live_values import reclassify
        G = Var("G")
        atoms = [("p", x, G) for x in "abc"]

        def form(rows):
            m = np.zeros((len(rows), 6), dtype=bool)
            for r, row in enumerate(rows):
                for i, v in enumerate(row):
                    if v is not None:
                        m[r, 2 * i + (0 if v else 1)] = True
            return SimpleNamespace(atoms=atoms, m=m, envs=[{G: ("obj", f"g{r}")} for r in range(len(rows))],
                                   where=lambda r: f"G = g{r}")
        with tempfile.TemporaryDirectory() as d:
            exp = Path(d) / "S.archive.jsonl.gz"
            write_report(exp, HEADER, REPORT)
            rows = Path(d) / "new.rows.jsonl.gz"
            # вопрос 1 (a, ¬c): в строке g0 c стало «верно» — строка выбывает; g1: a неизвестно, c ложно — A
            # вопрос 2 (b, c): был C; в g0 c стало «верно», b неизвестно — теперь A (ждёт b у g0), g1 выбывает
            T._write_row_facts(form([(True, None, True), (None, False, False)]), rows, "fp")
            with LiveArchive(Path(d) / "a.db") as arc:
                with gzip.open(exp, "rt", encoding="utf-8") as f:
                    header = json.loads(next(f))["header"]
                    ctx = arc.import_report(header, (json.loads(s) for s in f if s.strip()))
                res = reclassify(arc, ctx, rows)
            self.assertEqual(sorted((o, n, k) for o, n, k in res.values()), [("A", "A", 1), ("C", "A", 1)])


if __name__ == "__main__":
    unittest.main()
