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


if __name__ == "__main__":
    unittest.main()
