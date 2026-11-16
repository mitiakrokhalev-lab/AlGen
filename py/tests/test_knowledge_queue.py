"""tools.knowledge_queue: объединение корней знаний схем (сумма запретов, число схем, группы, правила)."""
import gzip
import json
import tempfile
import unittest
from pathlib import Path

from tools.knowledge_queue import load, queue


class KnowledgeQueueTest(unittest.TestCase):
    def test_union_over_schemes(self):
        with tempfile.TemporaryDirectory() as d:
            for name, roots in (("S1.knowledge.json.gz", [["a(G)", "g0", 3], ["b(G)", "×", 2]]),
                                ("roots-S2.json.gz", [["a(G)", "g0", 1], ["a(G)", "g1", 5]])):
                with gzip.open(Path(d) / name, "wt", encoding="utf-8") as f:
                    json.dump({"оставленные после сжатия": roots, "все неизвестные": roots * 2}, f)
            files, per_root, schemes = load(d)
            q = queue(per_root, schemes)
        self.assertEqual(len(files), 2)
        self.assertEqual(per_root[("a(G)", "g0")], 4)
        self.assertEqual(q["корней"], 3)
        self.assertEqual((q["значений записанных групп"], q["правил для произведений"]), (2, 1))
        self.assertEqual(q["в нескольких схемах"], 1)
        self.assertEqual(q["топ корней"][0], {"корень": "a(G) у g1", "запретов": 5, "схем": 1})
        self.assertEqual(q["топ групп"][0], {"группа": "g1", "запретов": 5})
        self.assertEqual(q["топ правил"], [{"шаблон": "b(G)", "запретов": 2}])


if __name__ == "__main__":
    unittest.main()
