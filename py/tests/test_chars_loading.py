"""Строение конечных групп (grp-chars.jsonl): загрузка до неподвижной точки и устойчивость к
обрезанной строке (ревью 17.11: за один проход терялись 183 из 377 записей)."""
import json
import tempfile
import unittest
from pathlib import Path

from algen.finite import load_chars, _jsonl_records


class CharsLoadingTest(unittest.TestCase):
    def test_all_records_applied(self):
        from algen.library import Library
        lib = Library()
        ch = load_chars()
        missing = [k for k in ch if lib.obj.get(k, {}).get("подгруппы") is None]
        self.assertEqual(missing, [], "записи grp-chars.jsonl, не дошедшие до библиотеки")

    def test_broken_line_is_skipped(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "x.jsonl"
            p.write_text(json.dumps({"key": "a"}) + "\n" + '{"key": "b", "ord' + "\n", encoding="utf-8")
            self.assertEqual([r["key"] for r in _jsonl_records(p)], ["a"])
            self.assertEqual(list(load_chars(p)), ["a"])


if __name__ == "__main__":
    unittest.main()
