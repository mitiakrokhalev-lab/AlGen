import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tools import stress_summary as S


class StressSummaryTest(unittest.TestCase):
    def write_case(self, root, sid, **changes):
        folder = root / sid
        (folder / "results").mkdir(parents=True, exist_ok=True)
        m = dict(scheme=sid, scope="full native scheme", complete=True, returncode=0,
                 scheme_status="ok", stop_reason="exited", saved_report=True,
                 limits=dict(seconds=1200, rss_gib=12),
                 wall_seconds=5, cpu_seconds=4, peak_rss_kib=1024)
        m.update(changes)
        rows = [{"№": "a", "класс": ["X"], "вердикт": "опровергается"},
                {"№": "a", "класс": ["X"], "вердикт": "неизвестно", "свёрнута": True, "следует из": ["b"]},
                {"№": "b", "класс": ["Y"], "вердикт": "неизвестно"},
                {"№": "c", "класс": ["Z"], "вердикт": "неизвестно", "свёрнута": True, "следует из": ["b"]}]
        data = b"".join((json.dumps(r, ensure_ascii=False, sort_keys=True)+"\n").encode() for r in rows)
        with gzip.open(folder / "report.jsonl.gz", "wb") as f:
            f.write(data)
        (folder / "stages.jsonl").write_text(json.dumps(dict(stage="run:end", report_rows=4,
                                                           report_sha256=hashlib.sha256(data).hexdigest())))
        (folder / "measurement.json").write_text(json.dumps(m))
        (folder / "results" / (sid + ".json")).write_text(json.dumps({
            "id": sid, "условие": "∀ G : Grp", "статус": "ok", "строк противоречат базе": 0, "отпечаток": "F:3", "посылок": 3, "термы": [],
            "вердикты": {"неизвестно": 2, "опровергается": 1}, "оставленные вопросы": [{"№": "b"}],
            "свёрнуто": {"a": ["b"], "c": ["b"]}}))
        return folder

    def plan(self, *ids):
        return dict(name="test", scope="selected schemes", native_fingerprint="F", k=3,
                    seconds_per_process=1200, rss_gib=12, cases=[dict(id=s, terms=[]) for s in ids])

    def test_all_planned_cases_and_costs_including_stops_and_missing(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.write_case(root, "G-1")
            self.write_case(root, "G-2", complete=False, stop_reason="time_budget", wall_seconds=10, cpu_seconds=9)
            d = S.collect(self.plan("G-1", "G-2", "G-3"), root)
            self.assertEqual(d["outcomes"], {"ok": 1, "incomplete": 1, "missing": 1})
            self.assertEqual(d["planned"], 3)
            self.assertFalse(d["all_complete"])
            self.assertEqual(d["measurements_all_observed"]["wall_seconds"], {"observed": 2, "value": 15})
            self.assertEqual(d["measurements_all_observed"]["cpu_seconds"]["value"], 13)
            self.assertEqual((d["unknown_ids_ok"], d["kept_ids_ok"], d["within_scheme_ratio_ok"]), (3, 1, 3))
            self.assertEqual(d["cases"][0]["first_class_verdicts"]["неизвестно"], 2)
            self.assertIn("G-3", S.markdown(d))
            self.write_case(root, "G-2", wall_seconds=5000, peak_rss_kib=30*1024**2)
            self.assertEqual(S.collect(self.plan("G-2"), root)["outcomes"], {"incomplete": 1})

    def test_corrupt_inconsistent_or_failed_outputs_never_count_as_ok(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for mode in ("missing_raw", "truncated", "bad_deflate", "bad_hash", "error_row", "bad_partition", "fake_folding", "bad_source", "fake_instance", "bad_exit", "bad_limits", "bad_terms"):
                with self.subTest(mode=mode):
                    folder = self.write_case(root, "G-1")
                    report = folder / "report.jsonl.gz"
                    if mode == "missing_raw":
                        report.rename(folder / "saved.gz")
                    elif mode == "truncated":
                        report.write_bytes(report.read_bytes()[:-8])
                    elif mode == "bad_deflate":
                        data = bytearray(gzip.compress(b'abc')); data[10] = 0x07
                        report.write_bytes(data)
                    elif mode == "bad_hash":
                        (folder / "stages.jsonl").write_text(json.dumps(dict(stage="run:end", report_rows=4, report_sha256="bad")))
                    elif mode == "error_row":
                        with gzip.open(report, "wt") as f:
                            f.write(json.dumps({"вердикт": "неизвестно", "ОШИБКА сжатия": "bad"})+"\n")
                    elif mode == "bad_partition":
                        p = folder / "results/G-1.json"
                        d = S.read(p); d["свёрнуто"] = {}; p.write_text(json.dumps(d))
                    elif mode == "fake_folding":
                        p = folder / "results/G-1.json"
                        d = S.read(p); d["оставленные вопросы"] = []; d["свёрнуто"]["b"] = ["a"]; p.write_text(json.dumps(d))
                    elif mode in ("bad_source", "fake_instance"):
                        with gzip.open(report, "rt") as f:
                            rows = [json.loads(line) for line in f]
                        deps = ["nonexistent-source" if mode == "bad_source" else "экземпляр: X"]
                        rows[1]["следует из"] = deps
                        data = b"".join((json.dumps(r)+"\n").encode() for r in rows)
                        with gzip.open(report, "wb") as f:
                            f.write(data)
                        (folder / "stages.jsonl").write_text(json.dumps(dict(stage="run:end", report_rows=4, report_sha256=hashlib.sha256(data).hexdigest())))
                        p = folder / "results/G-1.json"
                        d = S.read(p); d["свёрнуто"]["a"] = deps; p.write_text(json.dumps(d))
                    elif mode == "bad_limits":
                        p = folder / "measurement.json"
                        d = S.read(p); d["limits"] = dict(seconds=9999, rss_gib=100); p.write_text(json.dumps(d))
                    elif mode == "bad_terms":
                        p = folder / "results/G-1.json"
                        d = S.read(p); d["термы"] = ["different"]; p.write_text(json.dumps(d))
                    else:
                        p = folder / "measurement.json"
                        d = S.read(p); d["returncode"] = -15; p.write_text(json.dumps(d))
                    result = S.collect(self.plan("G-1"), root)
                    self.assertEqual(result["outcomes"], {"invalid": 1})
                    self.assertFalse(result["all_complete"])
                    if mode == "bad_limits":
                        self.assertEqual(result["measurements_all_observed"]["wall_seconds"]["observed"], 0)
                    if mode == "bad_deflate":
                        self.assertEqual(S.collect(self.plan("G-1", "G-2"), root)["outcomes"], {"invalid": 1, "missing": 1})
            with self.assertRaises(ValueError):
                S.collect(self.plan("G-1", "G-1"), root)


if __name__ == "__main__":
    unittest.main()
