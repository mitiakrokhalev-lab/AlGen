import json
from pathlib import Path
import tempfile
import unittest

from algen.metrics import collect


class MetricsTest(unittest.TestCase):
    def test_failed_missing_and_unmeasured_are_not_zero_or_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def put(name, d):
                (root / name).write_text(json.dumps(d))
            put('_план-1-1.json', {"схемы": ["a", "b", "c", "d", "e"]})
            put('a.json', {"id": "a", "статус": "ok", "секунд": 2, "память ГБ": [1, 2],
                           "вердикты": {"неизвестно": 9}, "оставленные вопросы": [{"№": "k1"}, {"№": "k2"}],
                           "свёрнуто": {str(i): ["k1"] for i in range(8)}})
            put('b.json', {"id": "b", "статус": "ошибка", "секунд": 90})
            (root / 'b.txt').write_text('Traceback\nMemoryError\n')
            put('c.json', {"id": "c", "статус": "ошибка: память"})
            put('d.json', {"id": "d", "статус": "таймаут 30 с", "секунд": 30})
            r = collect(root)
            self.assertEqual((r['planned'], r['reported'], r['missing'], r['oom_confirmed']), (5, 4, ['e'], 2))
            self.assertEqual(r['time_seconds_all_observed']['sum'], 122)
            self.assertEqual(r['time_seconds_all_observed']['n'], 3)
            self.assertEqual(r['time_unreported'], ['c'])
            self.assertEqual(r['time_seconds_ok_only']['sum'], 2)
            self.assertEqual(r['within_scheme_ratio'], 5)
            self.assertEqual(r['unknown_ids_before_compression'], 10)
            self.assertEqual(r['summary_counter_ratio'], 4.5)  # первый вердикт класса — другой счётчик
            self.assertIsNone(r['peak_rss_gib'])
            self.assertIsNone(r['cpu_seconds'])
            self.assertIsNone(r['global_verified_basis'])
            put('e.json', {"id": "e", "статус": "ok", "вердикты": {"неизвестно": 5}})
            self.assertIsNone(collect(root)['within_scheme_ratio'])
            put('e.json', {"id": "e", "статус": "ok", "вердикты": {}})
            self.assertEqual(collect(root)['within_scheme_ratio'], 5)
            put('e.json', {"id": "e", "статус": "ok", "секунд": float('nan')})
            r = collect(root)
            self.assertIsNone(r['within_scheme_ratio'])
            self.assertEqual(r['ok_missing_verdicts'], ['e'])
            self.assertEqual(r['time_unreported'], ['c', 'e'])


if __name__ == '__main__':
    unittest.main()
