"""Corrupt or incomplete plan files never keep a complete inventory stamp."""

import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from tools.build_scheme_manifest import validate,validate_completed,arm_parent,recover_attempts,stop_child


class SchemeManifestTest(unittest.TestCase):
    def fixture(self,root,items):
        directory = root/'G'/'attempt'
        directory.mkdir(parents=True)
        raw = b''.join(json.dumps(item,ensure_ascii=False).encode()+b'\n' for item in items)
        path = directory/'schemes.jsonl.gz'
        path.write_bytes(gzip.compress(raw,mtime=0))
        row = dict(base='G',status='complete',complete=True,directory='G/attempt',schemes=len(items),
                   plan_sha256=hashlib.sha256(json.dumps(items,ensure_ascii=False).encode()).hexdigest(),
                   jsonl_sha256=hashlib.sha256(raw).hexdigest())
        return path,row

    def test_canonical_hash_count_crc_and_duplicate_ids(self):
        for items,valid in (([['G',[]],['G-1',['center(G)']]],True),([['G',[]],['G',[]]],False)):
            with tempfile.TemporaryDirectory() as d:
                path,row = self.fixture(Path(d),items)
                if valid:
                    self.assertEqual(validate(path,row),2)
                    bad = dict(row,schemes=3)
                    with self.assertRaises(ValueError):
                        validate(path,bad)
                else:
                    with self.assertRaises(ValueError):
                        validate(path,row)

    def test_resume_invalidates_corruption_without_deleting_old_results(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            path,row = self.fixture(root,[['G',[]]])
            original = path.read_bytes()
            path.write_bytes(original[:-4])
            result = dict(complete=True,total_schemes=1,bases={'G':row})
            validate_completed(root,result)
            self.assertFalse(result['complete'])
            self.assertIsNone(result['total_schemes'])
            self.assertEqual(result['bases']['G']['status'],'invalid_or_error')
            self.assertIsNone(result['bases']['G']['schemes'])
            self.assertEqual(path.read_bytes(),original[:-4])
            self.assertEqual(len(row['validation_failures']),1)

    def test_interrupted_attempt_preserves_unknown_cost(self):
        attempt = dict(status='starting',pid=None,birth=None,parent_wall_seconds=None,child_cpu_seconds=None)
        row = dict(status='running',schemes=None,attempts=[attempt])
        recover_attempts(dict(bases={'G':row}))
        self.assertEqual(row['status'],'interrupted')
        self.assertIsNone(attempt['parent_wall_seconds'])
        self.assertIsNone(attempt['child_cpu_seconds'])
        self.assertEqual(attempt['status'],'interrupted')

    def test_dead_parent_fails_before_any_heavy_work(self):
        with self.assertRaises(RuntimeError):
            arm_parent(os.getppid()+1)

    def test_cleanup_terminates_its_own_child(self):
        proc = subprocess.Popen([sys.executable,'-B','-c','import signal; signal.pause()'])
        try:
            stop_child(proc)
            self.assertIsNotNone(proc.returncode)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()


if __name__=='__main__':
    unittest.main()
