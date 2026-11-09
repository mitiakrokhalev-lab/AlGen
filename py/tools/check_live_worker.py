"""Bounded integration: real E.run, table CLI, SQLite, global SAT compression.
Uses a bounded Library/table fixture and CLI main() in process. Verdict cache
is disabled. This does not test native storage, subprocess or the cache wrapper.
"""
import contextlib
import json
import os
import argparse
from pathlib import Path
import sys
import time
from unittest.mock import patch

for name in list(os.environ):
    if name.startswith("ALGEN_"):
        del os.environ[name]
os.environ.update(ALGEN_SIZE="2", ALGEN_FAST="1", ALGEN_COMPRESS="1", ALGEN_DYNAMIC_EXPORT="1")
from algen import table, enumerate as E, library, compress_base
from algen.logic import Vocab
from algen.live import LiveArchive, library_row
from algen.live_worker import create_plan, execute

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', required=True, help='новый каталог контрольного прогона')
args = parser.parse_args()
root = Path(args.out).resolve()
root.mkdir(parents=True, exist_ok=False)
tables = root / 'tables'
tables.mkdir()
(tables / 'G.1-1.pickle').write_bytes(b'controlled native fixture, see worker-control.py')
v, lib = Vocab.section('grp'), library.Library()

def form(objects=('1:1',)):
    f = E.SchemeForm(lib, v, '∀ G : Grp', ['center(G)'], with_rows=False)
    f.search.objects = list(objects)
    f.fill_rows()
    return f

def cli(main, argv, env=None):
    with contextlib.ExitStack() as stack:
        if env is not None:
            stack.enter_context(patch.dict(os.environ, env, clear=True))
        stack.enter_context(patch.object(sys, 'argv', argv))
        stack.enter_context(patch.object(library, 'built_library', return_value=lib))
        stack.enter_context(patch.object(table, 'built_library', return_value=lib))
        stack.enter_context(patch.object(table, 'load', side_effect=lambda *args: form()))
        stack.enter_context(patch.object(table, 'skeleton', side_effect=lambda *args: form()))
        stack.enter_context(patch.object(table, 'schemes', return_value=[('S', ['center(G)'])]))
        stack.enter_context(patch.object(table, 'STATE_SAVE', False))
        stack.enter_context(patch.object(table, 'STATE_IN', ''))
        try:
            main()
        except SystemExit as e:
            if e.code not in (None, 0):
                raise

start = time.monotonic()
with open(root / 'control.log', 'w') as log, contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
    cli(table.main, ['table', 'перебор', 'G', '--каталог', str(tables), '--выход', str(root / 'initial'),
                     '--посылок', '1', '--нитей', '1', '--схемы', 'S'])
    with LiveArchive(root / 'archive.sqlite') as a:
        ctx = a.import_file(root / 'initial/S.archive.jsonl.gz')
        fresh = form(('2:1',))
        before = a.stats(ctx)
        after = a.apply_example(ctx, library_row(fresh, 0, 'Library actual C2'))
    m = create_plan(root / 'archive.sqlite', ctx, tables, root / 'run')
    def runner(argv, env, logpath):
        mod = 'algen.table' if 'algen.table' in argv else 'algen.compress_base'
        tail = argv[argv.index(mod)+1:]
        cli(table.main if mod == 'algen.table' else compress_base.main, [mod] + tail, env)
    receipt = execute(root / 'archive.sqlite', m['id'], memory=0, limit=60, runner=runner)
    with LiveArchive(root / 'archive.sqlite') as a:
        final = a.stats(receipt['target'])
        assert not final['pending'] and final['unresolved'] == final['invalidated'] == 0
        assert after['states'].get('refuted', 0) > 0
        assert receipt['basis_folded'] > 1000 and receipt['basis_kept'] > 0
result = dict(root=str(root), seconds=round(time.monotonic()-start, 3),
              before=before, after=after, receipt=receipt, final=final)
(root / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2))
print(json.dumps(result, ensure_ascii=False), flush=True)

