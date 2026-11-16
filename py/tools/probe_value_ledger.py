"""Finite persistence experiment on all conditions of one small frozen domain.

No candidate sampling, no SAT/report replacement, no new mathematical data.
SQLite files must be kept outside uploaded artifacts; receipts contain hashes
and aggregates only. The experiment masks/restores a known projection cell,
tests rollback, and appends one originally withheld genuine Library row.
"""
import hashlib
import json
from pathlib import Path
import re
import time
import math
from types import SimpleNamespace
from unittest.mock import patch

import numpy as np

from algen.value_classify import PreparedValues
from algen.value_ledger import ValueLedger, canonical, structure

SCOPE = 'one complete stored minimal domain; NOT a complete future frontier or report'


def _stamp():
    return time.perf_counter(), time.process_time()


def _elapsed(start):
    return dict(wall_seconds=time.perf_counter() - start[0], cpu_seconds=time.process_time() - start[1])


def _digest(rows):
    h = hashlib.sha256()
    for row in rows:
        h.update((canonical(row) + '\n').encode())
    return h.hexdigest()


def _matrix_hash(matrix):
    """Hash logical row order with bounded copies, including native F/strided views."""
    h = hashlib.sha256()
    for start in range(0, len(matrix), 256):
        h.update(memoryview(np.ascontiguousarray(matrix[start:start+256])))
    return h.hexdigest()


def _fresh(form, conditions, max_total_events=1_000_000):
    """Full classification without consulting stored kinds, dependencies or events."""
    result, events = [], 0
    for b in PreparedValues(form).iter_batches(conditions, batch_size=128):
        events += len(b.rows)
        if events > max_total_events:
            raise ValueError('small probe event budget exceeded; no full-control receipt')
        for i, key in enumerate(b.keys):
            a, z = map(int, b.offsets[i:i+2])
            result.append((b.depth, int(key), int(b.kinds[i]), int(b.single[i]), int(b.multi[i]),
                int(b.refuting[i]), tuple((int(r), int(c)) for r, c in zip(b.rows[a:z], b.columns[a:z]))))
    return result


def _blocker(form, conditions):
    prepared = PreparedValues(form)
    for prem, goal in conditions:
        forbidden = sorted({c for j in (*prem, *form.fixed, goal ^ 1) for c in prepared.expansions[int(j)]})
        for c in forbidden:
            possible = form.m[:, c ^ 1].copy()
            for other in forbidden:
                if other != c:
                    possible &= form.m[:, other]
            found = np.flatnonzero(possible)
            if len(found):
                return int(found[0]), c // 2
    raise ValueError('no known single blocker in this small domain; choose a different control')


def _verify(db, form, conditions, identities, sources, manifest):
    """Compare the DB with EXTERNAL requested inputs, not DB-derived expectations."""
    with db.read():
        projection = db.projection()
        np.testing.assert_array_equal(projection.m, form.m)
        assert projection.atoms == list(form.atoms)
        assert tuple(projection.fixed) == tuple(form.fixed)
        assert projection.pair_atoms == getattr(form, 'pair_atoms', {})
        assert list(db.conditions().items()) == list(conditions.items())
        actual_rows = [tuple(r) for r in db.db.execute('SELECT r.identity,v.source FROM rows r JOIN row_versions v '
            'ON v.row_id=r.id AND v.revision=r.revision ORDER BY r.id')]
        assert actual_rows == [(canonical(structure(identity)), canonical(source))
                               for identity, source in zip(identities, sources)]
        assert db._meta('manifest') == manifest
        direct = _fresh(form, conditions)
        assert list(db.state_rows()) == direct
        return direct


def probe(form, conditions, identities, manifest, source, directory):
    """Caller provides a frozen complete small domain and exact concrete IDs."""
    if not 0 < len(conditions) <= 10000 or not 1 < len(form.m) <= 50000:
        raise ValueError('probe is restricted to a small nonempty control, not the candidate class')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    if len(identities) != len(form.m):
        raise ValueError('all concrete row identities are required')
    input_matrix = _matrix_hash(form.m)
    input_conditions = _digest((list(p), g, support) for (p, g), support in conditions.items())
    initial = _fresh(form, conditions)
    if any(row[2] == 3 for row in initial):
        raise ValueError('this control requires the initially unrefuted minimal domain')
    initial_hash = _digest(initial)
    expected_domain = _digest((len(p), conditions._encode(p, g), support)
                             for (p, g), support in conditions.items())
    row, atom = _blocker(form, conditions)
    original = form.m[row].copy()
    masked = original.copy()
    masked[2*atom:2*atom+2] = False
    masking_source = dict(kind='user', reference='diagnostic withholding of an existing checked cell; '
                          'underlying mathematical source is not retracted')
    stages, updates, hashes = {}, [], {}
    db_path = directory / 'values.sqlite'
    t = _stamp()
    with ValueLedger.create(db_path, form, conditions, identities, manifest, source, batch_size=128) as db:
        assert db._meta('domain_sha256') == expected_domain
        assert _verify(db, form, conditions, identities, [source]*len(identities), manifest) == initial
        before_identity = canonical(db.observation(row, atom))
        seed = db.summary()
        stages['seed'] = _elapsed(t)
        t = _stamp()
        hide = db.apply_row('hide-checked-cell', identities[row], masked, masking_source, 0)
        stages['hide_update'] = _elapsed(t)
        updates.append(hide)
        t = _stamp()
        masked_matrix = form.m.copy()
        masked_matrix[row] = masked
        expected_masked = SimpleNamespace(m=masked_matrix, atoms=form.atoms, fixed=form.fixed,
                                         pair_atoms=getattr(form, 'pair_atoms', {}))
        expected_sources = [source]*len(identities)
        expected_sources[row] = masking_source
        masked_fresh = _verify(db, expected_masked, conditions, identities, expected_sources, manifest)
        stages['hide_full_oracle'] = _elapsed(t)
        # Exact target count, not a top-K assertion that could silently miss it.
        hot_count = sum(1 for state in masked_fresh if state[2] == 1
                        for r, c in state[6] if r == row and c//2 == atom)
        stored_count = db.db.execute('SELECT count(*) FROM events e JOIN conditions c ON c.id=e.condition_id '
            'WHERE c.kind=1 AND e.row_id=? AND e.wanted/2=?', (row, atom)).fetchone()[0]
        assert stored_count == hot_count
        assert hot_count > 0
        hashes['masked'] = _digest(masked_fresh)
    # Reopen, restore and replay the same event: no process-local ledger cache.
    with ValueLedger(db_path) as db:
        t = _stamp()
        restored = db.apply_row('restore-checked-cell', identities[row], original, source, 1)
        stages['restore_after_reopen'] = _elapsed(t)
        updates.append(restored)
        assert canonical(db.observation(row, atom)) == before_identity
        assert _verify(db, form, conditions, identities, [source]*len(identities), manifest) == initial
        replay = db.apply_row('restore-checked-cell', identities[row], original, source, 1)
        assert replay == dict(restored, replayed=True)
        previous = list(db.state_rows())
        previous_versions = db.db.execute('SELECT count(*) FROM row_versions').fetchone()[0]
        reclassify = db._reclassify
        class ExpectedRollback(BaseException):
            pass
        def interrupted(*args):
            reclassify(*args)
            raise ExpectedRollback()
        with patch.object(db, '_reclassify', interrupted):
            try:
                db.apply_row('rolled-back', identities[row], masked, masking_source, 2)
            except ExpectedRollback:
                pass
            else:
                raise AssertionError('injected interruption was not delivered')
        assert _verify(db, form, conditions, identities, [source]*len(identities), manifest) == previous
        assert db.summary()['revision'] == 2
        assert db.db.execute('SELECT count(*) FROM row_versions').fetchone()[0] == previous_versions
        assert db.db.execute("SELECT count(*) FROM changes WHERE event='rolled-back'").fetchone()[0] == 0
        restored_summary = db.summary()
        hashes['restored'] = _digest(db.state_rows())
    # Deliberately omit the final existing Library row, then append it exactly.
    smaller = SimpleNamespace(m=form.m[:-1], atoms=form.atoms, fixed=form.fixed,
                              pair_atoms=getattr(form, 'pair_atoms', {}))
    second_path = directory / 'append.sqlite'
    t = _stamp()
    with ValueLedger.create(second_path, smaller, conditions, identities[:-1], manifest, source, batch_size=128) as db:
        _verify(db, smaller, conditions, identities[:-1], [source]*(len(identities)-1), manifest)
        add = db.apply_row('return-withheld-row', identities[-1], form.m[-1], source, 0, add=True)
        assert add['affected_conditions'] == len(conditions)
        assert _verify(db, form, conditions, identities, [source]*len(identities), manifest) == initial
        updates.append(add)
        hashes['new_row_restored'] = _digest(db.state_rows())
        stages['separate_withheld_row_control'] = _elapsed(t)
    assert _matrix_hash(form.m) == input_matrix
    assert _digest((list(p), g, support) for (p, g), support in conditions.items()) == input_conditions
    files = {p.name: dict(bytes=p.stat().st_size, sha256=hashlib.sha256(p.read_bytes()).hexdigest())
             for p in (db_path, second_path)}
    return dict(version=1, scope=SCOPE,
        sampled=False, classified=len(conditions), rows=len(form.m), literal_columns=form.m.shape[1],
        input_projection_sha256=input_matrix, input_conditions_sha256=input_conditions,
        domain_sha256=expected_domain, initial_state_sha256=initial_hash, state_hashes=hashes,
        full_domain_oracles_equal=True, external_projection_readback_verified=True,
        identities_sources_supports_readback_verified=True, original_inputs_unchanged=True, identity_stable=True,
        rollback_verified=True, reopen_verified=True, idempotent_replay_verified=True,
        hidden_observation_sha256=hashlib.sha256(before_identity.encode()).hexdigest(),
        hidden_row=row, hidden_atom=atom, hot_conditions_after_hide=hot_count,
        initial=seed, restored=restored_summary, updates=updates, stages=stages, database_files=files,
        database_files_uploaded=False, masking_is_not_source_retraction=True,
        proof_pending=len(conditions), current_support_computed=False, source_propagation_complete=False,
        candidate_frontier_complete=False, sat_verdicts_generated=False, production_speedup_claimed=False)


def valid_receipt(value):
    if not isinstance(value, dict):
        return False
    n, rows, cols = value.get('classified'), value.get('rows'), value.get('literal_columns')
    digest_ok = lambda x: isinstance(x, str) and re.fullmatch('[0-9a-f]{64}', x) is not None
    checks = ('full_domain_oracles_equal', 'original_inputs_unchanged', 'identity_stable',
              'rollback_verified', 'reopen_verified', 'idempotent_replay_verified', 'masking_is_not_source_retraction',
              'external_projection_readback_verified', 'identities_sources_supports_readback_verified')
    if (type(value.get('version')) is not int or value['version'] != 1 or value.get('scope') != SCOPE
            or type(n) is not int or not 0 < n <= 10000 or type(rows) is not int or not 1 < rows <= 50000
            or type(cols) is not int or cols <= 0 or cols%2 or value.get('sampled') is not False
            or any(value.get(k) is not True for k in checks)
            or value.get('candidate_frontier_complete') is not False
            or value.get('source_propagation_complete') is not False
            or value.get('current_support_computed') is not False
            or value.get('sat_verdicts_generated') is not False
            or value.get('production_speedup_claimed') is not False
            or value.get('database_files_uploaded') is not False
            or type(value.get('proof_pending')) is not int or value['proof_pending'] != n
            or any(not digest_ok(value.get(k)) for k in ('initial_state_sha256', 'domain_sha256',
                'input_projection_sha256', 'input_conditions_sha256', 'hidden_observation_sha256'))
            or type(value.get('hot_conditions_after_hide')) is not int or not 0 < value['hot_conditions_after_hide'] <= n
            or type(value.get('hidden_row')) is not int or not 0 <= value['hidden_row'] < rows
            or type(value.get('hidden_atom')) is not int or not 0 <= value['hidden_atom'] < cols//2):
        return False
    for key, revision in (('initial', 0), ('restored', 2)):
        summary = value.get(key)
        if not isinstance(summary, dict):
            return False
        for field, expected in (('conditions', n), ('rows', rows), ('proof_pending', n), ('revision', revision)):
            if type(summary.get(field)) is not int or summary[field] != expected:
                return False
        if (any(summary.get(k) is not False for k in ('candidate_frontier_complete',
                'source_propagation_complete', 'current_support_computed'))
                or summary.get('domain_import_complete') is not True or summary.get('original_support_preserved') is not True
                or type(summary.get('database_bytes')) is not int or not 0 < summary['database_bytes'] <= 64*1024**2):
            return False
        kinds = summary.get('kinds')
        if (not isinstance(kinds, dict) or any(k not in ('A','B','C','R') or type(v) is not int or v < 0 for k,v in kinds.items())
                or sum(kinds.values()) != n or kinds.get('R', 0) != 0):
            return False
    files = value.get('database_files')
    if not isinstance(files, dict) or set(files) != {'values.sqlite', 'append.sqlite'}:
        return False
    for f in files.values():
        if (not isinstance(f, dict) or type(f.get('bytes')) is not int or not 0 < f['bytes'] <= 64*1024**2
                or not digest_ok(f.get('sha256'))):
            return False
    stages = value.get('stages')
    if not isinstance(stages, dict) or set(stages) != {'seed', 'hide_update', 'hide_full_oracle',
            'restore_after_reopen', 'separate_withheld_row_control'}:
        return False
    if any(not isinstance(s, dict) or set(s) != {'wall_seconds', 'cpu_seconds'}
           or any(type(t) not in (int,float) or not math.isfinite(t) or t < 0 for t in s.values()) for s in stages.values()):
        return False
    hashes, updates = value.get('state_hashes'), value.get('updates')
    return (isinstance(hashes, dict) and digest_ok(hashes.get('masked'))
        and hashes['masked'] != value['initial_state_sha256']
        and hashes.get('restored') == hashes.get('new_row_restored') == value['initial_state_sha256']
        and value['initial']['kinds'] == value['restored']['kinds']
        and isinstance(updates, list) and len(updates) == 3
        and all(isinstance(x, dict) and type(x.get('affected_conditions')) is int
                and 0 < x['affected_conditions'] <= n and type(x.get('all_conditions')) is int
                and x['all_conditions'] == n and type(x.get('proof_pending')) is int and x['proof_pending'] == n
                and type(x.get('revision')) is int and x['revision'] == rev and x.get('add') is add
                and x.get('event') == event and type(x.get('row')) is int and x['row'] == row
                and digest_ok(x.get('projection_sha256'))
                and all(x.get(k) is False for k in ('candidate_frontier_complete',
                    'source_propagation_complete', 'current_support_computed'))
                for x, rev, add, event, row in zip(updates, (1,2,1), (False,False,True),
                    ('hide-checked-cell', 'restore-checked-cell', 'return-withheld-row'),
                    (value['hidden_row'], value['hidden_row'], rows-1)))
        and updates[2]['affected_conditions'] == n)
