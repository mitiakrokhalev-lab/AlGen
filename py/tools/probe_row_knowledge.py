"""Complete saved-domain control of one registered row's proof/source cycle.

The source is a frozen existing projection assumption bundle, not an audited
primitive mathematical provenance DAG. Withholding/recovering a known value
tests mechanics and does not add mathematical Library data. No raw DB export.
"""
import hashlib
import json
import math
from pathlib import Path
import re
from types import SimpleNamespace

import numpy as np

from algen.row_knowledge import FrozenRowTheory, RowKnowledge
from algen.value_classify import PreparedValues
from algen.value_ledger import ValueLedger, canonical, structure, _unstructure
from tools.probe_value_ledger import _digest, _elapsed, _fresh, _matrix_hash, _stamp

SCOPE = 'registered proof/source cycle of one row; all saved codes, NOT full frontier/report'


def _complete_pairs(form, row):
    result = row.copy()
    for i, parts in getattr(form, 'pair_atoms', {}).items():
        cols = [2*c+(not form.atoms[i][4]) for c in sorted(parts)]
        result[2*i] = all(result[c] for c in cols)
        result[2*i+1] = any(result[c^1] for c in cols)
    return result


def _select(form, conditions, session, trials=32):
    """Bound only diagnostic target search, never the saved condition domain."""
    prepared, seen, attempted = PreparedValues(form), set(), 0
    counts = {n: session.literals.count(n) for n in set(session.literals) if n}
    with session._stable():
        for prem, goal in conditions:
            forbidden = sorted({c for j in (*prem, *form.fixed, goal^1) for c in prepared.expansions[int(j)]})
            for column in forbidden:
                atom = column//2
                literal = session.literals[atom]
                if not literal or counts[literal] != 1:
                    continue  # this finite control uses a unique-view-variable target
                possible = form.m[:, column^1].copy()
                for other in forbidden:
                    if other != column:
                        possible &= form.m[:, other]
                for row in np.flatnonzero(possible)[:trials]:
                    row = int(row)
                    if (row,atom) in seen:
                        continue
                    seen.add((row,atom))
                    original = form.m[row]
                    if not np.array_equal(_complete_pairs(form,original),original):
                        raise ValueError('stored pair columns disagree with their known components')
                    # Never assume form.fixed as concrete row facts. Exclude the
                    # complete target SAT variable (including every alias).
                    claims = [[i,bool(original[2*i])] for i,n in enumerate(session.literals)
                              if n is not None and n != literal and (original[2*i] or original[2*i+1])]
                    facts = {session.literal(i,v) for i,v in claims} - {0}
                    cert = session.derive(atom,facts)
                    attempted += 1
                    if cert is not None:
                        if cert['value'] != bool(original[2*atom]):
                            raise ValueError('Theory entailment contradicts the existing checked projection')
                        if cert['core']:
                            masked = original.copy()
                            masked[2*atom:2*atom+2] = False
                            return row, atom, _complete_pairs(form,masked), claims, cert, attempted
                    if attempted >= trials:
                        raise ValueError('no nonempty-core target in bounded diagnostic search; no receipt')
    raise ValueError('no suitable target in this domain; no receipt')


def _oracle(db, form, conditions, identities, manifest):
    with db.read():
        projection = db.projection()
        np.testing.assert_array_equal(projection.m,form.m)
        assert projection.atoms == list(form.atoms)
        assert tuple(projection.fixed) == tuple(form.fixed)
        assert projection.pair_atoms == getattr(form,'pair_atoms',{})
        assert list(db.conditions().items()) == list(conditions.items())
        assert [r[0] for r in db.db.execute('SELECT identity FROM rows ORDER BY id')] == [canonical(structure(x)) for x in identities]
        assert db._meta('manifest') == manifest
        fresh = _fresh(form,conditions)
        assert list(db.state_rows()) == fresh
        assert db.summary()['proof_pending'] == len(conditions)
        return _digest(fresh)


def probe(form, conditions, identities, manifest, source, directory):
    if not 0 < len(conditions) <= 10000 or not 1 < len(form.m) <= 50000 or len(identities) != len(form.m):
        raise ValueError('full small-domain control dimensions required')
    directory = Path(directory)
    directory.mkdir(parents=True,exist_ok=False)
    input_matrix = _matrix_hash(form.m)
    input_conditions = _digest((list(p),g,s) for (p,g),s in conditions.items())
    initial = _fresh(form,conditions)
    if any(r[2] == 3 for r in initial):
        raise ValueError('initially unrefuted saved domain required')
    expected = _digest(initial)
    stages, hashes, receipts = {}, {}, {}
    t = _stamp()
    reference = dict(source_table_run=manifest.get('source_table_run'),library=manifest['library'],
                     language=manifest['language'],sources=manifest.get('sources',{}))
    theory = form.sc.T
    session = FrozenRowTheory(theory,form.atoms,reference)
    try:
        row,atom,masked,claims,certificate,trials = _select(form,conditions,session)
        stages['freeze_select_target'] = _elapsed(t)
        manifest = dict(manifest,theory=session.identity)
        context = dict(identity=session.identity,clauses_sha256=session.header['clauses_sha256'],
                       schema_sha256=session.header['schema_sha256'],clauses=len(theory.clauses),atoms=len(session.schema))
        bundle = dict(name='frozen-existing-row-assumptions',version=input_matrix,
            source=dict(source,reference=source['reference']+'; frozen projection assumptions, not primitive provenance'),claims=claims)
        altered = form.m.copy()
        altered[row] = masked
        view = SimpleNamespace(m=altered,atoms=form.atoms,fixed=form.fixed,pair_atoms=getattr(form,'pair_atoms',{}))
        path = directory/'knowledge.sqlite'
        t = _stamp()
        with ValueLedger.create(path,view,conditions,identities,manifest,source,batch_size=128) as db:
            hashes['masked'] = _oracle(db,view,conditions,identities,manifest)
            seed = db.summary()
            observation = canonical(db.observation(row,atom))
            hot = db.db.execute('SELECT count(*) FROM events e JOIN conditions c ON c.id=e.condition_id '
                'WHERE c.kind=1 AND e.row_id=? AND e.wanted/2=?',(row,atom)).fetchone()[0]
            if not hot:
                raise ValueError('selected masked target has no A dependency')
            stages['seed_and_full_oracle'] = _elapsed(t)
            k = RowKnowledge(db,session,row)
            t = _stamp()
            receipts['enroll'] = k.enroll('enroll',[bundle],0)
            stages['enroll'] = _elapsed(t)
            t = _stamp()
            receipts['derive'] = k.derive('derive-known-hidden-value',atom,1)
            stages['derive_update'] = _elapsed(t)
            assert receipts['derive']['outcome'] == 'derived'
            assert db.db.execute('SELECT count(*) FROM rk_proofs WHERE active=1').fetchone()[0] == 1
            certificate = json.loads(db.db.execute('SELECT certificate FROM rk_proofs').fetchone()[0])
            assert certificate['core'] and certificate['value'] == bool(form.m[row,2*atom])
            t = _stamp()
            hashes['derived'] = _oracle(db,form,conditions,identities,manifest)
            assert hashes['derived'] == expected
            stages['derived_full_oracle'] = _elapsed(t)
            t = _stamp()
            receipts['withdraw'] = k.withdraw('withdraw-registered-bundle',bundle['name'],bundle['version'],2)
            stages['withdraw_update'] = _elapsed(t)
            altered[row] = False
            hashes['withdrawn'] = _oracle(db,view,conditions,identities,manifest)
            assert db.db.execute('SELECT count(*) FROM rk_sources WHERE active=1').fetchone()[0] == 0
            assert db.db.execute('SELECT count(*) FROM rk_proofs WHERE active=1').fetchone()[0] == 0
    finally:
        session.close()
    # A second fresh solver must verify persisted certificates before reviving
    # conclusions. The first solver and its learned clauses are gone.
    t = _stamp()
    with FrozenRowTheory(theory,form.atoms,reference) as fresh, ValueLedger(path) as db:
        assert fresh.identity == context['identity']
        k = RowKnowledge(db,fresh,row)
        receipts['restore'] = k.put_source('restore-registered-bundle',bundle,3)
        stages['reopen_fresh_context_restore'] = _elapsed(t)
        hashes['restored'] = _oracle(db,form,conditions,identities,manifest)
        assert hashes['restored'] == expected
        assert canonical(db.observation(row,atom)) == observation
        replay = k.put_source('restore-registered-bundle',bundle,3)
        assert replay == dict(receipts['restore'],replayed=True)
        assert db.summary()['revision'] == 4
        with db.read():
            assert db.db.execute('SELECT count(*) FROM rk_events').fetchone()[0] == 4
            assert db.db.execute('SELECT count(*) FROM rk_proofs WHERE active=1').fetchone()[0] == 1
            assert json.loads(db.db.execute('SELECT bundle FROM rk_sources').fetchone()[0]) == bundle
        restored = db.summary()
    assert _matrix_hash(form.m) == input_matrix
    assert _digest((list(p),g,s) for (p,g),s in conditions.items()) == input_conditions
    return dict(version=1,scope=SCOPE,sampled=False,classified=len(conditions),rows=len(form.m),literal_columns=form.m.shape[1],
        input_projection_sha256=input_matrix,input_conditions_sha256=input_conditions,initial_state_sha256=expected,
        state_hashes=hashes,context=context,target_row=row,target_atom=atom,selection_trials=trials,
        target_observation_sha256=hashlib.sha256(observation.encode()).hexdigest(),hot_conditions_after_mask=int(hot),
        proof_certificate=certificate,source_bundle_sha256=hashlib.sha256(canonical(bundle).encode()).hexdigest(),
        source_claims=len(claims),source_bundle_is_frozen_projection=True,mathematical_provenance_audited=False,
        full_saved_domain_oracles_equal=True,original_inputs_unchanged=True,registered_source_withdrawal_verified=True,
        fresh_solver_reopen_verified=True,idempotent_replay_verified=True,identity_stable=True,
        initial=seed,restored=restored,updates=receipts,stages=stages,
        database_file=dict(bytes=path.stat().st_size,sha256=hashlib.sha256(path.read_bytes()).hexdigest()),database_files_uploaded=False,
        registered_proof_closure_verified=True,row_entailment_complete=False,condition_sat_verdicts_generated=False,
        proof_pending=len(conditions),source_propagation_complete=False,current_support_computed=False,
        candidate_frontier_complete=False,production_speedup_claimed=False)


def valid_receipt(r):
    if not isinstance(r,dict) or type(r.get('version')) is not int or r['version'] != 1 or r.get('scope') != SCOPE:
        return False
    digest = lambda x: isinstance(x,str) and re.fullmatch('[0-9a-f]{64}',x) is not None
    n,rows,cols = r.get('classified'),r.get('rows'),r.get('literal_columns')
    if (type(n) is not int or not 0 < n <= 10000 or type(rows) is not int or not 1 < rows <= 50000
            or type(cols) is not int or cols <= 0 or cols%2):
        return False
    for key in ('full_saved_domain_oracles_equal','original_inputs_unchanged','registered_source_withdrawal_verified',
                'fresh_solver_reopen_verified','idempotent_replay_verified','identity_stable','registered_proof_closure_verified',
                'source_bundle_is_frozen_projection'):
        if r.get(key) is not True:return False
    for key in ('sampled','mathematical_provenance_audited','row_entailment_complete','condition_sat_verdicts_generated',
                'source_propagation_complete','current_support_computed','candidate_frontier_complete',
                'production_speedup_claimed','database_files_uploaded'):
        if r.get(key) is not False:return False
    if type(r.get('proof_pending')) is not int or r['proof_pending'] != n:return False
    for key in ('input_projection_sha256','input_conditions_sha256','initial_state_sha256',
                'target_observation_sha256','source_bundle_sha256'):
        if not digest(r.get(key)):return False
    for key,bound in (('target_row',rows),('target_atom',cols//2),('selection_trials',33),
                      ('hot_conditions_after_mask',n+1),('source_claims',cols//2+1)):
        if type(r.get(key)) is not int or not (0 if key in ('target_row','target_atom') else 1) <= r[key] < bound:return False
    context,cert,hashes = r.get('context'),r.get('proof_certificate'),r.get('state_hashes')
    if (not isinstance(context,dict) or any(not digest(context.get(k)) for k in ('identity','clauses_sha256','schema_sha256'))
            or any(type(context.get(k)) is not int or context[k] < 0 for k in ('clauses','atoms'))
            or not isinstance(cert,dict) or cert.get('context') != context['identity']
            or type(cert.get('atom')) is not int or cert['atom'] != r['target_atom']
            or type(cert.get('value')) is not bool or type(cert.get('version')) is not int or cert['version'] != 1
            or not isinstance(cert.get('core'),list) or not cert['core']
            or not isinstance(hashes,dict) or set(hashes) != {'masked','derived','withdrawn','restored'}
            or any(not digest(v) for v in hashes.values())
            or hashes['derived'] != hashes['restored'] or hashes['restored'] != r['initial_state_sha256']
            or hashes['masked'] == hashes['derived'] or hashes['withdrawn'] == hashes['derived']):return False
    def atom_schema(value):
        try:
            atom = _unstructure(value)
            return (structure(atom) == value and type(atom) is tuple
                and ((len(atom) == 3 and atom[0] == 'p') or (len(atom) == 4 and atom[0] == 'r'))
                and type(atom[1]) is str and bool(atom[1]))
        except (ValueError,TypeError,IndexError,KeyError,RecursionError):
            return False
    if not atom_schema(cert.get('target')):return False
    core = []
    for p in cert['core']:
        if not isinstance(p,dict):return False
        lit = p.get('literal')
        if (type(lit) is not int or not 0 < abs(lit) <= context['atoms'] or not atom_schema(p.get('atom'))
                or type(p.get('value')) is not bool or p['value'] != (lit > 0)):return False
        core.append(lit)
    if core != sorted(set(core)) or any(-x in core for x in core) or len(core) > r['source_claims']:return False
    updates = r.get('updates')
    if not isinstance(updates,dict) or set(updates) != {'enroll','derive','withdraw','restore'}:return False
    for rev,key in enumerate(('enroll','derive','withdraw','restore'),1):
        u = updates[key]
        if not isinstance(u,dict) or u.get('registered_proof_closure_verified') is not True:return False
        l = u.get('ledger')
        if (not isinstance(l,dict) or type(l.get('revision')) is not int or l['revision'] != rev
                or type(l.get('all_conditions')) is not int or l['all_conditions'] != n
                or type(l.get('affected_conditions')) is not int or not 0 <= l['affected_conditions'] <= n
                or type(l.get('row')) is not int or l['row'] != r['target_row']
                or type(l.get('proof_pending')) is not int or l['proof_pending'] != n
                or l.get('add') is not False or l.get('replayed',False) is not False
                or not digest(l.get('projection_sha256'))):return False
        if any(u.get(k) is not False or l.get(k) is not False for k in
               ('source_propagation_complete','current_support_computed','candidate_frontier_complete')):return False
        if u.get('row_entailment_complete') is not False:return False
        event = dict(enroll='enroll',derive='derive-known-hidden-value',withdraw='withdraw-registered-bundle',restore='restore-registered-bundle')[key]
        if (l.get('event') != f'rk:{r["target_row"]}:{event}'
                or u.get('operation') != ('put_source' if key == 'restore' else key)
                or u.get('outcome') != ('derived' if key == 'derive' else None)
                or u.get('replayed',False) is not False):return False
        active = key != 'withdraw'
        expected_sources = [dict(name='frozen-existing-row-assumptions',version=r['input_projection_sha256'],
                                 bundle_sha256=r['source_bundle_sha256'])] if active else []
        if u.get('source_versions') != expected_sources:return False
        proofs = u.get('proofs')
        if not isinstance(proofs,list) or len(proofs) != (0 if key == 'enroll' else 1):return False
        if proofs:
            p = proofs[0]
            bindings = [dict(literal=x,providers=[['frozen-existing-row-assumptions',r['input_projection_sha256']]] if active else []) for x in core]
            if (not isinstance(p,dict) or type(p.get('proof')) is not int or p['proof'] != 1
                    or p.get('active') is not active or p.get('bindings') != bindings):return False
            if any(not isinstance(b,dict) or type(b.get('literal')) is not int for b in p['bindings']):return False
    for key,revision in (('initial',0),('restored',4)):
        s = r.get(key)
        if (not isinstance(s,dict) or any(type(s.get(k)) is not int or s[k] != v
                for k,v in (('conditions',n),('rows',rows),('proof_pending',n),('revision',revision)))
                or s.get('domain_import_complete') is not True or s.get('original_support_preserved') is not True
                or type(s.get('database_bytes')) is not int or not 0 < s['database_bytes'] <= 64*1024**2
                or any(s.get(k) is not False for k in ('source_propagation_complete','current_support_computed','candidate_frontier_complete'))):return False
        kinds = s.get('kinds')
        if not isinstance(kinds,dict) or any(k not in ('A','B','C','R') or type(v) is not int or v < 0 for k,v in kinds.items()) or sum(kinds.values()) != n:return False
    if r['initial']['kinds'].get('R',0) or r['restored']['kinds'].get('R',0):return False
    f,stages = r.get('database_file'),r.get('stages')
    if not isinstance(f,dict) or type(f.get('bytes')) is not int or not 0 < f['bytes'] <= 64*1024**2 or not digest(f.get('sha256')):return False
    expected = {'freeze_select_target','seed_and_full_oracle','enroll','derive_update','derived_full_oracle','withdraw_update','reopen_fresh_context_restore'}
    return (isinstance(stages,dict) and set(stages) == expected and all(isinstance(s,dict)
        and set(s) == {'wall_seconds','cpu_seconds'} and all(type(v) in (int,float) and math.isfinite(v) and v >= 0 for v in s.values()) for s in stages.values()))
