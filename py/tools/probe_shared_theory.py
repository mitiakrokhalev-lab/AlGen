"""Paired first-pass control on two distinct complete saved value domains.

No production report, new mathematical data, primitive-provenance audit or
full-frontier claim. Private SQLite files must stay outside public artifacts.
Both modes use a deterministic, intentionally unminimized conditional core;
solver learning must not change the target, source bundle or published state.
"""
import hashlib
import json
import math
from pathlib import Path
import re
from types import SimpleNamespace

import numpy as np

from algen.frozen_theory import FrozenTheoryBasis
from algen.logic import App, Var
from algen.row_knowledge import FrozenRowTheory, RowKnowledge
from algen.value_ledger import ValueLedger, canonical, structure, _unstructure
from tools.probe_row_knowledge import _complete_pairs, _oracle
from tools.probe_value_ledger import _digest, _elapsed, _fresh, _matrix_hash, _stamp

SCOPE = 'two complete saved domains; shared immutable basis; NOT production report/frontier'


class PairControl:
    def __init__(self, directory, mode, expected_cases, *, row=20117, target=None):
        if not __debug__:
            raise RuntimeError('paired external oracles require active assertions')
        if mode not in ('separate','shared') or type(row) is not int or row < 0:
            raise ValueError('explicit basis mode and concrete target row required')
        if (not isinstance(expected_cases,list) or len(expected_cases) != 2
                or any(not isinstance(x,(tuple,list)) or len(x) != 2 or not isinstance(x[0],str) or not x[0]
                       or type(x[1]) is not int or not 0 < x[1] <= 10000 for x in expected_cases)
                or len({x[0] for x in expected_cases}) != 2):
            raise ValueError('two different complete small domain plans required')
        self.directory, self.mode = Path(directory),mode
        self.directory.mkdir(parents=True,exist_ok=False)
        self.expected = list(map(tuple,expected_cases))
        self.row = row
        self.target = target or ('p','abelian',App('sym',(Var('G'),)))
        self._theory, self._reference, self._shared = None,None,None
        self._saved, self._stats = [],[]
        self._finished, self._sealed = False,False

    def abort(self):
        if self._shared is not None:
            self._shared.close()
            self._shared = None

    def consume(self, sid, form, conditions, identities, manifest, source):
        index = len(self._saved)
        if self._finished or self._sealed or index >= 2 or (sid,len(conditions)) != self.expected[index]:
            raise ValueError('saved domain missing, repeated, reordered or incomplete')
        if not 1 < len(form.m) <= 50000 or not self.row < len(form.m) or len(identities) != len(form.m):
            raise ValueError('complete concrete row domain required')
        theory = form.sc.T
        reference = dict(source_table_run=manifest.get('source_table_run'),library=manifest['library'],
                         language=manifest['language'],sources=manifest.get('sources',{}))
        if self._theory is None:
            self._theory,self._reference = theory,reference
        elif theory is not self._theory or canonical(reference) != canonical(self._reference):
            raise ValueError('both different views must share the exact unchanged Theory owner and reference')
        t = _stamp()
        if self.mode == 'shared':
            if self._shared is None:
                self._shared = FrozenTheoryBasis(theory,reference)
            basis = self._shared
        else:
            basis = FrozenTheoryBasis(theory,reference)
        try:
            record,saved = self._case(sid,form,conditions,identities,manifest,source,basis)
            record['first_pass_case'] = _elapsed(t)
            self._saved.append((record,saved))
            return record
        finally:
            if self.mode == 'separate':
                basis.close()
                self._stats.append(basis.stats())

    def _case(self, sid, form, conditions, identities, manifest, source, basis):
        stages,receipts,hashes = {},{},{}
        input_hash = _matrix_hash(form.m)
        condition_hash = _digest((list(p),g,s) for (p,g),s in conditions.items())
        original_state = _fresh(form,conditions)
        if any(r[2] == 3 for r in original_state):
            raise ValueError('control requires an initially unrefuted saved minimal domain')
        original_hash = _digest(original_state)
        atom = list(form.atoms).index(self.target)
        if not form.m[self.row,2*atom+1] or form.m[self.row,2*atom]:
            raise ValueError('predeclared diagnostic target must be an existing known False value')
        with FrozenRowTheory(self._theory,form.atoms,self._reference,basis=basis) as view:
            t = _stamp()
            variable = view.literals[atom]
            if not variable or view.literals.count(variable) != 1:
                raise ValueError('diagnostic target must have one unique primitive SAT variable in the view')
            original = form.m[self.row].copy()
            if not np.array_equal(_complete_pairs(form,original),original):
                raise ValueError('original pair columns do not match known primitive components')
            claims = [[i,bool(original[2*i])] for i,n in enumerate(view.literals)
                      if n is not None and n != variable and (original[2*i] or original[2*i+1])]
            facts = {view.literal(i,v) for i,v in claims} - {0}
            if not facts:
                raise ValueError('nonempty conditional source core required')
            # Fix the entire core independently of mutable SAT learning history.
            # It is intentionally not a minimal core or new mathematical fact.
            certificate = view.certificate(atom,False,sorted(facts))
            with view._stable():
                view.compatible(facts)
                view.verify(certificate)
            stages['prepare_canonical_proof'] = _elapsed(t)
            manifest = dict(manifest,theory=view.identity)
            source_bundle = dict(name='existing-row-assumptions',version=input_hash,
                source=dict(source,reference=source['reference']+'; frozen projection assumptions, no primitive provenance audit'),claims=claims)
            masked = original.copy();masked[2*atom:2*atom+2] = False
            altered = form.m.copy();altered[self.row] = _complete_pairs(form,masked)
            expected = SimpleNamespace(m=altered,atoms=form.atoms,fixed=form.fixed,pair_atoms=getattr(form,'pair_atoms',{}))
            path = self.directory/(sid+'.sqlite')
            t = _stamp()
            with ValueLedger.create(path,expected,conditions,identities,manifest,source,batch_size=128) as db:
                hashes['masked'] = _oracle(db,expected,conditions,identities,manifest)
                initial = db.summary()
                observation = canonical(db.observation(self.row,atom))
                hot = db.db.execute('SELECT count(*) FROM events e JOIN conditions c ON c.id=e.condition_id '
                    'WHERE c.kind=1 AND e.row_id=? AND e.wanted/2=?',(self.row,atom)).fetchone()[0]
                if not hot:raise ValueError('fixed target has no single-missing dependency in the complete domain')
                stages['seed_and_full_oracle'] = _elapsed(t)
                k = RowKnowledge(db,view,self.row)
                t = _stamp();receipts['enroll'] = k.enroll('enroll',[source_bundle],0)
                stages['enroll'] = _elapsed(t)
                t = _stamp();receipts['prove'] = k.register_proof('canonical-proof',certificate,1)
                stages['canonical_proof_update'] = _elapsed(t)
                hashes['proved'] = _oracle(db,form,conditions,identities,manifest)
                if hashes['proved'] != original_hash:raise AssertionError('proved projection does not restore original domain')
                t = _stamp();receipts['withdraw'] = k.withdraw('withdraw',source_bundle['name'],source_bundle['version'],2)
                stages['withdraw_update'] = _elapsed(t)
                altered[self.row] = False
                hashes['withdrawn'] = _oracle(db,expected,conditions,identities,manifest)
                assert db.db.execute('SELECT count(*) FROM rk_proofs WHERE active=1').fetchone()[0] == 0
                t = _stamp();receipts['restore'] = k.put_source('restore',source_bundle,3)
                stages['restore_update'] = _elapsed(t)
                hashes['restored'] = _oracle(db,form,conditions,identities,manifest)
                assert hashes['restored'] == original_hash
                assert db.summary()['revision'] == 4
                assert canonical(db.observation(self.row,atom)) == observation
                assert k.put_source('restore',source_bundle,3) == dict(receipts['restore'],replayed=True)
                assert db.summary()['revision'] == 4
                restored = db.summary()
                domain = db._meta('domain_sha256')
        assert _matrix_hash(form.m) == input_hash
        assert _digest((list(p),g,s) for (p,g),s in conditions.items()) == condition_hash
        record = dict(sid=sid,conditions=len(conditions),rows=len(form.m),literal_columns=form.m.shape[1],
            target_row=self.row,target_atom=atom,target=structure(self.target),hot_conditions=int(hot),
            input_projection_sha256=input_hash,input_conditions_sha256=condition_hash,
            initial_state_sha256=original_hash,domain_sha256=domain,
            observation_sha256=hashlib.sha256(observation.encode()).hexdigest(),view_context=view.identity,
            basis_context=basis.identity,theory_atoms=len(view.schema),theory_clauses=len(self._theory.clauses),
            certificate_sha256=hashlib.sha256(canonical(certificate).encode()).hexdigest(),
            source_bundle_sha256=hashlib.sha256(canonical(source_bundle).encode()).hexdigest(),
            source_claims=len(claims),core_literal_count=len(facts),core_minimization_attempted=False,
            state_hashes=hashes,initial=initial,restored=restored,updates=receipts,stages=stages)
        saved = dict(path=path,form=form,conditions=conditions,identities=identities,manifest=manifest,
                     source=source,source_bundle=source_bundle,certificate=certificate,observation=observation)
        return record,saved

    def seal_first_pass(self):
        if self._finished or [r['sid'] for r,s in self._saved] != [s for s,n in self.expected]:
            raise ValueError('both complete distinct first-pass domains required before validation')
        if self._sealed:
            return
        if self._shared is not None:
            self._shared.close()
            self._stats.append(self._shared.stats())
            self._shared = None
        self._sealed = True

    def finish(self):
        self.seal_first_pass()
        t = _stamp()
        with FrozenTheoryBasis(self._theory,self._reference) as fresh:
            for record,saved in self._saved:
                form,conditions = saved['form'],saved['conditions']
                with FrozenRowTheory(self._theory,form.atoms,self._reference,basis=fresh) as view, ValueLedger(saved['path']) as db:
                    assert view.identity == record['view_context'] and fresh.identity == record['basis_context']
                    k = RowKnowledge(db,view,self.row)
                    receipt = k.register_proof('fresh-replay',saved['certificate'],4)
                    assert receipt['ledger']['revision'] == 5
                    record['fresh_replay'] = receipt
                    record['state_hashes']['fresh_replayed'] = _oracle(db,form,conditions,saved['identities'],saved['manifest'])
                    assert record['state_hashes']['fresh_replayed'] == record['initial_state_sha256']
                    assert canonical(db.observation(self.row,record['target_atom'])) == saved['observation']
                    assert db.db.execute('SELECT count(*) FROM rk_proofs WHERE active=1').fetchone()[0] == 1
                    assert db.db.execute('SELECT count(*) FROM rk_events').fetchone()[0] == 5
                    assert json.loads(db.db.execute('SELECT bundle FROM rk_sources').fetchone()[0]) == saved['source_bundle']
                    record['final'] = db.summary()
                    record['domain_sha256'] = db._meta('domain_sha256')
                    record['logical_history_sha256'] = _digest(tuple(r) for r in db.db.execute('SELECT event,packet,receipt FROM rk_events ORDER BY event'))
                    record['original_inputs_unchanged'] = (_matrix_hash(form.m) == record['input_projection_sha256']
                        and _digest((list(p),g,s) for (p,g),s in conditions.items()) == record['input_conditions_sha256'])
                    assert record['original_inputs_unchanged']
                with saved['path'].open('rb') as stream:
                    database_hash = hashlib.file_digest(stream,'sha256').hexdigest()
                record['database_file'] = dict(bytes=saved['path'].stat().st_size,sha256=database_hash)
                logical = {k:v for k,v in record.items() if k not in ('stages','first_pass_case','database_file')}
                record['canonical_output_sha256'] = hashlib.sha256(canonical(logical).encode()).hexdigest()
            fresh.close()
            validation_stats = fresh.stats()
        self._finished = True
        return dict(version=1,scope=SCOPE,mode=self.mode,sampled=False,
            expected_cases=[list(x) for x in self.expected],cases=[r for r,s in self._saved],
            main_basis_stats=self._stats,fresh_validation_basis_stats=validation_stats,fresh_validation=_elapsed(t),
            all_saved_domain_oracles_equal=True,fresh_solver_proofs_replayed=True,source_withdrawal_verified=True,
            idempotent_replay_verified=True,common_Theory_owner_verified=True,
            database_files_uploaded=False,source_bundle_is_frozen_projection=True,primitive_mathematical_provenance_audited=False,
            production_E_run_knowledge_first=False,condition_sat_verdicts_generated=False,
            proof_pending=sum(n for s,n in self.expected),current_support_computed=False,source_propagation_complete=False,
            candidate_frontier_complete=False,scientific_output_reduction_measured=False,production_speedup_claimed=False)


def _valid_receipt(r):
    """Strict aggregate contract; actual proof replay is performed in finish()."""
    digest = lambda x:isinstance(x,str) and re.fullmatch('[0-9a-f]{64}',x) is not None
    def elapsed(x):
        return (isinstance(x,dict) and set(x)=={'wall_seconds','cpu_seconds'}
            and all(type(v) in (int,float) and math.isfinite(v) and v>=0 for v in x.values()))
    def stats(x,views):
        if not isinstance(x,dict) or x.get('solver_live') is not False:return False
        for k,w in (('snapshot_builds',1),('views_bound',views),('solver_bootstrap_attempts',1),('solver_bootstraps',1),('solver_discards',1)):
            if type(x.get(k)) is not int or x[k]!=w:return False
        if type(x.get('clause_hash_calls')) is not int or x['clause_hash_calls']<1:return False
        timing_keys = [name+'_'+kind+'_seconds' for name in ('literal_map_snapshot','schema_hash','clause_hash',
                       'snapshot','literal_map_validation','solver_bootstrap') for kind in ('wall','cpu')]
        return all(type(x.get(k)) in (int,float) and math.isfinite(x[k]) and x[k]>=0 for k in timing_keys)
    if (not isinstance(r,dict) or type(r.get('version')) is not int or r['version']!=1
            or r.get('scope')!=SCOPE or r.get('mode') not in ('separate','shared')):return False
    for key in ('all_saved_domain_oracles_equal','fresh_solver_proofs_replayed','source_withdrawal_verified',
                'idempotent_replay_verified','common_Theory_owner_verified','source_bundle_is_frozen_projection'):
        if r.get(key) is not True:return False
    for key in ('sampled','database_files_uploaded','primitive_mathematical_provenance_audited','production_E_run_knowledge_first',
                'condition_sat_verdicts_generated','current_support_computed','source_propagation_complete',
                'candidate_frontier_complete','scientific_output_reduction_measured','production_speedup_claimed'):
        if r.get(key) is not False:return False
    plan,cases = r.get('expected_cases'),r.get('cases')
    if (not isinstance(plan,list) or len(plan)!=2 or any(not isinstance(p,list) or len(p)!=2
            or not isinstance(p[0],str) or not p[0] or type(p[1]) is not int or not 0<p[1]<=10000 for p in plan)
            or plan[0][0]==plan[1][0] or not isinstance(cases,list) or len(cases)!=2
            or type(r.get('proof_pending')) is not int or r['proof_pending']!=sum(p[1] for p in plan)):return False
    bases = r.get('main_basis_stats')
    if (not isinstance(bases,list) or len(bases)!=(1 if r['mode']=='shared' else 2)
            or any(not stats(b,2 if r['mode']=='shared' else 1) for b in bases)
            or not stats(r.get('fresh_validation_basis_stats'),2) or not elapsed(r.get('fresh_validation'))):return False
    for (sid,n),c in zip(plan,cases):
        if not isinstance(c,dict) or c.get('sid')!=sid or type(c.get('conditions')) is not int or c['conditions']!=n:return False
        rows,cols,atoms = c.get('rows'),c.get('literal_columns'),c.get('theory_atoms')
        if (type(rows) is not int or not 1<rows<=50000 or type(cols) is not int or cols<=0 or cols%2
                or type(atoms) is not int or atoms<1 or type(c.get('theory_clauses')) is not int or c['theory_clauses']<0):return False
        for key,lo,hi in (('target_row',0,rows),('target_atom',0,cols//2),('hot_conditions',1,n+1),
                          ('source_claims',1,cols//2+1),('core_literal_count',1,cols//2+1)):
            if type(c.get(key)) is not int or not lo<=c[key]<hi:return False
        try:
            target = _unstructure(c.get('target'))
            if (structure(target)!=c['target'] or type(target) is not tuple
                    or not ((len(target)==3 and target[0]=='p') or (len(target)==4 and target[0]=='r'))):return False
        except (ValueError,TypeError,IndexError,KeyError,RecursionError):return False
        if c['core_literal_count']>c['source_claims'] or c.get('core_minimization_attempted') is not False:return False
        for key in ('input_projection_sha256','input_conditions_sha256','initial_state_sha256','domain_sha256','observation_sha256',
                    'view_context','basis_context','certificate_sha256','source_bundle_sha256','logical_history_sha256','canonical_output_sha256'):
            if not digest(c.get(key)):return False
        hs = c.get('state_hashes')
        if (not isinstance(hs,dict) or set(hs)!={'masked','proved','withdrawn','restored','fresh_replayed'}
                or any(not digest(x) for x in hs.values()) or any(hs[k]!=c['initial_state_sha256'] for k in ('proved','restored','fresh_replayed'))
                or any(hs[k]==c['initial_state_sha256'] for k in ('masked','withdrawn'))):return False
        for key,revision in (('initial',0),('restored',4),('final',5)):
            s = c.get(key)
            if not isinstance(s,dict):return False
            for field,w in (('revision',revision),('conditions',n),('rows',rows),('proof_pending',n)):
                if type(s.get(field)) is not int or s[field]!=w:return False
            if (s.get('domain_import_complete') is not True or s.get('original_support_preserved') is not True
                    or any(s.get(k) is not False for k in ('source_propagation_complete','current_support_computed','candidate_frontier_complete'))
                    or type(s.get('database_bytes')) is not int or not 0<s['database_bytes']<=64*1024**2):return False
            kinds = s.get('kinds')
            if (not isinstance(kinds,dict) or any(k not in ('A','B','C','R') or type(v) is not int or v<0 for k,v in kinds.items())
                    or sum(kinds.values())!=n or kinds.get('R',0)):return False
        updates = c.get('updates')
        if not isinstance(updates,dict) or set(updates)!={'enroll','prove','withdraw','restore'}:return False
        proof_literals = None
        for revision,key,event,operation in ((1,'enroll','enroll','enroll'),(2,'prove','canonical-proof','register_proof'),
                (3,'withdraw','withdraw','withdraw'),(4,'restore','restore','put_source'),(5,'fresh_replay','fresh-replay','register_proof')):
            u = c.get(key) if key=='fresh_replay' else updates[key]
            if not isinstance(u,dict) or u.get('operation')!=operation or u.get('outcome') is not None:return False
            if (u.get('registered_proof_closure_verified') is not True or u.get('row_entailment_complete') is not False
                    or any(u.get(k) is not False for k in ('source_propagation_complete','current_support_computed','candidate_frontier_complete'))):return False
            l = u.get('ledger')
            if not isinstance(l,dict):return False
            for field,w in (('revision',revision),('all_conditions',n),('proof_pending',n),('row',c['target_row'])):
                if type(l.get(field)) is not int or l[field]!=w:return False
            if (type(l.get('affected_conditions')) is not int or not 0<=l['affected_conditions']<=n or l.get('add') is not False
                    or l.get('event')!=f'rk:{c["target_row"]}:{event}' or not digest(l.get('projection_sha256'))
                    or any(l.get(k) is not False for k in ('source_propagation_complete','current_support_computed','candidate_frontier_complete'))):return False
            active = key!='withdraw'
            sources = [dict(name='existing-row-assumptions',version=c['input_projection_sha256'],bundle_sha256=c['source_bundle_sha256'])] if active else []
            if u.get('source_versions')!=sources:return False
            proofs = u.get('proofs')
            if not isinstance(proofs,list) or len(proofs)!=(0 if key=='enroll' else 1):return False
            if proofs:
                p = proofs[0]
                if (not isinstance(p,dict) or type(p.get('proof')) is not int or p['proof']!=1 or p.get('active') is not active
                        or not isinstance(p.get('bindings'),list) or len(p['bindings'])!=c['core_literal_count']):return False
                literals = []
                for b in p['bindings']:
                    if not isinstance(b,dict) or type(b.get('literal')) is not int or not 0<abs(b['literal'])<=atoms:return False
                    if b.get('providers')!=([['existing-row-assumptions',c['input_projection_sha256']]] if active else []):return False
                    literals.append(b['literal'])
                if literals!=sorted(set(literals)) or any(-x in literals for x in literals):return False
                if proof_literals is None:proof_literals=literals
                elif proof_literals!=literals:return False
        stages = c.get('stages')
        if (not isinstance(stages,dict) or set(stages)!={'prepare_canonical_proof','seed_and_full_oracle','enroll',
                'canonical_proof_update','withdraw_update','restore_update'} or any(not elapsed(v) for v in stages.values())
                or not elapsed(c.get('first_pass_case')) or c.get('original_inputs_unchanged') is not True):return False
        f = c.get('database_file')
        if not isinstance(f,dict) or type(f.get('bytes')) is not int or not 0<f['bytes']<=64*1024**2 or not digest(f.get('sha256')):return False
        logical = {k:v for k,v in c.items() if k not in ('stages','first_pass_case','database_file','canonical_output_sha256')}
        if hashlib.sha256(canonical(logical).encode()).hexdigest()!=c['canonical_output_sha256']:return False
    return (cases[0]['basis_context']==cases[1]['basis_context'] and cases[0]['view_context']!=cases[1]['view_context']
        and cases[0]['target']==cases[1]['target'] and cases[0]['target_row']==cases[1]['target_row'])


def valid_receipt(r):
    try:
        return _valid_receipt(r)
    except (ValueError,TypeError,KeyError,IndexError,OverflowError,RecursionError):
        return False
