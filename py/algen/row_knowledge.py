"""Checked entailments and registered-source withdrawal for one ledger row.

Source bundles are externally checked assumptions, not facts established by
source_checked. Only registered proofs are maintained; this is not full row
backbone completion, global Library propagation, current support or a frontier.
All condition verdicts remain pending. No SAT models are used as group examples.
"""
from contextlib import contextmanager
import hashlib
import json

import numpy as np

from .live import source_checked
from .frozen_theory import FrozenTheoryBasis
from .value_ledger import canonical, structure, _unstructure


class FrozenRowTheory:
    """Exact view over a fresh or explicitly borrowed immutable Theory basis.

    A shared basis saves full schema hashing and Solver bootstrap across
    different views of the same unchanged base during a first pass. Each view
    keeps its complete structural header and proof namespace. No row facts or
    fixed assumptions are made permanent in the shared solver.
    """
    def __init__(self, theory, atoms, reference, *, basis=None):
        self._closed, self._owns_basis = False, basis is None
        self._basis = FrozenTheoryBasis(theory,reference) if basis is None else basis
        try:
            if (not isinstance(self._basis,FrozenTheoryBasis) or self._basis.theory is not theory
                    or canonical(reference) != canonical(self._basis.header['reference'])):
                raise ValueError('borrowed basis must match exact Theory owner and reference')
            self._basis.check(force=True)
            self.theory, self.atoms = theory, tuple(atoms)
            self.schema = self._basis.schema
            self.literals = []
            count = len(theory.atoms)
            for atom in self.atoms:
                if atom[0] == 'pair':
                    self.literals.append(None)
                    continue
                if atom[0] not in ('p','r'):
                    raise ValueError('row proof atom is outside the frozen literal schema')
                lit = self._basis._literal_number(atom)
                if type(lit) is not int or not 0 <= lit <= len(self.schema):
                    raise ValueError('invalid frozen primitive literal mapping')
                self.literals.append(lit)
            if len(theory.atoms) != count:
                raise ValueError('literal lookup mutated the Theory schema')
            self.header = json.loads(canonical(dict(self._basis.header,
                view_atoms=[structure(a) for a in self.atoms],view_literals=self.literals)))
            self.identity = hashlib.sha256(canonical(self.header).encode()).hexdigest()
            self.check(force=True)
            self._basis._metrics['views_bound'] += 1
        except BaseException:
            if self._owns_basis:
                self._basis.close()
            self._closed = True
            raise

    def _check_view(self):
        if self._closed:
            raise RuntimeError('frozen Theory session is closed')
        if (self.theory is not self._basis.theory or self.schema is not self._basis.schema
                or self.literals != self.header['view_literals']
                or [structure(a) for a in self.atoms] != self.header['view_atoms']
                or hashlib.sha256(canonical(self.header).encode()).hexdigest() != self.identity):
            raise ValueError('frozen Theory changed; a new checked context is required')

    def check(self, *, force=False):
        self._check_view()
        self._basis.check(force=force)

    @contextmanager
    def _stable(self):
        self._check_view()
        with self._basis._stable():
            self._check_view()
            yield
            self._check_view()

    @property
    def _solver(self):
        return self._basis._solver

    @property
    def _query_solver(self):
        self.check()
        return self._basis._query_solver

    def close(self):
        if not self._closed:
            if self._basis._depth:
                raise RuntimeError('cannot close a view during a proof operation')
            if self._owns_basis:
                self._basis.close()
            self._closed = True

    def __enter__(self):
        self.check()
        return self

    def __exit__(self, *exc):
        self.close()

    def literal(self, atom, value):
        if type(atom) is not int or not 0 <= atom < len(self.atoms) or type(value) is not bool:
            raise ValueError('primitive atom index and Boolean claim required')
        n = self.literals[atom]
        if n is None:
            raise ValueError('a pair is not an atomic proof conclusion')
        if n == 0:
            if not value:
                raise ValueError('a source denies a reflexive tautology')
            return 0
        return n if value else -n

    def compatible(self, facts):
        if any(-x in facts for x in facts) or not self._query_solver.solve(assumptions=sorted(facts)):
            raise ValueError('all active source facts must be jointly compatible with Theory')

    def certificate(self, atom, value, core):
        return dict(version=1, context=self.identity, atom=atom,
            target=structure(self.atoms[atom]), value=value,
            core=[dict(literal=x, atom=structure(self.schema[abs(x)-1]), value=x > 0) for x in sorted(set(core))])

    def verify(self, certificate):
        c = certificate
        if (not isinstance(c, dict) or type(c.get('version')) is not int or c['version'] != 1
                or c.get('context') != self.identity):
            raise ValueError('invalid proof context')
        lit = self.literal(c.get('atom'), c.get('value'))
        if c.get('target') != structure(self.atoms[c['atom']]) or not isinstance(c.get('core'), list):
            raise ValueError('proof target/core does not match its structural schema')
        core = []
        for p in c['core']:
            n = p.get('literal') if isinstance(p, dict) else None
            if (type(n) is not int or not 0 < abs(n) <= len(self.schema)
                    or p.get('atom') != structure(self.schema[abs(n)-1])
                    or type(p.get('value')) is not bool or p['value'] != (n > 0)):
                raise ValueError('invalid structural proof premise')
            core.append(n)
        if core != sorted(set(core)):
            raise ValueError('proof core must be canonical and duplicate-free')
        s = self._query_solver
        if not s.solve(assumptions=core):
            raise ValueError('inconsistent proof core cannot justify a row value')
        if lit == 0:
            if core:
                raise ValueError('reflexive-constant proof must have an empty core')
        elif s.solve(assumptions=[*core, -lit]):
            raise ValueError('proof conclusion is not entailed by Theory and core')
        return core

    def derive(self, atom, facts):
        self.compatible(facts)
        positive = self.literal(atom, True)
        if positive == 0:
            return self.certificate(atom, True, [])
        for value, conclusion in ((True, positive), (False, -positive)):
            if not self._query_solver.solve(assumptions=[*sorted(facts), -conclusion]):
                raw = self._query_solver.get_core()
                if raw is None:
                    core = sorted(facts)
                else:
                    if -conclusion not in raw or any(x not in facts and x != -conclusion for x in raw):
                        raise ValueError('solver returned an invalid assumption core')
                    core = sorted(set(raw) - {-conclusion})
                c = self.certificate(atom, value, core)
                self.verify(c)
                return c
        return None  # formal non-entailment, never a group counterexample


class RowKnowledge:
    """Atomic registered-proof closure, scoped to one concrete existing row."""
    def __init__(self, ledger, theory, row):
        self.ledger, self.theory, self.row = ledger, theory, row
        self.db = ledger.db
        if self.db.in_transaction:
            raise RuntimeError('install RowKnowledge outside a transaction')
        if type(row) is not int:
            raise ValueError('concrete row index required')
        rec = self.db.execute('SELECT identity FROM rows WHERE id=?', (row,)).fetchone()
        if rec is None or ledger._meta('atoms') != theory.header['view_atoms']:
            raise ValueError('row or view does not belong to the frozen ledger domain')
        self.identity = _unstructure(json.loads(rec[0]))
        self.db.executescript('''
        CREATE TABLE IF NOT EXISTS rk_rows(row_id INTEGER PRIMARY KEY REFERENCES rows(id), context TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS rk_sources(row_id INTEGER, name TEXT, version TEXT, bundle TEXT NOT NULL,
          active INTEGER NOT NULL, PRIMARY KEY(row_id,name,version));
        CREATE UNIQUE INDEX IF NOT EXISTS rk_one_version ON rk_sources(row_id,name) WHERE active=1;
        CREATE TABLE IF NOT EXISTS rk_claims(row_id INTEGER, name TEXT, version TEXT, col INTEGER, literal INTEGER NOT NULL,
          PRIMARY KEY(row_id,name,version,col), FOREIGN KEY(row_id,name,version) REFERENCES rk_sources(row_id,name,version));
        CREATE TABLE IF NOT EXISTS rk_proofs(id INTEGER PRIMARY KEY, row_id INTEGER NOT NULL,
          certificate TEXT NOT NULL, active INTEGER NOT NULL, UNIQUE(row_id,certificate));
        CREATE TABLE IF NOT EXISTS rk_events(row_id INTEGER, event TEXT, packet TEXT NOT NULL, receipt TEXT NOT NULL,
          PRIMARY KEY(row_id,event));
        ''')
        self._context_check(required=False)

    def _context_check(self, required=True):
        self.theory.check()
        rec = self.db.execute('SELECT context FROM rk_rows WHERE row_id=?', (self.row,)).fetchone()
        if rec is None:
            if required:
                raise ValueError('row is not enrolled')
        elif rec[0] != canonical(self.theory.header):
            raise ValueError('frozen proof context changed; explicit migration required')

    def _source(self, value):
        if (not isinstance(value, dict) or any(not isinstance(value.get(k), str) or not value[k]
                for k in ('name', 'version')) or not isinstance(value.get('claims'), list)):
            raise ValueError('source name/version/claims required')
        source_checked(value.get('source'))
        claims = {}
        for pair in value['claims']:
            if not isinstance(pair, (list,tuple)) or len(pair) != 2:
                raise ValueError('source claims must be atom/Boolean pairs')
            atom, truth = pair
            self.theory.literal(atom, truth)
            if atom in claims and claims[atom] != truth:
                raise ValueError('one bundle contradicts itself')
            claims[atom] = truth
        return dict(name=value['name'], version=value['version'], source=value['source'],
                    claims=[[a, claims[a]] for a in sorted(claims)])

    def _put_source(self, source):
        name, version, bundle = source['name'], source['version'], canonical(source)
        old = self.db.execute('SELECT bundle FROM rk_sources WHERE row_id=? AND name=? AND version=?',
                              (self.row, name, version)).fetchone()
        if old and old[0] != bundle:
            raise ValueError('source id/version is bound to different claims or provenance')
        self.db.execute('UPDATE rk_sources SET active=0 WHERE row_id=? AND name=?', (self.row, name))
        if old:
            self.db.execute('UPDATE rk_sources SET active=1 WHERE row_id=? AND name=? AND version=?', (self.row,name,version))
        else:
            self.db.execute('INSERT INTO rk_sources VALUES(?,?,?,?,1)', (self.row,name,version,bundle))
            self.db.executemany('INSERT INTO rk_claims VALUES(?,?,?,?,?)',
                ((self.row,name,version,2*a+(not v),self.theory.literal(a,v)) for a,v in source['claims']))
        if self.db.execute('SELECT count(*) FROM rk_sources WHERE row_id=? AND active=1', (self.row,)).fetchone()[0] > 512:
            raise ValueError('registered row-source budget exceeded')

    def _claims(self):
        return list(self.db.execute('SELECT c.col,c.literal,c.name,c.version FROM rk_claims c JOIN rk_sources s '
            'ON s.row_id=c.row_id AND s.name=c.name AND s.version=c.version WHERE c.row_id=? AND s.active=1 '
            'ORDER BY c.name,c.version,c.col', (self.row,)))

    def _store_proof(self, certificate):
        self.theory.verify(certificate)
        self.db.execute('INSERT OR IGNORE INTO rk_proofs(row_id,certificate,active) VALUES(?,?,0)',
                        (self.row,canonical(certificate)))
        if self.db.execute('SELECT count(*) FROM rk_proofs WHERE row_id=?', (self.row,)).fetchone()[0] > 4096:
            raise ValueError('registered row-proof budget exceeded')

    def _project(self, claims):
        facts, providers = set(), {}
        projection = np.zeros(self.ledger._meta('ncols'), dtype=bool)
        for c in claims:
            projection[c['col']] = True
            if c['literal']:
                facts.add(c['literal'])
                providers.setdefault(c['literal'], set()).add((c['name'],c['version']))
        self.theory.compatible(facts)  # all active facts, not just one proof's core
        applicability = []
        for p in self.db.execute('SELECT id,certificate FROM rk_proofs WHERE row_id=? ORDER BY id', (self.row,)):
            cert = json.loads(p['certificate'])
            core = self.theory.verify(cert)
            active = all(n in providers for n in core)
            self.db.execute('UPDATE rk_proofs SET active=? WHERE id=?', (int(active),p['id']))
            bindings = [dict(literal=n, providers=[list(x) for x in sorted(providers.get(n,()))]) for n in core]
            applicability.append(dict(proof=p['id'],active=active,bindings=bindings))
            if active:
                projection[2*cert['atom']+(not cert['value'])] = True
        for i, atom in enumerate(self.theory.atoms):
            if atom[0] == 'pair':
                components = self.ledger._meta('pairs')[str(i)]
                columns = [2*c+(not atom[4]) for c in components]
                projection[2*i] = all(projection[c] for c in columns)
                projection[2*i+1] = any(projection[c^1] for c in columns)
            elif projection[2*i] and projection[2*i+1]:
                raise ValueError('registered projection has contradictory conclusions')
        return projection, applicability

    def _perform(self, event, operation, payload, expected_revision):
        if not isinstance(event, str) or not event or type(expected_revision) is not int:
            raise ValueError('event and expected ledger revision required')
        packet = canonical(dict(context=self.theory.header,row=structure(self.identity),operation=operation,
                                payload=payload,expected_revision=expected_revision))
        with self.ledger._atomic(), self.theory._stable():
            previous = self.db.execute('SELECT packet,receipt FROM rk_events WHERE row_id=? AND event=?', (self.row,event)).fetchone()
            if previous:
                if previous[0] != packet:
                    raise ValueError('knowledge event reused with different operation or input')
                return dict(json.loads(previous[1]),replayed=True)
            if self.ledger._meta('revision') != expected_revision:
                raise ValueError('stale knowledge revision')
            if operation == 'enroll':
                self._context_check(required=False)
                if self.db.execute('SELECT 1 FROM rk_rows WHERE row_id=?', (self.row,)).fetchone():
                    raise ValueError('row already enrolled')
                self.db.execute('INSERT INTO rk_rows VALUES(?,?)', (self.row,canonical(self.theory.header)))
                for source in payload:
                    self._put_source(source)
            else:
                self._context_check()
                if operation == 'put_source':
                    self._put_source(payload)
                elif operation == 'withdraw':
                    name, version = payload
                    if not self.db.execute('SELECT 1 FROM rk_sources WHERE row_id=? AND name=? AND version=?',
                                           (self.row,name,version)).fetchone():
                        raise ValueError('source version was never registered')
                    self.db.execute('UPDATE rk_sources SET active=0 WHERE row_id=? AND name=? AND version=?', (self.row,name,version))
            claims = self._claims()
            facts = {c['literal'] for c in claims if c['literal']}
            self.theory.compatible(facts)
            outcome = None
            if operation == 'derive':
                certificate = self.theory.derive(payload, facts)
                outcome = 'undetermined' if certificate is None else 'derived'
                if certificate is not None:
                    self._store_proof(certificate)
            elif operation == 'register_proof':
                self._store_proof(payload)
            projection, proofs = self._project(claims)
            if operation == 'enroll':
                current = self.db.execute('SELECT v.projection FROM rows r JOIN row_versions v ON v.row_id=r.id '
                    'AND v.revision=r.revision WHERE r.id=?', (self.row,)).fetchone()[0]
                if self.ledger._pack(projection) != current:
                    raise ValueError('initial sources do not explain the stored row projection')
            source_versions = [dict(name=r['name'],version=r['version'],bundle_sha256=hashlib.sha256(r['bundle'].encode()).hexdigest())
                for r in self.db.execute('SELECT name,version,bundle FROM rk_sources WHERE row_id=? AND active=1 ORDER BY name', (self.row,))]
            metadata = dict(kind='user',reference=f'RowKnowledge:{self.row}:{event}',
                            context=self.theory.identity,active_sources=source_versions,registered_proofs=proofs)
            ledger_receipt = self.ledger._apply_row_in_transaction(f'rk:{self.row}:{event}', self.identity,
                projection, metadata, expected_revision, _managed=True)
            receipt = dict(operation=operation,outcome=outcome,ledger=ledger_receipt,
                source_versions=source_versions,proofs=proofs,registered_proof_closure_verified=True,
                row_entailment_complete=False,source_propagation_complete=False,current_support_computed=False,
                candidate_frontier_complete=False)
            self.db.execute('INSERT INTO rk_events VALUES(?,?,?,?)', (self.row,event,packet,canonical(receipt)))
            self.theory.check()
            return receipt

    def enroll(self, event, sources, expected_revision):
        if not isinstance(sources, list) or len(sources) > 512:
            raise ValueError('bounded source list required')
        sources = [self._source(x) for x in sources]
        if len({s['name'] for s in sources}) != len(sources):
            raise ValueError('enrolment must have one version of each source')
        return self._perform(event,'enroll',sorted(sources,key=lambda x:x['name']),expected_revision)

    def put_source(self, event, source, expected_revision):
        return self._perform(event,'put_source',self._source(source),expected_revision)

    def withdraw(self, event, name, version, expected_revision):
        if any(not isinstance(x,str) or not x for x in (name,version)):
            raise ValueError('source name/version required')
        return self._perform(event,'withdraw',[name,version],expected_revision)

    def derive(self, event, atom, expected_revision):
        self.theory.literal(atom,True)
        return self._perform(event,'derive',atom,expected_revision)

    def register_proof(self, event, certificate, expected_revision):
        return self._perform(event,'register_proof',certificate,expected_revision)
