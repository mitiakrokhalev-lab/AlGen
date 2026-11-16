"""An immutable Theory basis for sequential proof views, not a global cache."""
from contextlib import contextmanager
import hashlib
import json
import sys
import time

from pysat.solvers import Solver

from .logic import REFLEXIVE, SYMMETRIC
from .value_ledger import canonical, structure


def _stamp():
    return time.perf_counter(), time.process_time()


class FrozenTheoryBasis:
    """Pin one exact Theory; share only its unconditional CNF and private solver.

    Source facts are assumptions on individual queries. No mutable solver or
    transaction scope is public. The owner must outlive its borrowed views.
    Private helpers are trusted internals, not an arbitrary-Python sandbox.
    """
    def __init__(self, theory, reference):
        start = _stamp()
        self.theory = self._owner = theory
        self.schema = self._pinned_schema = tuple(theory.atoms)
        self._schema_store, self._clause_store = theory.atoms, theory.clauses
        self._var_store, self._cache_store = theory.var, theory._lc
        self._symmetric, self._reflexive = frozenset(SYMMETRIC), frozenset(REFLEXIVE)
        self._data_store, self._offset_store = theory.clauses.data, theory.clauses.offs
        self.data = memoryview(self._data_store).toreadonly()
        self.offsets = memoryview(self._offset_store).toreadonly()
        self._closed, self._solver, self._depth = False, None, 0
        self._metrics = dict(snapshot_builds=1, views_bound=0, clause_hash_calls=0,
            clause_hash_wall_seconds=0., clause_hash_cpu_seconds=0.,
            solver_bootstrap_attempts=0, solver_bootstraps=0, solver_discards=0,
            solver_bootstrap_wall_seconds=0., solver_bootstrap_cpu_seconds=0.)
        try:
            t = _stamp()
            self._var_snapshot = dict(theory.var)
            self._cache_snapshot = dict(theory._lc)
            self._elapsed('literal_map_snapshot',t)
            t = _stamp()
            h = hashlib.sha256()
            for atom in self.schema:
                h.update((canonical(structure(atom))+'\n').encode())
            self._elapsed('schema_hash',t)
            self.header = json.loads(canonical(dict(version=1, reference=reference,
                clauses_sha256=self._clause_digest(), schema_sha256=h.hexdigest())))
            self.identity = hashlib.sha256(canonical(self.header).encode()).hexdigest()
            self._elapsed('snapshot',start)
        except BaseException:
            self.close()
            raise

    def _elapsed(self, name, start):
        self._metrics[name+'_wall_seconds'] = self._metrics.get(name+'_wall_seconds',0.)+time.perf_counter()-start[0]
        self._metrics[name+'_cpu_seconds'] = self._metrics.get(name+'_cpu_seconds',0.)+time.process_time()-start[1]

    def stats(self):
        """Fresh aggregate counters; excludes view-specific proof/header work."""
        return dict(self._metrics,solver_live=self._solver is not None)

    def _clause_digest(self):
        t = _stamp()
        try:
            h = hashlib.sha256(canonical([sys.byteorder,self.data.format,self.offsets.format,
                                         len(self.data),len(self.offsets)]).encode())
            h.update(self.data)
            h.update(self.offsets)
            return h.hexdigest()
        finally:
            self._metrics['clause_hash_calls'] += 1
            self._elapsed('clause_hash',t)

    def check(self, *, force=False):
        if self._closed:
            raise RuntimeError('frozen Theory basis is closed')
        boundary = force or not self._depth
        if (self.theory is not self._owner or self.schema is not self._pinned_schema
                or self.theory.atoms is not self._schema_store
                or self.theory.clauses is not self._clause_store
                or self.theory.var is not self._var_store or self.theory._lc is not self._cache_store
                or self._clause_store.data is not self._data_store
                or self._clause_store.offs is not self._offset_store
                or len(self.theory.atoms) != len(self.schema)
                or (boundary and self._clause_digest() != self.header['clauses_sha256'])
                or hashlib.sha256(canonical(self.header).encode()).hexdigest() != self.identity):
            raise ValueError('frozen Theory changed; a new checked context is required')
        if boundary:
            start = _stamp()
            try:
                # Slot identities also distinguish structurally typed values
                # that Python equality merges (for example int(1)/bool(True)).
                if (any(a is not b for a,b in zip(self.theory.atoms,self._pinned_schema))
                        or self.theory.var != self._var_snapshot):
                    raise ValueError('frozen Theory changed; schema or literal namespace differs')
                if self.theory._lc != self._cache_snapshot:
                    # Theory.lit may legitimately add memoized lookups for an
                    # existing atom/reflexive constant. Never admit a new alias
                    # or rebind a previously frozen cache entry.
                    for a,n in self.theory._lc.items():
                        if a in self._cache_snapshot:
                            expected = self._cache_snapshot[a]
                        else:
                            expected = self._literal_number(a)
                        if n != expected:
                            raise ValueError('frozen Theory changed; literal cache rebound')
                    for a,n in self._cache_snapshot.items():
                        if a not in self.theory._lc or self.theory._lc[a] != n:
                            raise ValueError('frozen Theory changed; literal cache removed')
                    self._cache_snapshot.update(self.theory._lc)
            finally:
                self._elapsed('literal_map_validation',start)

    def _literal_number(self, atom):
        """Resolve solely in the captured namespace, including initial aliases."""
        canonical_atom = atom
        if atom[0] == 'r' and atom[1] in self._symmetric and str(atom[3]) < str(atom[2]):
            canonical_atom = (atom[0],atom[1],atom[3],atom[2])
        if canonical_atom[0] == 'r' and canonical_atom[1] in self._reflexive and canonical_atom[2] == canonical_atom[3]:
            return 0
        if canonical_atom not in self._var_snapshot:
            raise ValueError('row proof atom is outside the frozen literal schema')
        return self._cache_snapshot.get(atom,self._var_snapshot[canonical_atom])

    def _discard_solver(self):
        if self._solver is not None:
            self._solver.delete()
            self._solver = None
            self._metrics['solver_discards'] += 1

    @contextmanager
    def _stable(self):
        if self._depth:
            raise RuntimeError('reentrant frozen Theory operation is forbidden')
        self.check(force=True)
        self._depth += 1
        try:
            yield
            self.check(force=True)
        except BaseException:
            self._discard_solver()
            raise
        finally:
            self._depth -= 1

    @property
    def _query_solver(self):
        self.check()
        if self._solver is None:
            self.check(force=True)
            start = _stamp()
            self._metrics['solver_bootstrap_attempts'] += 1
            try:
                clauses = (self.data[self.offsets[i]:self.offsets[i+1]].tolist()
                           for i in range(len(self.offsets)-1))
                self._solver = Solver(name='g4',bootstrap_with=clauses)
                self.check(force=True)
                self._metrics['solver_bootstraps'] += 1
            except BaseException:
                # Also required for a direct query outside a row transaction.
                self._discard_solver()
                raise
            finally:
                self._elapsed('solver_bootstrap',start)
        return self._solver

    def close(self):
        if not self._closed:
            if self._depth:
                raise RuntimeError('cannot close a basis during a proof operation')
            self._discard_solver()
            self.data.release()
            self.offsets.release()
            if hasattr(self,'_var_snapshot'):
                self._var_snapshot.clear()
            if hasattr(self,'_cache_snapshot'):
                self._cache_snapshot.clear()
            self._closed = True

    def __enter__(self):
        self.check()
        return self

    def __exit__(self, *exc):
        self.close()
