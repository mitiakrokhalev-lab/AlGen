"""Diagnostic global SAT backend comparison; mathematical inputs unchanged."""
import sys
from pathlib import Path

sys.path.insert(0, '/workspace/work/algen-dev/py')
from tools import profile_memory as P

i = sys.argv.index('--global-solver')
backend = sys.argv[i + 1]
del sys.argv[i:i + 2]
phase_policy = 'random'
if '--phase-policy' in sys.argv:
    i = sys.argv.index('--phase-policy')
    phase_policy = sys.argv[i + 1]
    del sys.argv[i:i + 2]
if phase_policy not in {'random', 'saved', 'projected', 'schema'}:
    raise ValueError('Unsupported diagnostic phase policy')
if backend not in {'g4', 'g4-incr', 'm22', 'cadical195'}:
    raise ValueError('Unsupported diagnostic solver')

if '--backend-child' not in sys.argv:
    original_popen = P.subprocess.Popen

    def launch(command, *args, **kwargs):
        if '--child' in command and 'tools.profile_memory' in command:
            offset = command.index('tools.profile_memory') + 1
            command = [sys.executable, '-B', __file__, '--global-solver', backend,
                       '--phase-policy', phase_policy,
                       '--backend-child'] + command[offset:]
        return original_popen(command, *args, **kwargs)

    P.subprocess.Popen = launch
    P.main()
else:
    import hashlib
    import json
    import signal
    import time
    import weakref
    from collections import defaultdict
    from algen import logic, fast, enumerate as E
    from pysat import solvers

    sys.argv.remove('--backend-child')
    out = Path(sys.argv[sys.argv.index('--out') + 1])
    harness_source = Path(__file__).read_bytes()
    harness_hash = hashlib.sha256(harness_source).hexdigest()
    (out / 'diagnostic-harness.py').write_bytes(harness_source)
    original_factory = logic.Solver
    original_solve = solvers.Solver.solve
    original_set_phases = solvers.Solver.set_phases
    instances = {}
    created = []
    times = defaultdict(lambda: dict(calls=0, seconds=0.0))
    original_bank_init = fast.Bank.__init__
    original_bank_sat = fast.Bank.sat
    active_bank = None
    phase_scopes = []
    schema_scopes = {}
    original_run = E.run

    def run(*args, **kwargs):
        form = kwargs.get('form', args[3] if len(args) > 3 else None)
        theory = getattr(getattr(form, 'sc', None), 'T', None)
        old_scope = schema_scopes.get(id(theory))
        if theory is not None:
            # Read existing IDs only: do not allocate new theory variables.
            schema_scopes[id(theory)] = sorted({n for a in form.atoms
                if type(n := theory._lc.get(a)) is int and n > 0})
        try:
            return original_run(*args, **kwargs)
        finally:
            if old_scope is None:
                schema_scopes.pop(id(theory), None)
            else:
                schema_scopes[id(theory)] = old_scope

    def bank_sat(self, *args, **kwargs):
        global active_bank
        before = active_bank
        active_bank = self
        try:
            return original_bank_sat(self, *args, **kwargs)
        finally:
            active_bank = before

    def set_phases(self, literals):
        scope_size = None
        if active_bank is not None and self is active_bank.s:
            scope = (schema_scopes.get(id(active_bank.T)) if phase_policy == 'schema'
                     else [int(v) for v in active_bank.vars[-2048:]])
            if scope is not None:
                literals = [literals[v - 1] for v in scope if v <= len(literals)]
                scope_size = len(literals)
        result = original_set_phases(self, literals)
        if scope_size is not None:
            phase_scopes.append(scope_size)
        return result

    def bank_init(self, *args, **kwargs):
        original_bank_init(self, *args, **kwargs)
        if phase_policy == 'saved':
            self.phases = [[]]  # regular solve; no warm_start, no assumption changes

    def factory(*args, **kwargs):
        if kwargs.get('name') == 'g4':
            kwargs['name'] = 'g4' if backend == 'g4-incr' else backend
            if backend == 'g4-incr':
                kwargs['incr'] = True
        solver = original_factory(*args, **kwargs)
        actual = type(solver.solver).__name__
        instances[id(solver)] = (weakref.ref(solver), actual)
        created.append(dict(actual=actual, incremental=kwargs.get('incr', False),
                            variables=solver.nof_vars(), clauses=solver.nof_clauses()))
        return solver

    def solve(self, *args, **kwargs):
        start = time.perf_counter()
        result = original_solve(self, *args, **kwargs)
        elapsed = time.perf_counter() - start
        entry = instances.get(id(self))
        if entry and entry[0]() is self:
            stat = times[f'{entry[1]}:{result!r}']
            stat['calls'] += 1
            stat['seconds'] += elapsed
        return result

    def interrupted(*args):
        raise KeyboardInterrupt('profile parent watchdog')

    logic.Solver = factory
    fast.Bank.__init__ = bank_init
    solvers.Solver.solve = solve
    if phase_policy in {'projected', 'schema'}:
        fast.Bank.sat = bank_sat
        solvers.Solver.set_phases = set_phases
    if phase_policy == 'schema':
        E.run = run
    signal.signal(signal.SIGTERM, interrupted)
    try:
        P.main()
    finally:
        receipt = dict(scope='diagnostic backend selection; completion is in measurement.json',
                       requested_backend=backend, phase_policy=phase_policy,
                       created=created, solve_times=dict(times),
                       phase_scope_sizes=phase_scopes,
                       phase_scope_kind={
                           'random': 'all clause variables, four original random vectors',
                           'saved': 'no new phase preferences, regular solve',
                           'projected': 'last registered Bank variables, up to 2048; not an LRU',
                           'schema': 'cached variable IDs of schema atoms at E.run entry',
                       }[phase_policy],
                       timing_scope='completed global Solver.solve only; excludes solve_limited and interrupted calls',
                       harness_sha256=harness_hash)
        (out / 'solver-backend.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
