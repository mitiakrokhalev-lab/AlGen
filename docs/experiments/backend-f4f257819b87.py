"""Diagnostic global SAT backend comparison; mathematical inputs unchanged."""
import sys
from pathlib import Path

sys.path.insert(0, '/workspace/work/algen-dev/py')
from tools import profile_memory as P

i = sys.argv.index('--global-solver')
backend = sys.argv[i + 1]
del sys.argv[i:i + 2]
if backend not in {'g4', 'g4-incr', 'm22', 'cadical195'}:
    raise ValueError('Unsupported diagnostic solver')

if '--backend-child' not in sys.argv:
    original_popen = P.subprocess.Popen

    def launch(command, *args, **kwargs):
        if '--child' in command and 'tools.profile_memory' in command:
            offset = command.index('tools.profile_memory') + 1
            command = [sys.executable, '-B', __file__, '--global-solver', backend,
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
    from algen import logic
    from pysat import solvers

    sys.argv.remove('--backend-child')
    out = Path(sys.argv[sys.argv.index('--out') + 1])
    harness_source = Path(__file__).read_bytes()
    harness_hash = hashlib.sha256(harness_source).hexdigest()
    (out / 'diagnostic-harness.py').write_bytes(harness_source)
    original_factory = logic.Solver
    original_solve = solvers.Solver.solve
    instances = {}
    created = []
    times = defaultdict(lambda: dict(calls=0, seconds=0.0))

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
    solvers.Solver.solve = solve
    signal.signal(signal.SIGTERM, interrupted)
    try:
        P.main()
    finally:
        receipt = dict(scope='diagnostic backend selection; completion is in measurement.json',
                       requested_backend=backend, created=created, solve_times=dict(times),
                       timing_scope='completed global Solver.solve only; excludes solve_limited and interrupted calls',
                       harness_sha256=harness_hash)
        (out / 'solver-backend.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
