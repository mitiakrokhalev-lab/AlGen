"""Small exhaustive research check of selector SAT; never used by E.run.

The finite domain below is explicit, not the complete AlGen grammar. Signed
integers name selected atoms; Library rows use True/False/None. Two copies of
the ORIGINAL theory require both truth values of a goal. Only the countermodel
copy receives compatible, still-unproved basis hypotheses. SAT models are not
group counterexamples. No minimization or region blocking is attempted here.
"""

import argparse
from dataclasses import dataclass, field
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import random
import resource
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


@dataclass
class Domain:
    n: int
    k: int
    requirements: dict = field(default_factory=dict)
    cover: tuple = ()
    fixed: tuple = ()
    available: tuple = ()  # proved from T and fixed, never from basis B


def literals(n):
    return tuple(lit for atom in range(1, n + 1) for lit in (atom, -atom))


def holds(lit, row):
    value = row[abs(lit) - 1]
    return value is not None and value == (lit > 0)


def clause(question):
    prem, goal = question
    return tuple(-lit for lit in prem) + (goal,)


def question_true(question, model):
    prem, goal = question
    return not all(holds(lit, model) for lit in prem) or holds(goal, model)


def all_candidates(d):
    """Independent explicit domain oracle: no selectors or minimality filter."""
    available = set(d.fixed) | set(d.available)
    fixed_atoms = {abs(lit) for lit in d.fixed}
    for size in range(d.k + 1):
        for atoms in combinations(range(1, d.n + 1), size):
            for signs in product((1, -1), repeat=size):
                prem = tuple(a * s for a, s in zip(atoms, signs))
                have = set(prem) | available
                for goal in literals(d.n):
                    used = set(atoms) | {abs(goal)}
                    if abs(goal) in atoms or abs(goal) in fixed_atoms:
                        continue
                    if any(not set(d.requirements.get(a, ())) <= have for a in used):
                        continue
                    if any(not used.intersection(group) for group in d.cover):
                        continue
                    yield prem, goal


def projected_models(clauses, variables, fixed=()):
    """Real-theory oracle: all 2**n projections, each checked by ordinary SAT."""
    out = []
    with Solver(name="g4", bootstrap_with=clauses) as solver:
        for values in product((False, True), repeat=len(variables)):
            assumptions = [v if bit else -v for v, bit in zip(variables, values)]
            assumptions += [variables[abs(lit) - 1] * (1 if lit > 0 else -1) for lit in fixed]
            if solver.solve(assumptions=assumptions):
                out.append(values)
    return out


def truth_models(clauses, n, fixed=()):
    """Synthetic oracle uses Python truth tables, independently of any solver."""
    return [m for m in product((False, True), repeat=n)
            if all(holds(lit, m) for lit in fixed)
            and all(any(holds(lit, m) for lit in c) for c in clauses)]


def classify(question, rows, models):
    prem, goal = question
    if any(all(holds(lit, r) for lit in prem) and holds(-goal, r) for r in rows):
        return "library_refuted"
    supported = [m for m in models if all(holds(lit, m) for lit in prem)]
    if not supported:
        return "inconsistent_premises"
    if all(holds(goal, m) for m in supported):
        return "derived"
    if all(holds(-goal, m) for m in supported):
        return "theory_refuted"
    return "unknown"


def find_basis(d, clauses, variables, rows):
    """Meta search only; explicit candidate oracle is never called here."""
    if d.n < 1 or not 0 <= d.k <= 3 or len(variables) != d.n:
        raise ValueError("small domain requires n>=1, k=0..3 and n variables")
    if len(set(variables)) != d.n or any(type(v) is not int or v <= 0 for v in variables):
        raise ValueError("selected theory variables must be distinct positive integers")
    lits = literals(d.n)
    for lit in (*d.fixed, *d.available, *(r for rs in d.requirements.values() for r in rs)):
        if type(lit) is not int or lit not in lits:
            raise ValueError("invalid domain literal")
    if any(type(a) is not int or not 1 <= a <= d.n for a in d.requirements):
        raise ValueError("invalid requirement atom")
    if any(any(type(a) is not int or not 1 <= a <= d.n for a in group) for group in d.cover):
        raise ValueError("invalid coverage atom")
    if any(len(r) != d.n or any(v is not None and type(v) is not bool for v in r) for r in rows):
        raise ValueError("rows must contain only bool/None with exactly n values")
    base = [list(c) for c in clauses]
    if any(type(lit) is not int or lit == 0 for c in base for lit in c):
        raise ValueError("invalid theory literal")
    nv = max([*variables, *(abs(lit) for c in base for lit in c)])

    def theory_lit(lit, offset=0):
        v = variables[abs(lit) - 1] + offset
        return v if lit > 0 else -v

    fixed = [[theory_lit(lit)] for lit in d.fixed]
    stats = dict(meta_solves=0, compatibility_solves=0, validation_solves=0)
    with Solver(name="g4", bootstrap_with=base + fixed) as check:
        def validate(assumptions=()):
            stats["validation_solves"] += 1
            return check.solve(assumptions=list(assumptions))
        if not validate():
            raise ValueError("inconsistent original theory/fixed context")
        for lit in d.available:
            if validate([-theory_lit(lit)]):
                raise ValueError("requirement availability is not proved")
        for row in rows:
            known = [theory_lit(i if value else -i) for i, value in enumerate(row, 1) if value is not None]
            if not validate(known):
                raise ValueError("Library row contradicts original theory/fixed")

    pool = IDPool(start_from=2 * nv + 1)
    P = {lit: pool.id(("P", lit)) for lit in lits}
    G = {lit: pool.id(("G", lit)) for lit in lits}
    cnf = base + fixed
    cnf += [[(abs(lit) + nv) * (1 if lit > 0 else -1) for lit in c] for c in base]
    cnf += [[theory_lit(lit, nv)] for lit in d.fixed]
    cnf += CardEnc.atmost(list(P.values()), bound=min(d.k, len(P)), vpool=pool, encoding=EncType.seqcounter).clauses
    cnf += CardEnc.equals(list(G.values()), bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    available = set(d.fixed) | set(d.available)
    for lit in lits:
        # Premises hold in both worlds. A goal is false in the first, true in
        # the second; the latter always keeps the ORIGINAL theory without B.
        cnf += [[-P[lit], theory_lit(lit)], [-P[lit], theory_lit(lit, nv)],
                [-G[lit], -theory_lit(lit)], [-G[lit], theory_lit(lit, nv)],
                [-G[lit], -P[lit]], [-G[lit], -P[-lit]]]
        if lit > 0:
            cnf.append([-P[lit], -P[-lit]])
        if abs(lit) in {abs(x) for x in d.fixed}:
            cnf.append([-G[lit]])
        for required in d.requirements.get(abs(lit), ()):
            if required not in available:
                cnf += [[-P[lit], P[required]], [-G[lit], P[required]]]
    for group in d.cover:
        cnf.append([selector[lit] for lit in lits if abs(lit) in group for selector in (P, G)])
    for ri, row in enumerate(rows):
        miss = [P[lit] for lit in lits if not holds(lit, row)]
        a = pool.id(("row_miss", ri))
        cnf.append([-a, *miss])
        cnf += [[-p, a] for p in miss]
        cnf += [[-G[goal], a] for goal in lits if holds(-goal, row)]

    basis, exceptions, trace = [], [], []
    # Guard variables used in compatibility checks are allocated from the same
    # ID pool. They never overlap either copy of T or the meta selectors.
    with Solver(name="g4", bootstrap_with=cnf) as meta, Solver(name="g4", bootstrap_with=base + fixed) as compatible:
        while True:
            stats["meta_solves"] += 1
            answer = meta.solve()
            if answer is False:
                break
            if answer is not True:
                raise RuntimeError("meta solver did not complete")
            model = {lit for lit in meta.get_model() if lit > 0}
            prem = tuple(lit for lit in lits if P[lit] in model)
            goal, = (lit for lit in lits if G[lit] in model)
            question = (prem, goal)
            selectors = (*P.values(), *G.values())
            # Block the WHOLE exact selector assignment, never a T-model, a
            # minimized question or the entire tree of stronger conditions.
            meta.add_clause([-v if v in model else v for v in selectors])
            c = [theory_lit(lit) for lit in clause(question)]
            guard = pool.id(("admit", len(trace)))
            compatible.add_clause([-guard, *c])
            stats["compatibility_solves"] += 1
            answer = compatible.solve(assumptions=[guard])
            if answer not in (True, False):
                raise RuntimeError("compatibility solver did not complete")
            accepted = answer is True
            trace.append(dict(prem=list(prem), goal=goal, admitted=accepted))
            if accepted:
                compatible.add_clause(c)
                meta.add_clause(c)  # first world only
                basis.append(question)
            else:
                exceptions.append(question)
        return dict(complete=True, basis=basis, exceptions=exceptions, trace=trace,
                    stats=stats, theory_variables=nv, meta_variables=meta.nof_vars(),
                    initial_meta_clauses=len(cnf))


def verify(d, rows, models, result):
    """Every candidate, every extraction/admission and final conditional cover."""
    if not models or result.get("complete") is not True:
        raise AssertionError("missing original models or complete search")
    available = set(d.fixed) | set(d.available)
    assert all(all(holds(lit, m) for m in models) for lit in available)
    assert all(any(all(v is None or v == m[i] for i, v in enumerate(r)) for m in models) for r in rows)
    candidates = list(all_candidates(d))
    kinds = {}
    unknown = set()
    for q in candidates:
        kind = classify(q, rows, models)
        kinds[kind] = kinds.get(kind, 0) + 1
        if kind == "unknown":
            unknown.add(q)
    surviving, accepted, outside, seen = list(models), [], [], set()
    for record in result["trace"]:
        q = (tuple(record["prem"]), record["goal"])
        assert q in unknown and q not in seen, ("invalid/duplicate extraction", q)
        seen.add(q)
        assert any(not question_true(q, m) for m in surviving), ("already covered", q)
        next_models = [m for m in surviving if question_true(q, m)]
        assert record["admitted"] is bool(next_models), ("bad compatibility", q)
        if next_models:
            surviving = next_models
            accepted.append(q)
        else:
            outside.append(q)
    assert accepted == [(tuple(p), g) for p, g in result["basis"]]
    assert outside == [(tuple(p), g) for p, g in result["exceptions"]]
    assert surviving, "contradictory basis"
    exceptions = set(outside)
    uncovered = [q for q in unknown if q not in exceptions and any(not question_true(q, m) for m in surviving)]
    assert not uncovered, ("missing candidates", uncovered)
    return dict(candidates=len(candidates), kinds=kinds, checked_unknown=len(unknown),
                basis=len(accepted), exceptions=len(outside), retained=len(accepted) + len(outside),
                covered_by_compatible_basis=len(unknown - exceptions), uncovered=0,
                original_projected_models=len(models), basis_projected_models=len(surviving))


def synthetic(seed):
    rng = random.Random(seed)
    n = 5
    planted = tuple(rng.choice((False, True)) for _ in range(n))
    cnf = []
    for _ in range(5):
        atoms = rng.sample(range(1, n + 1), rng.randint(1, 3))
        c = [a * rng.choice((1, -1)) for a in atoms]
        if not any(holds(lit, planted) for lit in c):
            c[0] *= -1
        cnf.append(c)
    fixed = (1 if planted[0] else -1,) if seed % 3 == 0 else ()
    models = truth_models(cnf, n, fixed)
    rows = [tuple(value if rng.random() < 0.65 else None for value in rng.choice(models)) for _ in range(4)]
    available = tuple(lit for lit in literals(n) if all(holds(lit, m) for m in models))
    req = {3: (1,), 5: (-2,)} if seed % 2 else {}
    cover = ((1, 3, 5), (2, 4, 5)) if seed % 4 else ()
    return dict(n=n, requirements=req, cover=cover, fixed=fixed, available=available), cnf, rows, models


def real_fixture():
    """A frozen FOUR-ATOM slice of actual group Theory/Library, not native E.run."""
    from algen import enumerate as E
    from algen.library import Library
    from algen.logic import Vocab
    form = E.SchemeForm(Library(), Vocab.section("grp"), "∀ G : Grp", ["center(G)"], with_rows=False)
    form.search.objects = ["1:1", "2:1", "4:2", "6:1"]
    form.fill_rows()
    labels = ("abelian(G)", "cyclic(G)", "perfect(G)", "cyclic(center(G))")
    by_name = {E.atom_name(a): i for i, a in enumerate(form.atoms)}
    columns = [by_name[label] for label in labels]
    variables = [form.sc.T.lit(form.atoms[i]) for i in columns]
    rows = [tuple(True if r[2*i] else False if r[2*i+1] else None for i in columns) for r in form.e]
    if form.skipped:
        raise AssertionError("real Library rows skipped as contradictory")
    clauses = [list(c) for c in form.sc.T.clauses]
    form.sc.s.delete()
    return clauses, variables, rows, dict(atoms=labels, objects=form.search.objects,
        rows=len(rows), scope="four selected atoms of G/center(G), actual grow=1 Theory and Library; no native pipeline or full grammar")


def run(real=True):
    start_wall, start_cpu = time.perf_counter(), time.process_time()
    records = []
    # Frozen seeds/atoms are chosen before seeing outcomes; do not tune them to
    # produce a flattering compression ratio or a native coverage claim.
    fixtures = []
    for seed in range(8100, 8112):
        kw, cnf, rows, models = synthetic(seed)
        fixtures.append((f"synthetic-{seed}", kw, cnf, list(range(1, 6)), rows, models, {}))
    if real:
        cnf, variables, rows, info = real_fixture()
        models = projected_models(cnf, variables)
        fixtures.append(("group-four-atom-slice", dict(n=4, cover=((1, 2, 3), (4,))), cnf, variables, rows, models, info))
    for name, kw, cnf, variables, rows, models, info in fixtures:
        for k in range(4):
            d = Domain(k=k, **kw)
            a, cpu = time.perf_counter(), time.process_time()
            result = find_basis(d, cnf, variables, rows)
            meta_seconds, meta_cpu = time.perf_counter()-a, time.process_time()-cpu
            a = time.perf_counter()
            checked = verify(d, rows, models, result)
            oracle_seconds = time.perf_counter()-a
            records.append(dict(fixture=name, k=k, domain=vars(d), metadata=info,
                input_sha256=hashlib.sha256(json.dumps([cnf, variables, rows], sort_keys=True).encode()).hexdigest(),
                verification=checked, search=result, meta_wall_seconds=meta_seconds,
                meta_cpu_seconds=meta_cpu, oracle_wall_seconds=oracle_seconds))
    return dict(version=1, scope="research finite selector domain; NOT complete AlGen grammar/native coverage or production speedup",
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        complete=True, cases=records,
        totals_scope='Sum over separate fixture/k cases; candidates recur at different k. Not a count of unique AlGen questions.',
        totals={key:sum(r['verification'][key] for r in records)
            for key in ('candidates','checked_unknown','basis','exceptions','retained','uncovered')},
        wall_seconds=time.perf_counter()-start_wall, cpu_seconds=time.process_time()-start_cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        limitations=['Two full theory copies may be too large for native schemes.',
            'Explicit-domain structural rules are req/coverage/signs/fixed/k only; no numerical/pair/symmetry mapping.',
            'No minimization, production filtering/order/core equivalence, archive frontier or dynamic update implementation.',
            'Counts are directed candidates, not old raw forbidden classes/unknown IDs; ratios are not comparable.',
            'Shared explicit oracle and meta timing is a research expense, not a production benchmark.'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True)
    parser.add_argument('--synthetic-only', action='store_true')
    args = parser.parse_args()
    target = Path(args.out)
    if target.exists():
        parser.error('output exists; preserve old results, choose a new file')
    result = run(real=not args.synthetic_only)
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','limitations')}, ensure_ascii=False))


if __name__ == '__main__':
    main()
