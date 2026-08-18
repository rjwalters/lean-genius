#!/usr/bin/env python3
"""Audit the abstract connected-H mu=3 exterior grid.

Rows X and columns Y both have order eight.  H is the canonical Hamiltonian
16-cycle, with x adjacent to y=x and y=x-1.  Forty-eight of the 64 cells are
occupied, six in every row and column.  The exterior graph C is required to
satisfy the exact row/column-hit law forced by HB+BC=J:

  |N_C((a,b)) intersect row x| = 1 iff (x,b) is not an H-edge,

and its column dual.  We test whether those equations alone, or together with
the ambient C4 constraints, are satisfiable.  This is an experimental boundary
audit, not a proof artifact.
"""

from z3 import And, Bool, Implies, Or, PbEq, PbLe, Solver, is_true, sat


ORDER = 8
CELLS = [(a, b) for a in range(ORDER) for b in range(ORDER)]


def h_edge(a: int, b: int) -> bool:
    return b == a or b == (a - 1) % ORDER


def make_solver(with_c4: bool, fixed_occupied=None):
    solver = Solver()
    solver.set(timeout=180_000)
    occ = [Bool(f"o_{a}_{b}") for a, b in CELLS]
    edge_vars = {
        (i, j): Bool(f"c_{i}_{j}")
        for i in range(len(CELLS))
        for j in range(i + 1, len(CELLS))
    }

    def edge(i: int, j: int):
        assert i != j
        return edge_vars[(i, j) if i < j else (j, i)]

    for a in range(ORDER):
        solver.add(PbEq([(occ[8 * a + b], 1) for b in range(ORDER)], 6))
    for b in range(ORDER):
        solver.add(PbEq([(occ[8 * a + b], 1) for a in range(ORDER)], 6))
    if fixed_occupied is not None:
        for i, value in enumerate(fixed_occupied):
            solver.add(occ[i] == value)

    for (i, j), e in edge_vars.items():
        solver.add(Implies(e, And(occ[i], occ[j])))

    # Exact row and column hits for every occupied cell u=(a,b).
    for i, (a, b) in enumerate(CELLS):
        for x in range(ORDER):
            row_terms = [
                (edge(i, 8 * x + y), 1)
                for y in range(ORDER)
                if 8 * x + y != i
            ]
            solver.add(Implies(occ[i], PbEq(row_terms, 0 if h_edge(x, b) else 1)))
        for y in range(ORDER):
            col_terms = [
                (edge(i, 8 * x + y), 1)
                for x in range(ORDER)
                if 8 * x + y != i
            ]
            solver.add(Implies(occ[i], PbEq(col_terms, 0 if h_edge(a, y) else 1)))

    if with_c4:
        for i, (a, b) in enumerate(CELLS):
            for j in range(i + 1, len(CELLS)):
                a2, b2 = CELLS[j]
                common_small = int(a == a2) + int(b == b2)
                assert common_small <= 1
                common_c = [
                    (And(edge(i, k), edge(j, k)), 1)
                    for k in range(len(CELLS))
                    if k not in (i, j)
                ]
                solver.add(
                    Implies(
                        And(occ[i], occ[j]),
                        PbLe(common_c, 1 - common_small),
                    )
                )
    return solver, occ


def missing_factor_balance_solver(require_noncirculant: bool):
    """Classify 2-regular missing matrices satisfying MH^T = HM^T."""
    solver = Solver()
    missing = [[Bool(f"m_{a}_{b}") for b in range(ORDER)] for a in range(ORDER)]
    for a in range(ORDER):
        solver.add(PbEq([(missing[a][b], 1) for b in range(ORDER)], 2))
    for b in range(ORDER):
        solver.add(PbEq([(missing[a][b], 1) for a in range(ORDER)], 2))
    for a in range(ORDER):
        for a2 in range(a + 1, ORDER):
            # |M_row(a) intersect H_row(a2)| = the reversed quantity.
            solver.add(
                Or(*[
                    And(
                        PbEq([(missing[a][b], 1) for b in range(ORDER)
                              if h_edge(a2, b)], value),
                        PbEq([(missing[a2][b], 1) for b in range(ORDER)
                              if h_edge(a, b)], value),
                    )
                    for value in range(3)
                ])
            )
    if require_noncirculant:
        solver.add(
            Or(*[
                missing[a][b] != missing[0][(b - a) % ORDER]
                for a in range(ORDER) for b in range(ORDER)
            ])
        )
    return solver, missing


def main() -> None:
    classification, missing_vars = missing_factor_balance_solver(True)
    classification_result = classification.check()
    print(
        f"balanced missing factor, required noncirculant: {classification_result}",
        flush=True,
    )
    if classification_result == sat:
        classification_model = classification.model()
        missing_model = [
            (a, b)
            for a in range(ORDER) for b in range(ORDER)
            if is_true(classification_model.eval(missing_vars[a][b], model_completion=True))
        ]
        print(f"noncirculant balanced missing cells: {missing_model}", flush=True)
        missing_set = set(missing_model)
        noncirculant_occupied = [cell not in missing_set for cell in CELLS]
        noncirculant, _ = make_solver(True, noncirculant_occupied)
        noncirculant_result = noncirculant.check()
        print(
            f"fixed noncirculant balanced occupancy, C4=True: {noncirculant_result}",
            flush=True,
        )

    base, occ = make_solver(False)
    result = base.check()
    print(f"row/column law, C4=False: {result}", flush=True)
    assert result == sat
    model = base.model()
    occupied = [is_true(model.eval(o, model_completion=True)) for o in occ]
    missing = [CELLS[i] for i, value in enumerate(occupied) if not value]
    print(f"sample missing cells: {missing}", flush=True)

    # First test the full C4 system on the concrete occupancy returned by the
    # easy equations.  This separates the exterior-code obstruction from the
    # expensive quantification over every 2-regular missing-cell graph.
    fixed, _ = make_solver(True, occupied)
    fixed_result = fixed.check()
    print(f"fixed occupancy, C4=True: {fixed_result}", flush=True)

    # Cyclic representatives for missing 2-factors: the union of the identity
    # matching and shift-k matching.  k=7 is exactly the internal C16 factor H.
    for shift in range(1, ORDER):
        cyclic_occupied = [
            not (b == a or b == (a + shift) % ORDER)
            for a, b in CELLS
        ]
        cyclic, _ = make_solver(True, cyclic_occupied)
        cyclic_result = cyclic.check()
        print(f"missing shifts (0,{shift}), C4=True: {cyclic_result}", flush=True)


if __name__ == "__main__":
    main()
