#!/usr/bin/env python3
"""Small exact control for the Goal #7 compensated-surgery interface.

On the explicit 4-regular C4-free graph ``fifteenRegular``, test every
delete-one/add-two repair.  The ``deletion-only`` mode fixes the survivor
graph to G-u.  The ``compensated`` mode permits an arbitrary spanning
subgraph K <= G-u.  Attachments and the optional edge between the two new
vertices are unrestricted.

Expected result:

    deletion-only: UNSAT
    compensated: SAT u=3 Fedge=False
      A0=[1, 6, 10, 13] A1=[0, 1, 9, 11]
      removed=[(1, 11), (9, 13)]

Thus survivor-edge deletion is a genuine resource, not something that can
always be uncrossed into selector pruning.
"""

from z3 import And, Bool, If, Implies, Solver, Sum, is_true, sat


EDGES = {
    (0, 1), (0, 2), (0, 3), (0, 4),
    (1, 3), (1, 11), (1, 12),
    (2, 4), (2, 7), (2, 14),
    (3, 6), (3, 10),
    (4, 8), (4, 13),
    (5, 6), (5, 8), (5, 12), (5, 14),
    (6, 10), (6, 14),
    (7, 9), (7, 10), (7, 12),
    (8, 12), (8, 13),
    (9, 10), (9, 11), (9, 13),
    (11, 13), (11, 14),
}


def solve(mode: str):
    """Return the first model in ``mode``, or ``None`` if none exists."""
    assert mode in {"deletion-only", "compensated"}
    for deleted in range(15):
        old = [v for v in range(15) if v != deleted]
        vertices = old + [15, 16]
        for gadget_edge in (False, True):
            solver = Solver()
            edge_vars = {}
            for i, a in enumerate(vertices):
                for b in vertices[i + 1 :]:
                    var = Bool(f"e_{mode}_{deleted}_{int(gadget_edge)}_{a}_{b}")
                    edge_vars[a, b] = var
                    if a < 15 and b < 15:
                        if mode == "deletion-only":
                            solver.add(var == ((a, b) in EDGES))
                        else:
                            solver.add(Implies(var, (a, b) in EDGES))
                    elif (a, b) == (15, 16):
                        solver.add(var == gadget_edge)

            def edge(a, b):
                assert a != b
                return edge_vars[tuple(sorted((a, b)))]

            # Minimum degree four.
            for a in vertices:
                solver.add(
                    Sum([If(edge(a, b), 1, 0) for b in vertices if b != a]) >= 4
                )

            # C4-free iff each distinct pair has at most one common neighbor.
            for i, a in enumerate(vertices):
                for b in vertices[i + 1 :]:
                    solver.add(
                        Sum(
                            [
                                If(And(edge(a, c), edge(b, c)), 1, 0)
                                for c in vertices
                                if c not in (a, b)
                            ]
                        )
                        <= 1
                    )

            if solver.check() == sat:
                model = solver.model()
                kept = {
                    pair for pair, var in edge_vars.items() if is_true(model.eval(var))
                }
                removed = sorted(
                    pair
                    for pair in EDGES
                    if deleted not in pair and pair not in kept
                )
                attachments = [
                    sorted(v for v in old if tuple(sorted((v, new))) in kept)
                    for new in (15, 16)
                ]
                return deleted, gadget_edge, attachments, removed
    return None


def main() -> None:
    for mode in ("deletion-only", "compensated"):
        result = solve(mode)
        if result is None:
            print(f"{mode}: UNSAT")
        else:
            deleted, gadget_edge, attachments, removed = result
            print(f"{mode}: SAT u={deleted} Fedge={gadget_edge}")
            print(f"  A0={attachments[0]} A1={attachments[1]}")
            print(f"  removed={removed}")


if __name__ == "__main__":
    main()
