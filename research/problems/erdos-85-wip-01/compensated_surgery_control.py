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

The compensated model also realizes the tight matching normal form from
Science Card #15: the removed survivor edges are a two-edge matching, at
most one matching endpoint lies in the deleted vertex's neighbourhood, and
the two selectors are the balanced safe-colour classes determined by that
matching (with their one shared neighbour counted in both classes).
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


def verify_matching_normal_form(result) -> None:
    """Check the exact tight Card #15 certificate carried by the SAT model."""
    deleted, gadget_edge, attachments, removed = result
    assert not gadget_edge
    assert len(attachments[0]) == len(attachments[1]) == 4
    assert len(removed) == 2

    deleted_neighbors = {
        v for v in range(15) if tuple(sorted((deleted, v))) in EDGES
    }
    assert len(deleted_neighbors) == 4
    assert deleted_neighbors <= set(attachments[0]) | set(attachments[1])

    removed_degree = {v: 0 for v in range(15) if v != deleted}
    for a, b in removed:
        removed_degree[a] += 1
        removed_degree[b] += 1
    assert all(value <= 1 for value in removed_degree.values())
    matching_endpoints = {v for edge in removed for v in edge}
    assert len(matching_endpoints) == 4
    assert len(matching_endpoints & deleted_neighbors) <= 1

    # Pointwise equality in the compensated degree budget:
    # attachment multiplicity = deleted-neighbour loss + matching loss.
    for v in removed_degree:
        multiplicity = sum(v in selector for selector in attachments)
        deleted_loss = int(v in deleted_neighbors)
        assert multiplicity == deleted_loss + removed_degree[v]

    # With K = G-u-M, each selector is independent in K's
    # common-neighbour conflict graph.  This simultaneously checks the
    # old-old and mixed C4 budgets for an edgeless two-vertex gadget.
    kept_old = {
        edge for edge in EDGES if deleted not in edge and edge not in removed
    }
    old = [v for v in range(15) if v != deleted]

    def old_edge(a, b):
        return tuple(sorted((a, b))) in kept_old

    for selector in attachments:
        for i, a in enumerate(selector):
            for b in selector[i + 1 :]:
                common = [z for z in old if z not in (a, b)
                          and old_edge(a, z) and old_edge(b, z)]
                assert not common
    assert len(set(attachments[0]) & set(attachments[1])) <= 1


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
            if mode == "compensated":
                verify_matching_normal_form(result)
                print("  matching-normal-form: VERIFIED")


if __name__ == "__main__":
    main()
