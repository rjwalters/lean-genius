#!/usr/bin/env python3
"""Exact d=4, k=2 control for compensated growing-k surgery.

On the repository ``fifteenRegular`` graph, delete an independent pair with
a common neighbour, add three vertices, permit arbitrary survivor-edge
deletion and arbitrary old-new attachments, and require the final graph to be
4-regular and C4-free.  The gadget is tested with zero or one internal edge.
The tight capacity identity then forces respectively two or one deleted
survivor edges.

This is the smallest control combining the two features left alive after
Science Card #15 divergence #60: a multi-vertex independent deletion set and
genuine survivor-edge deletion.

The final queries negate the first-model incidence conjectures over the full
independent-pair space.  Both negations are satisfiable: solutions may have
three (rather than two) multiplicity-two survivors, and the selector-pair
incidence graph need not be P3 or complement the gadget edge.  The exact
surviving invariant is only linearity (each selector pair has at most one
shared survivor).
"""

from itertools import combinations

from z3 import And, Bool, If, Implies, Or, Solver, Sum, is_true, sat

from compensated_surgery_control import EDGES


def original_edge(a: int, b: int) -> bool:
    return tuple(sorted((a, b))) in EDGES


def candidate_deleted_pairs(require_common_root):
    for a, b in combinations(range(15), 2):
        if original_edge(a, b):
            continue
        common = [
            r for r in range(15)
            if r not in (a, b) and original_edge(a, r) and original_edge(b, r)
        ]
        if require_common_root is None or bool(common) == require_common_root:
            yield (a, b), (common[0] if common else None)


def solve(gadget_edges: int, require_common_root, refinement=None):
    assert gadget_edges in (0, 1)
    for deleted, root in candidate_deleted_pairs(require_common_root):
        deleted_set = set(deleted)
        old = [v for v in range(15) if v not in deleted_set]
        new = [15, 16, 17]
        vertices = old + new
        solver = Solver()
        edge_vars = {}

        for i, a in enumerate(vertices):
            for b in vertices[i + 1:]:
                var = Bool(f"e_{gadget_edges}_{deleted[0]}_{deleted[1]}_{a}_{b}")
                edge_vars[a, b] = var
                if a < 15 and b < 15:
                    solver.add(Implies(var, original_edge(a, b)))
                elif a >= 15 and b >= 15:
                    solver.add(var == (gadget_edges == 1 and (a, b) == (15, 16)))

        def edge(a: int, b: int):
            return edge_vars[tuple(sorted((a, b)))]

        for a in vertices:
            solver.add(Sum([If(edge(a, b), 1, 0) for b in vertices if b != a]) == 4)

        for i, a in enumerate(vertices):
            for b in vertices[i + 1:]:
                solver.add(Sum([
                    If(And(edge(a, c), edge(b, c)), 1, 0)
                    for c in vertices if c not in (a, b)
                ]) <= 1)

        multiplicities = {
            v: Sum([If(edge(v, w), 1, 0) for w in new]) for v in old
        }
        if refinement == "non_path_multiplicities":
            count_two = Sum([
                If(multiplicities[v] == 2, 1, 0) for v in old
            ])
            solver.add(Or(
                count_two != 2,
                Or([multiplicities[v] >= 3 for v in old]),
            ))
        elif refinement == "noncanonical_pair_slots":
            def shared(w, z):
                return Or([And(edge(v, w), edge(v, z)) for v in old])

            if gadget_edges == 0:
                shared_count = Sum([
                    If(shared(w, z), 1, 0) for w, z in combinations(new, 2)
                ])
                solver.add(shared_count != 2)
            else:
                # The fixed gadget edge is 15--16.  The observed canonical
                # pattern uses the other two point-pairs as its two unique
                # selector intersections.
                solver.add(Or(
                    shared(15, 16),
                    ~shared(15, 17),
                    ~shared(16, 17),
                ))

        if solver.check() != sat:
            continue

        model = solver.model()
        kept = {
            pair for pair, var in edge_vars.items() if is_true(model.eval(var))
        }
        survivor_edges = {
            pair for pair in EDGES if not deleted_set.intersection(pair)
        }
        removed = sorted(survivor_edges - kept)
        attachments = {
            w: sorted(v for v in old if tuple(sorted((v, w))) in kept)
            for w in new
        }
        expected_removed = 2 - gadget_edges
        assert len(removed) == expected_removed
        return deleted, root, attachments, removed
    return None


def verify(gadget_edges: int, result) -> None:
    deleted, _, attachments, removed = result
    deleted_set = set(deleted)
    old = [v for v in range(15) if v not in deleted_set]
    new = [15, 16, 17]
    vertices = old + new
    final_edges = {
        pair for pair in EDGES
        if not deleted_set.intersection(pair) and pair not in set(removed)
    }
    if gadget_edges == 1:
        final_edges.add((15, 16))
    for w, selector in attachments.items():
        final_edges.update(tuple(sorted((v, w))) for v in selector)

    def adjacent(a: int, b: int) -> bool:
        return tuple(sorted((a, b))) in final_edges

    assert all(sum(adjacent(a, b) for b in vertices if b != a) == 4
               for a in vertices)
    assert all(
        sum(adjacent(a, c) and adjacent(b, c)
            for c in vertices if c not in (a, b)) <= 1
        for i, a in enumerate(vertices) for b in vertices[i + 1:]
    )


def main() -> None:
    for require_common_root in (True, False):
        pair_count = sum(1 for _ in candidate_deleted_pairs(require_common_root))
        pair_class = "common-root" if require_common_root else "no-common-root"
        print(f"independent {pair_class} deletion pairs: {pair_count}")
        for gadget_edges in (0, 1):
            result = solve(gadget_edges, require_common_root)
            label = f"k=2 compensated |E(F)|={gadget_edges}"
            if result is None:
                print(f"{label}: UNSAT")
                continue
            deleted, root, attachments, removed = result
            verify(gadget_edges, result)
            print(f"{label}: SAT D={deleted} common_root={root}")
            print(f"  attachments={attachments}")
            print(f"  removed={removed}")
            print("  direct-verification: VERIFIED")

    print("full-space structural negations:")
    for gadget_edges in (0, 1):
        for refinement in ("non_path_multiplicities", "noncanonical_pair_slots"):
            result = solve(gadget_edges, None, refinement)
            verdict = "SAT" if result is not None else "UNSAT"
            print(f"  |E(F)|={gadget_edges} {refinement}: {verdict}")
            if result is not None:
                deleted, root, attachments, removed = result
                verify(gadget_edges, result)
                print(f"    D={deleted} common_root={root}")
                print(f"    attachments={attachments}")
                print(f"    removed={removed}")


if __name__ == "__main__":
    main()
