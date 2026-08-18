# Erdős 85 repair-set stress test — 2026-08-03

## Verified formal increment

Erdos85RepairSet.lean now names HasRepairSet G d, the canonical
delete-one/add-an-adjacent-pair condition reduced to one set.

## Exhaustive finite experiments

A direct exhaustive search tested the sharp 4-regular C4-free witnesses at
orders 15 through 20.

For the connected-pair canonical repair (a set R of size 3, no edges from R
to the deleted vertex's old neighborhood, and R safe after deletion):

- orders 15, 16, 17, 18, 19: no repair;
- order 20: repair exists, for example center 8 and R = {12,13,18}.

A broader nonadjacent-pair variant (R of size 4, no cross-edge restriction)
also fails at orders 15 through 19 and succeeds at order 20.

A further experiment deleting all cross edges before connected-pair
attachment succeeds at orders 17 through 20, but still fails at orders 15
and 16 even when both attachment sets of sizes 3 or 4 are searched
exhaustively.

These are computational findings, not yet kernel-certified theorems.

## Consequence for strategy

Universal local extension of an arbitrarily chosen extremal witness is too
strong: f(15) = f(16) = 5, yet the 15-vertex sharp witness fails all tested
local repair variants. The next-order witness can be globally different.

The formal OneDefectCore reduction correctly asks only for existence of
some core. Future work should focus on spectra of globally constructed
witnesses, especially polarity/projective-plane subgraphs, rather than a
universal surgery theorem.

## Literature checkpoint

Luis Boza, Exact Values and Bounds for Ramsey Numbers of C4 Versus a Star
Graph (arXiv:2409.12770), Lemma 5, shows that whenever the Ramsey parameters
permit a witness, one can choose an edge-minimal witness whose minimum degree
is exactly the target. This suggests formalizing exact-minimum-degree witness
normalization next. The same paper's general inequalities do not resolve the
downward-jump direction in Erdős 85.

