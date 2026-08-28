# Size-two circulant coherence audit

## Scope

This note tests the first model that retains the **reuse of the same exterior
two-factor across every endpoint**.  It is deliberately restricted to a
simultaneously circulant model; no theorem currently puts arbitrary size-two
blocks into this normal form.

Let `q=8`, `G=Z/16`, and let the four defect colors be `c,d,e in {0,1,2,3}`.
Write a two-regular circulant block as

`X_cd = sum_{a in A_cd} P_a`,

where `A_cd` is a two-subset of `G`.  Symmetry and the self-indexed diagonal
give

* `A_dc = -A_cd`;
* `A_cc = {s_c,-s_c}` with two distinct elements.

The complete cross-Gram identity is exactly

`disjoint_union_e (A_ce - A_de) = G` for every `c != d`.

Each summand is a four-element difference rectangle.  Thus this single array
encodes the binary products, the `J` tiling, reciprocity, diagonal
self-indexing, and—crucially—the reuse of `A_ce` for every other endpoint.

## Exact result at q=8

The system above is **unsatisfiable**.

The dependency-free verifier
`verify_q8_circulant_coherent_factorization.py` performs an exhaustive search:

1. Equal diagonal types are immediately impossible, since the two endpoint
   rectangles for that color pair collide.
2. Up to color relabeling, it checks all `choose(7,4)=35` distinct diagonal
   spectra.
3. For every exterior entry it retains only two-sets for which the two
   endpoint rectangles already contain eight distinct residues.
4. It backtracks through the six exterior entries using exact minimum
   remaining values.  A branch is cut only when a determined rectangle has an
   internal repeat or overlaps another determined rectangle for the same
   color pair.
5. It exhausts exactly `766168` nodes and finds no completion.

At a leaf, four disjoint four-element rectangles in a group of order sixteen
are automatically the required exact partition.  Hence the pruning predicate
is equivalent to the target equations on complete assignments.

The verifier also calibrates the two-color `q=4`, `G=Z/8` version.  It has 32
raw solutions, so the search is not accidentally proving a false base-case
obstruction.  The obstruction first appears when four colors must reuse their
factors coherently.

Run:

```text
python3 research/problems/erdos-85-wip-01/verify_q8_circulant_coherent_factorization.py
```

Reference output:

```text
q4 raw solutions: 32
q8: UNSAT
diagonal spectra: 35
backtracking nodes: 766168
```

## What this cuts, and what survives

This rules out the full coherent factorization inside the simultaneous cyclic
translation ansatz.  It is strictly stronger than the earlier countermodels:
those realize sparse intertwiner tiles, and even factor each tile locally,
but do not reuse one factor consistently across all triples.

It does **not** prove A-REG-NONBIP.  A general bipartite two-regular block is a
union of cycles and need not share a regular cyclic action with the other
blocks.  The remaining paths are therefore:

* turn the exhaustion into a group-ring/augmentation-adic proof whose local
  ingredient survives without circulant normalization; or
* prove a simultaneous-normalization theorem from the full reciprocal Gram
  system (currently unsupported and likely too strong).

The exact finite obstruction is useful evidence for the first path: the bare
tile and local-factor interfaces have uniform countermodels, whereas the first
model retaining global factor reuse fails sharply at `q=8`.
