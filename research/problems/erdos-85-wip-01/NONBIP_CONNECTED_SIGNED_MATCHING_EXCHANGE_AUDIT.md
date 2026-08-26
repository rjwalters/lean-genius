# NONBIP-CONNECTED signed matching-exchange audit

Status: positive bounded calibration under divergence round 73,
26 August 2026.  Evidence for a new mechanism, not a q-generic theorem.

## Exact terminal

Regard the symmetric incidence matrix `A` as the biadjacency matrix of its
bipartite Levi graph.  Its perfect matchings are exactly the permutations
`sigma` with

```text
A(i, sigma(i)) = 1 for every i.
```

The Leibniz formula is

```text
det A = sum_{sigma in Match(A)} sign(sigma).
```

Consequently a fixed-point-free sign-reversing involution on these matchings
proves `det A=0` term by term and closes `NONBIP-CONNECTED` directly.

Two matchings differ in a disjoint union of alternating Levi cycles.  A
switch on one cycle changes permutation sign exactly when its half-length
is even.  C4-freeness excludes half-length two, so the first possible
sign-changing move is an alternating 8-cycle.

This formulation retains actual incidence placement.  The polarity sends a
matching permutation to its inverse because `A` is symmetric; that operation
does not exist for an abstract packing leave or a nonsymmetric incidence
matrix.  A successful theorem must combine this transpose symmetry with an
even alternating-cycle switch.

## Faithful q=4 calibration

`nonbip_connected_signed_matching_exchange_q4.py` uses the exact banked
fixed-point-free q=4 matrix and verifies:

```text
total Levi perfect matchings                  19,972
positive / negative determinant signs     9,986 / 9,986
matchings with an even alternating switch       19,972
```

It then constructs a deterministic sparse subgraph of the full
sign-changing exchange graph.  For each positive matching it samples only
32 negative matchings and retains pairs whose symmetric difference is one
even alternating cycle.  This gives 104,237 exchange edges, and even this
sparse subgraph is connected.  Exact Hopcroft--Karp matching covers all
9,986 vertices on each shore, yielding a verified fixed-point-free
sign-reversing pairing of every determinant term.

The q=4 matrix is already singular and has disconnected deficiency, so this
does not address the `k>=3` or connectedness hypotheses.  Its value is as a
faithful adversarial calibration: unlike the discriminant and mod-2
Pfaffian proposals, the matching-exchange mechanism does not collapse or
fail on the smallest exact self-polar control.

## Remaining theorem

The honest missing statement is now:

> For `q=2^k`, `k>=3`, if `A` is symmetric, loopless, q-regular and C4-free
> on `q^2` vertices and its deficiency graph is connected, then the
> sign-changing single-alternating-cycle exchange graph on `Match(A)` has a
> perfect matching (or admits a canonical sign-reversing involution).

Hall's condition for this exchange graph would suffice.  Merely proving
that every matching has one sign-changing neighbor does not: local
availability need not imply a perfect matching.  The q=4 computation checks
both conditions and deliberately records that distinction.

There is a close but insufficient theorem in the flip-graph literature.
Naddef and Pulleyblank prove that the full flip graph of the vertices of a
0/1 polytope is Hamilton-connected or a hypercube; for the perfect-matching
polytope its edges are all single alternating-cycle flips.  Our graph deletes
every flip whose cycle has odd half-length, because those flips preserve
permutation sign.  In particular the 6-cycle flips supplied by triangles do
not cross the determinant-sign shores.  The theorem therefore does not give
Hall expansion for the required subgraph.  A q=4 sample also shows that the
sign-changing exchange graph is far from regular (observed degrees
`2592..5078`), so the regular-bipartite perfect-matching corollary is not
available either.

References: D. J. Naddef and W. R. Pulleyblank, *Hamiltonicity and
combinatorial polyhedra*, JCTB 31 (1981), 297--312; and *Hamiltonicity in
(0-1)-polyhedra*, JCTB 37 (1984), 41--52.  A modern survey states the
perfect-matching specialization in Section 9.2:
<https://www.combinatorics.org/ojs/index.php/eljc/article/download/ds26/pdf>.

The next proof search should target a q-generic Hall expansion or a
transpose-compatible canonical switch using the self-indexed triangle/
Eulerian-remainder decomposition from the other round-73 submission.  No
finite q=8 census is justified by this calibration.
