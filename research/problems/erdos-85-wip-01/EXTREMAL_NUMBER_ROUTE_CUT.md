# A square-order regular C4-free graph is not extremal: exact-extremal classification cannot reach A-REG

2026-09-08, claude (Fable). Divergence #110 item (2), source-first per goal
#36: read Firke–Kosek–Nash–Williford (arXiv 1201.4912, JCTB 103 (2013)) and
Tait–Timmons (arXiv 1502.02722). Outcome: the EXACT-extremal classification
route is cut uniformly, and the FKNW method has no iterable step; a
near-extremal stability theorem at order q² is not supplied by the two
papers checked and is recorded below as the exact missing lemma, not
claimed impossible. No A-REG node changes.

## The proposed route

An A-REG counterexample is a q-regular C4-free graph G on n = q² vertices,
hence e(G) = q³/2. The Reiman bound ex(n, C4) ≤ (n/4)(1 + √(4n − 3)) gives
ex(q², C4) < q³/2 + q²/4, so G is within n/4 of extremal. The hope was a
stability theorem of the Füredi type ("C4-free with ≥ ex − o(·) edges at
this order ⇒ induced subgraph of a polarity graph"), after which the
ER-surgery no-go already in the ledger (no induced q²-subgraph of ER_q is
q-regular; the pole of the absolute line is forced isolated) would finish.

## Why the FKNW method does not extend

FKNW prove ex(q² + q, C4) ≤ q(q+1)²/2 − q for even q. Their argument is
global, not per-deleted-vertex: Füredi's two-path count
C(n − d, 2) ≥ Σ_{v≠u} C(d(v) − 1, 2), Jensen, and a degree-sequence case
analysis (Lemma 1: Δ ≤ q + 2; Theorem 3: with Δ ≤ q + 1 the bound holds and
equality forces one of two degree sequences; Lemmas 2–6 and Corollary 2 kill
the single possible degree-(q+2) vertex). It works because the surplus over
E₀ at n = q² + q is exactly one edge, and because q + 1 odd forces every
degree-(q+1) vertex to have a neighbour matched to nothing inside its
neighbourhood. There is no structural step that isolates a deleted vertex,
so nothing to iterate q + 1 times down to order q².

## G would not be extremal: exact-extremal classification cannot apply

Tait–Timmons Theorem 1.1: if Π is a projective plane of order q with an
oval and a polarity, then for m ∈ {1, …, q+1} the polarity graph contains a
subgraph on at most m + C(m, 2) vertices with at least
2·C(m, 2) + m⁴/(8q) − O(m⁴/q^{3/2} + m) edges. Their inequality (6): for any
vertex set X of a polarity graph of order q,

    e(G ∖ X) ≥ e(G) − (q + 1)|X| + e(X).

Loops must be handled explicitly, since Theorem 1.1 and (6) count them.
Write e₀ for loopless edge counts and ℓ for loop counts, and let G be the
looped polarity graph of PG(2, q) (loops exactly at the q + 1 absolute
points), so ER_q = G with loops removed and e₀(ER_q) = q(q+1)²/2. A vertex x
has loopless degree q + 1 − [x absolute], hence for any X ⊂ V,

    e₀(ER_q ∖ X) = e₀(ER_q) − Σ_{x∈X} (q + 1 − [x absolute]) + e₀(X)
                 = e₀(ER_q) − (q + 1)|X| + ℓ(X) + e₀(X)
                 = e₀(ER_q) − (q + 1)|X| + e(X),

an exact identity in which e(X) = e₀(X) + ℓ(X) is precisely the looped
count that Theorem 1.1 bounds from below; this is (6) with equality. Take
|X| = q + 1, so that ER_q ∖ X is a C4-free loopless graph on exactly q²
vertices. Then

    e₀(ER_q ∖ X) = q³/2 − (3q + 2)/2 + e(X),

so any X with e(X) > (3q + 2)/2 (loops included) certifies ex(q², C4) > q³/2.
Theorem 1.1 with m ≈ √(2q) gives e(X) ≥ 5q/2 − O(√q); hence

    ex(q², C4) ≥ q³/2 + q − O(√q)      for every prime power q.

Therefore a q-regular C4-free graph on q² vertices, if it existed, would have
strictly fewer edges than the extremal number at its own order (for all
large q, and certifiably for q = 8, 16, 32, 64 below). Exact-extremal
classification theorems — Füredi's equality case at q² + q + 1, FKNW's at
q² + q, and McCuaig's conjecture ("every extremal C4-free graph is an
induced subgraph of an orthogonal polarity graph") — therefore say nothing
about it. What the route would still need is a NEAR-extremal stability
theorem at order q² whose tolerance covers the ACTUAL deficit
ex(q², C4) − q³/2. That deficit is only bracketed: at least q − O(√q) by
the construction above, less than q²/4 by Reiman; it is not known to be
of order q, so a theorem tolerating only ~q might not suffice. Any such
deficit is o(n^{3/2}), so nothing above excludes such a theorem. Neither
paper checked supplies one at this order; it is the exact missing lemma if
this route is ever reopened, and this note makes no claim that it is false. (Tait–Timmons also note ex(q² − 1, C4) ≥
q³/2 − O(√q), so the affine q² − 1 witness with (q³ − q)/2 edges is not
extremal either.)

## Exact certification at binary q

`verify_extremal_number_route_cut.py` (stdlib) builds ER_q over F_q for
q = 8, 16, 32, 64 with the orthogonal polarity x·y = 0 (checking the
q² + q + 1 vertices, the q + 1 absolute points, the degrees q / q + 1 and,
for q ≤ 32, C4-freeness of the final graph), constructs the Tait–Timmons
set X from a conic (S ⊂ {(1, t, t²)}, plus the vertices with exactly two
neighbours in S), pads and 1-swap-improves it to |X| = q + 1, and counts the
remaining edges exactly. As a control, deleting the absolute line leaves
exactly (q³ − q)/2 edges (the affine witness plus its isolated pole).

| q  | e(ER_q) | absolute-line deletion | explicit X, |X| = q+1 | q³/2   | margin |
|----|---------|------------------------|-----------------------|--------|--------|
| 8  | 324     | 252                    | 258                   | 256    | +2     |
| 16 | 2312    | 2040                   | 2062                  | 2048   | +14    |
| 32 | 17424   | 16368                  | 16417                 | 16384  | +33    |
| 64 | 135200  | 131040                 | 131179                | 131072 | +107   |

So ex(q², C4) > q³/2 already at q = 8, with the margin growing roughly
linearly, as the asymptotic predicts. These are lower bounds from one
explicit set each; the true extremal numbers may be larger.

## Scope

This is a cut of the exact-extremal version of one proposed mechanism, with
sources and exact numbers. It does not bear on whether a q-regular C4-free
graph on q² vertices exists; it only shows that such a graph is not an
extremal C4-free graph, so exact extremal-structure results cannot be the
tool. A near-extremal stability statement at order q² covering the true
deficit (bracketed between q − O(√q) and q²/4) was not found in the
papers checked and is left open. The q = 8 computation is an
edge count inside the known graph ER_8, not an order-64 candidate search,
and stays outside the A.5.2 park.
