# Knowledge Base: roth-theorem-k3-oq-02-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: discharge the 2 sorries in `proofs/Proofs/RothTriangleRemoval.lean`
(lines 292 and 309) so that `roth_via_triangle_removal` is fully verified,
proving Roth's theorem via the Ruzsa-Szemerédi (1978) construction.

**File status (2026-05-30)**: 465 LOC, 0 axioms, 2 sorries, build-clean
otherwise. Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
Leaf file (0 importers across the gallery).

**The two sorries**:

1. `rs_tc_ap_free_le` (line 292): `triangleCount G univ univ univ ≤
   6 * A.card * N` when A is AP-free. The factor `6 = 3!` is the symmetry
   group of an unordered triangle (`triangleCount` counts ordered triples).

2. `rs_removal_lb` (line 309): if `R ⊆ Edges(G)` covers every triangle of
   the RS graph, then `A.card * N ≤ R.card`. Comes from edge-disjointness
   of the `|A|·N` canonical triangles `{(0,x), (1,x+a), (2,x+2a)}` for
   `(a, x) ∈ A × ZMod N`.

---

## Insights

### Insight 1 — Canonical (a, x) parametrization is the key.

The composition `triangle_yields_ap_triple` → `ap_free_forces_equal` shows
that *every* triangle in the AP-free RS graph has the shape
`{xVert x, yVert (x+a), zVert (x+2a)}` for a unique `(a, x) ∈ A × ZMod N`.
Both sorries reduce to counting / injecting over this parametrization.

### Insight 2 — `triangleCount` counts ORDERED triples; bound's factor 6 is `3!`.

`triangleCount G A B C` is defined as the cardinality of the filter
`(A ×ˢ B ×ˢ C).filter (fun (u, v, w) => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)`.
With `A = B = C = univ`, each unordered triangle is counted 6 times (one
for each ordering of its 3 vertices). Hence the bound `6 * |A| * N` =
6 × (number of unordered canonical triangles).

### Insight 3 — The XY edge-uniqueness lemma is in place; YZ and XZ analogues are MISSING.

`xy_edge_unique_triangle` (line 228) proves: given AP-free A, an XY edge
(x, y) extends to a triangle in at most one way (unique z). The analogous
statements for YZ and XZ edges are not in the file but are needed for the
sorry #2 attack (edge-disjointness of canonical triangles). They should
follow by the same `triangle_yields_ap_triple` + `ap_free_forces_equal`
chain — direct copy/adaptation of the XY proof.

### Insight 4 — `RothTriangleRemoval.lean` is a LEAF file (0 importers).

```bash
$ grep -rln 'import Proofs.RothTriangleRemoval' proofs/Proofs/ | wc -l
0
```

Sub-ACTs cannot cascade into other gallery files. This contrasts with the
non-leaf-parent risk of e.g. `lagrange-four-squares-oq-01-oq-02` (where
`ThreeSquares.lean` has 4 importers). Sub-ACTs S3 / S4 / S5 can each merge
independently without affecting other slugs.

### Insight 5 — `ap_free_min_removal` already does 80% of the sorry-#2 work.

`ap_free_min_removal` (line 317) is proved (0 sorry). It establishes:
for each `(a, x) ∈ A × ZMod N`, R contains at least one of the 6 directed
pairs of the canonical triangle. Sorry #2 only needs the *quantitative*
consequence: those |A|·N choices are distinct elements of R.

### Insight 6 — Classical choice on a 6-way `Or` is the obvious tool for the (a,x) → R map.

`ap_free_min_removal` returns a 6-way disjunction (`p ∈ R ∨ p' ∈ R ∨ ...`).
For the injection, Classical choice gives a function
`A × ZMod N → RSVertex × RSVertex` landing in R. Injectivity then reduces
to: different `(a, x)` yield different chosen pairs, which uses the YZ/XZ
edge-uniqueness helpers (S3).

---

## Dead Ends

None observed yet (S2 OBSERVE only; no Lean attempts).

### Approaches NOT to take

- **Don't** try to count triangles directly via `Finset.sum` over vertex
  triples. The filter-then-card approach via embedding is cleaner.
- **Don't** introduce a new triangle structure type. The existing
  `APTriple` and the canonical `(a, x)` parametrization are sufficient.
- **Don't** try to discharge both sorries in a single PR. The 3-sub-ACT
  split (S3 helpers → S4 sorry #1 → S5 sorry #2) keeps each piece below
  the build-time risk threshold and matches the agent-feedback pattern
  for scoped progress.

---

## References

- Ruzsa & Szemerédi (1978), *Triple systems with no six points carrying
  three triangles*, Coll. Math. Soc. J. Bolyai 18, 939–945. The graph
  construction that gives `r_3(N) = o(N)` via the triangle removal lemma.
- Tao & Vu, *Additive Combinatorics*, Cambridge 2006, §10.2. Modern
  exposition of the same construction.
- `src/data/proofs/roth-theorem-k3-oq-02/meta.json` — gallery metadata
  (status: `formalized`, badge: `wip`, sorries: 2, axioms: 0).
- `proofs/Proofs/RothTheorem.lean` — alternative Fourier-analytic proof
  (already 0 sorry, used in `roth_proofs_agree` to relate the two routes).
