# Knowledge: konigsberg-oq-04-oq-01 (Matrix-Tree formalizability)

## Problem framing
Parent `konigsberg-oq-04` (BEST theorem) axiomatizes `arborescenceCount`
because Kirchhoff/Tutte's Matrix-Tree theorem is unproved in the project.
OQ-04-OQ-01 asks whether Mathlib's linear-algebra/determinant API suffices to
formalize Matrix-Tree and discharge that axiom.

## Insight 1 — The two Matrix-Tree theorems, and which one OQ-04 needs
- **Undirected (Kirchhoff)**: `τ(G)` = any cofactor of `L = D − A`. Closest to
  Mathlib's existing `SimpleGraph.lapMatrix`.
- **Directed (Tutte)**: #in-arborescences rooted at `r` = `(r,r)` cofactor of
  `L_out = diag(d_out) − A`, where `A[u][v] = #arcs u→v`, `d_out(v)=Σ_w A[v][w]`.
  **This is the version the BEST theorem (OQ-04) actually consumes** —
  `arborescenceCount D w` over a `Digraph`, not a `SimpleGraph`.
- Convention check vs the Lean file: `Arborescence` (KonigsbergOQ04.lean:49)
  is an *in-tree* (every vertex has a directed path TO the root via `parent`),
  so the matching matrix is `L_out` (out-degree Laplacian), `(r,r)` minor.

## Insight 2 — Mathlib bearer map (surveyed master, 2026-06-14)
PRESENT:
- `SimpleGraph.lapMatrix` and full API in
  `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`. Notably
  `det_lapMatrix_eq_zero` (full Laplacian singular ⇒ must use a cofactor) and
  `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` (ker dim = #comps).
- `SimpleGraph.incMatrix` (`IncMatrix.lean`) — substrate for the `L = N Nᵀ`
  identity underlying the Cauchy-Binet proof.
- `Matrix.adjugate`/cofactor + `Matrix.det` API.

ABSENT (the gap that makes OQ-04-OQ-01 nontrivial):
- Kirchhoff's theorem itself — `docs/1000.yaml` Q2226691 lists it as an
  *unmet* target (title only).
- Cauchy-Binet (`det(NNᵀ)=Σ_S det(N_S)²`) — 0 hits; keystone for the classical
  undirected proof.
- Directed-graph Laplacian — none upstream; required for M2/BEST.

## Insight 3 — Numerical anchor (durable, `verify_matrix_tree.py`)
A single Laplacian-minor determinant reproduces every count the parent file
asserts by hand, brute-force-cross-checked:
- DIRECTED: C3→1, K3→3 (= the Lean `arborescenceCount`s), root-independent on K3.
- UNDIRECTED: P3→1, K3→3, C4→4, K4→16, K5→125 (Cayley `n^{n-2}`).
This fixes the exact theorem statement and its base instances, so the eventual
Lean transcription has a regression oracle.

## Insight 4 — base-case oracle now in Lean (S2, build-pending)
The Insight-3 anchors are now machine-checkable Lean lemmas in
`proofs/Proofs/KonigsbergOQ04OQ01MatrixTree.lean` (UNREGISTERED, build-pending):
`arborescenceCofactor_C3 = 1`, `spanningTreeCofactor_K3 = 3`,
`spanningTreeCofactor_C4 = 4`, `spanningTreeCofactor_K4 = 16` — each a concrete
reduced-Laplacian `Matrix.det` over ℤ, closed by `Matrix.det_fin_two/three` + `norm_num`.
This is the down-payment that converts the Python cert into Lean; the full M1/M2
theorems must reproduce these exact cofactor values. Note this does NOT touch the
parent axiom — Cauchy–Binet (M1a) is still the blocking gap.

## Open threads
- Does a Cauchy-Binet PR exist in the Mathlib queue? (If it lands, M1 trivializes.)
- Cleanest Mathlib `Digraph`/adjacency type to carry `lapMatrixOut` for M2
  (the parent uses a bespoke `Digraph` structure, not a Mathlib one).

## Links
- Parent: [[konigsberg-oq-04]] (BEST theorem; axiomatized arborescence count).
- Verification vein: see make-ephemeral-verification-durable cert pattern.
