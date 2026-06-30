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

## Insight 5 — bearer re-survey at Mathlib **v4.26.0** (2026-06-27); the incidence in Mathlib is the WRONG sign
Re-ran the bearer survey against the project's pinned Mathlib (`v4.26.0`,
`proofs/.lake/packages/mathlib`). The 2026-06-14 gap **persists unchanged**:
- **Cauchy-Binet**: still ABSENT (`det_mul_submatrix`, `cauchyBinet`, `sum_det` = 0 hits).
- **Kirchhoff / Matrix-Tree**: still ABSENT (only tangential hits — `Quiver/Arborescence`,
  `SimpleGraph/Acyclic` (`IsAcyclic`/`IsTree` *predicates*, no spanning-tree **count**),
  `FreeGroup/NielsenSchreier`).
- **`SimpleGraph.lapMatrix`**: still only `det_lapMatrix_eq_zero` — no cofactor/tree theorem.

**New, sharper finding (refines M1a):** Mathlib's `SimpleGraph.incMatrix` is the
**UNSIGNED** 0/1 incidence matrix. Its product theorem `incMatrix_mul_transpose`
(+ `incMatrix_mul_transpose_diag`) therefore gives `N Nᵀ = D + A` — the **signless**
Laplacian — *not* the `B Bᵀ = D − A = lapMatrix` identity the classical Matrix-Tree
proof rides on. So M1a is really **two** sub-gaps, not one:
  (M1a-i) define an **oriented** incidence matrix `B` (entries in {−1,0,+1} per an edge
          orientation) and prove `B Bᵀ = G.lapMatrix` — currently NO oriented incidence
          object upstream; and
  (M1a-ii) Cauchy-Binet `det(B_S B_Sᵀ) = Σ …` over that `B`.
This means even the *substrate* for the undirected proof must be built first; the
existing unsigned `incMatrix` cannot be reused directly. (M2's directed Laplacian gap
is unaffected.)

## Insight 6 — M1a-i is now PROVED in Lean (S4, 2026-06-28, 0-axiom)
The oriented-incidence ⇒ Laplacian substrate from Insight 5 is no longer just a
documented gap — it is a machine-checked theorem in
`proofs/Proofs/KonigsbergOQ04OQ01MatrixTree.lean` (registered, host-verified; axioms
`propext/Classical.choice/Quot.sound` only — `decide` is kernel, not `native_decide`):
- `incidence head tail : Matrix V E ℤ` — oriented incidence of a loopless multigraph
  presented by `head tail : E → V` (column `e` = `+1` at head, `−1` at tail). This is
  the **signed** object Mathlib lacks (`incMatrix` is unsigned → `N Nᵀ = D + A`, wrong
  sign; see Insight 5).
- `incidence_mul_transpose : B Bᵀ = lap` where `lap` is the integer Laplacian `D − A`
  (`deg` on the diagonal, `−adjc` = negative edge-multiplicity off-diagonal). Proved
  entrywise: diagonal via `(a−b)² = a+b` under looplessness (the two indicators never
  overlap); off-diagonal via the four-way indicator case split where only the cross
  terms `±1` survive.
- `k3_incidence_mul_transpose` — concrete bridge: K₃'s oriented incidence (edges
  `0→1,1→2,0→2`) gives `B Bᵀ = [[2,−1,−1],[−1,2,−1],[−1,−1,2]]` by `decide`, whose
  reduced `(0,0)`-cofactor is exactly the `spanningTreeCofactor_K3` oracle (det 3).

This closes **M1a-i** (the oriented-incidence substrate — Mathlib's own `IncMatrix.lean:42`
TODO). It does NOT discharge the parent axiom: the remaining undirected gap is **M1a-ii
Cauchy–Binet** (`det(B_S B_Sᵀ)=…`, still absent upstream); the directed BEST path still
needs **M2** (Tutte out-Laplacian cofactor = `arborescenceCount`).

## Open threads
- **M1a-ii (Cauchy–Binet)** is now the sole blocker on the undirected Matrix-Tree path:
  with `incidence_mul_transpose` proved, M1 reduces to `det(reduced L) = Σ_{S spanning tree}
  det(B_S)²` + `det(B_S)²∈{0,1}`. Does a Cauchy-Binet PR exist in the Mathlib queue? (If
  it lands, M1 collapses to cofactor bookkeeping over the now-available `incidence`.)
- Bridge `deg`/`adjc`/`lap` to Mathlib's `SimpleGraph.degree`/`adjMatrix`/`lapMatrix` by
  instantiating `E` as an oriented edge set (the Sym2 plumbing deferred this session) — would
  let `incidence_mul_transpose` land `SimpleGraph.lapMatrix` directly.
- Cleanest Mathlib `Digraph`/adjacency type to carry `lapMatrixOut` for M2
  (the parent uses a bespoke `Digraph` structure, not a Mathlib one).
- Could `B` be defined as a signed reweighting of `incMatrix` (reuse its `mul_transpose`
  bookkeeping) rather than from scratch? Worth a build-time experiment.

## Links
- Parent: [[konigsberg-oq-04]] (BEST theorem; axiomatized arborescence count).
- Verification vein: see make-ephemeral-verification-durable cert pattern.
