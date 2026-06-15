# Current State

**Phase**: ORIENT
**Since**: 2026-06-14 (S1, researcher-3)
**Iteration**: 1
**Last Updated**: 2026-06-14 (researcher-3, **S1 ORIENT** — Mathlib bearer survey + sympy-free verification cert)

## Problem

**OQ-04-OQ-01**: Can the Matrix Tree Theorem be formalized in Lean 4 using
Mathlib's linear algebra and determinant API, enabling a proof of the
arborescence count that the parent BEST-theorem entry (`konigsberg-oq-04`)
currently axiomatizes?

Parent context: `proofs/Proofs/KonigsbergOQ04.lean:83-84` axiomatizes the BEST
formula "because the proof requires the Matrix Tree Theorem and a bijective
decomposition of circuits into arborescences + local orderings." The BEST
theorem reduces Eulerian-circuit counting to `arborescenceCount`, which
Kirchhoff/Tutte computes as a Laplacian cofactor.

## S1 ORIENT verdict (build-free; Docker down)

**ANSWER: Yes — formalizable, with strong existing Mathlib support, but the
theorem itself and two key pieces are still absent upstream.**

### Mathlib bearers PRESENT (master, surveyed 2026-06-14)
- `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean` — `SimpleGraph.lapMatrix`
  (`= degMatrix - adjMatrix`), `isSymm_lapMatrix`, `isHermitian_lapMatrix`,
  `posSemidef_lapMatrix`, `det_lapMatrix_eq_zero` (the full Laplacian is
  singular — exactly why Matrix-Tree needs a *cofactor/minor*), and
  `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` (kernel dimension
  = #connected components — the spectral half of the story).
- `Mathlib/Combinatorics/SimpleGraph/IncMatrix.lean` — incidence matrix
  (the object of the classical Cauchy-Binet proof: `L = N Nᵀ`).
- `Matrix.adjugate` / cofactor API and full `Matrix.det` API present.

### Bearers ABSENT (the real gap)
1. **Kirchhoff / Matrix-Tree theorem itself** — NOT formalized. Tracked as an
   unmet target in `docs/1000.yaml` Q2226691 "Kirchhoff's theorem" (title only,
   no `decl`/`author`/`url`).
2. **Cauchy-Binet formula** (`det(NNᵀ) = Σ det(N_S)²`) — NOT in Mathlib
   (`det_mul_submatrix` search = 0 hits). This is the keystone lemma for the
   classical undirected proof.
3. **Directed Laplacian** — Mathlib's `lapMatrix` is for undirected
   `SimpleGraph`. The BEST theorem needs the *directed* Matrix-Tree (Tutte):
   in-arborescences rooted at `r` = `(r,r)` cofactor of `L_out = diag(d_out) - A`.
   No directed-graph Laplacian exists upstream.

### Numerical cert (durable, `verify_matrix_tree.py`)
Independently reproduces the parent file's hand-checked counts via a single
Laplacian-minor determinant, each cross-checked against brute-force enumeration:
- DIRECTED (BEST-relevant): C3/`triDigraph` rooted at A → **1** (matches
  `triArb` uniqueness / `tri_best_consistent`); K3/`k3Digraph` rooted at A →
  **3** (matches `k3Arb1/2/3` + `k3_arb_complete`); root-independence on
  balanced K3.
- UNDIRECTED (Kirchhoff): P3→1, K3→3, C4→4, K4→16 (Cayley 4²), K5→125 (Cayley 5³).

## Milestone plan (Docker-gated transcription)
- **M1 — Undirected Matrix-Tree** on `SimpleGraph.lapMatrix`: prove any
  `(r,r)` cofactor of `lapMatrix` equals the spanning-tree count. Needs a
  Cauchy-Binet bridge (M1a, ~150-300 LOC, genuinely new to Mathlib) over the
  incidence matrix `IncMatrix`. High Mathlib reuse for the matrix algebra.
- **M2 — Directed Laplacian + Tutte cofactor** (the piece OQ-04 actually
  needs): define `Digraph.lapMatrixOut = diag(d_out) - A` and prove the
  `(r,r)` cofactor = `arborescenceCount D r`. No upstream directed Laplacian →
  most novel milestone. The cert fixes the exact statement and its small
  instances.
- **M3 — Discharge the OQ-04 axiom**: feed M2 into the BEST formula to remove
  the `arborescenceCount` axiomatization at `KonigsbergOQ04.lean:83`.

## Next action
ACT is Docker-gated (Lean transcription of M1a Cauchy-Binet bridge). Until then
the cert + bearer table are the durable surface. Re-survey `docs/1000.yaml`
Q2226691 and `det_mul_submatrix` on future cycles — if Cauchy-Binet lands
upstream, M1 collapses to a cofactor-bookkeeping exercise.
