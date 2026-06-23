import Mathlib

/-!
# Matrix-Tree (Kirchhoff / Tutte) base cases — Lean regression oracle

Companion to `research/problems/konigsberg-oq-04-oq-01` (S1 ORIENT, PR #24170).

The parent entry `KonigsbergOQ04.lean` **axiomatizes** `best_theorem` because the
BEST formula reduces Eulerian-circuit counting to `arborescenceCount`, and computing
arborescence counts requires the **Matrix-Tree theorem** (the count is a cofactor of
the (directed) Laplacian). The Matrix-Tree theorem is *not* in Mathlib: the keystone
`det (N Nᵀ) = Σ_S det(N_S)²` (Cauchy–Binet) is absent, so a full proof is a large
BUILD, not a one-session task (see the OQ-04-OQ-01 knowledge base).

This file is a small, *concrete* down-payment: it encodes — in Lean — the exact
determinant identities that the S1 numerical certificate (`verify_matrix_tree.py`)
checks by brute force. Each lemma below states that a specific **reduced-Laplacian
cofactor** equals the known spanning-tree / arborescence count. These are the
base-instance "regression oracle" that any eventual `matrix_tree` /
`arborescenceCount = cofactor` theorem must reproduce.

Counts reproduced (cross-checked against the parent file and the Python cert):

| graph | reduced Laplacian | det | meaning |
|-------|-------------------|-----|---------|
| C₃ (directed cycle) | `[[1,-1],[0,1]]` | 1 | `arborescenceCount triDigraph` = 1 |
| K₃ | `[[2,-1],[-1,2]]` | 3 | spanning trees of K₃ (= directed arborescences, root-indep.) |
| C₄ | `[[2,-1,0],[-1,2,-1],[0,-1,2]]` | 4 | spanning trees of C₄ |
| K₄ | `[[3,-1,-1],[-1,3,-1],[-1,-1,3]]` | 16 | spanning trees of K₄ (Cayley 4²) |

NOTE: build-pending. The Docker Lean toolchain was unavailable when this was written,
so the proofs have not been machine-checked; the file is intentionally NOT registered
in `Proofs.lean` until it builds. The determinant facts are elementary and were
hand-verified plus cross-checked by `verify_matrix_tree.py`. The lemma names and tactics
were verified against the pinned Mathlib (`Matrix.det_fin_two_of`, `Matrix.det_fin_three`)
and follow the repo's proven idioms (e.g. `DesarguesTheorem.lean` uses `simp [det_fin_three]`).
-/

namespace KonigsbergMatrixTree

open Matrix

/-- **C₃ directed-cycle arborescence count.**
The out-degree Laplacian of the directed triangle `A→B→C→A` is
`L_out = diag(1,1,1) − A_arc`. Deleting the root row/column leaves `[[1,-1],[0,1]]`,
whose determinant is `1` — matching `arborescenceCount triDigraph w = 1` in
`KonigsbergOQ04.lean`. (Root-independent: deleting any vertex gives `det = 1`.) -/
theorem arborescenceCofactor_C3 :
    (!![(1 : ℤ), -1; 0, 1]).det = 1 := by
  rw [Matrix.det_fin_two_of]; norm_num

/-- **K₃ spanning-tree count (= directed arborescence count).**
The reduced Laplacian after deleting one vertex is `[[2,-1],[-1,2]]`, determinant `3`.
This is both the undirected spanning-tree count of K₃ and (since K₃ is symmetric and
Eulerian) the `arborescenceCount` the parent file records as `3`. -/
theorem spanningTreeCofactor_K3 :
    (!![(2 : ℤ), -1; -1, 2]).det = 3 := by
  rw [Matrix.det_fin_two_of]; norm_num

/-- **C₄ spanning-tree count.** Reduced Laplacian `[[2,-1,0],[-1,2,-1],[0,-1,2]]`,
determinant `4` (a 4-cycle has exactly 4 spanning trees: delete any one of its 4 edges). -/
theorem spanningTreeCofactor_C4 :
    (!![(2 : ℤ), -1, 0; -1, 2, -1; 0, -1, 2]).det = 4 := by
  simp [Matrix.det_fin_three]

/-- **K₄ spanning-tree count.** Reduced Laplacian `[[3,-1,-1],[-1,3,-1],[-1,-1,3]]`,
determinant `16 = 4²`, agreeing with Cayley's formula `n^{n-2}` at `n = 4`. -/
theorem spanningTreeCofactor_K4 :
    (!![(3 : ℤ), -1, -1; -1, 3, -1; -1, -1, 3]).det = 16 := by
  simp [Matrix.det_fin_three]

end KonigsbergMatrixTree
