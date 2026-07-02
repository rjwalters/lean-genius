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

/-! ## M1a-i: the oriented-incidence ⇒ Laplacian identity (`B Bᵀ = D − A`)

The base cases above are concrete determinant oracles. The first *general* milestone
toward Matrix-Tree is the substrate identity that the classical (undirected) proof
rides on: for the oriented incidence matrix `B` of a loopless multigraph, `B Bᵀ` is
the graph Laplacian `D − A`.

This is precisely the gap flagged in the OQ-04-OQ-01 knowledge base (Insight 5) and,
independently, in Mathlib itself: `Mathlib/Combinatorics/SimpleGraph/IncMatrix.lean`
lists as future-work TODOs (lines 41–42)

  * "Define the oriented incidence matrices for oriented graphs."
  * "Define the graph Laplacian of a simple graph using the oriented incidence matrix."

Mathlib's existing `incMatrix` is the *unsigned* 0/1 incidence matrix, for which
`N Nᵀ = D + A` (the *signless* Laplacian) — the wrong sign for Matrix-Tree. So the
oriented object below cannot be obtained from `incMatrix` directly; it is built here
from `head`/`tail` functions (a multigraph presentation: each edge `e` is an oriented
pair `tail e → head e`).

What this milestone does **not** do: it does not discharge the parent
`konigsberg-oq-04` axiom. That still needs Cauchy–Binet (`det (B_S B_Sᵀ) = …`, M1a-ii),
which remains absent upstream, plus the directed Tutte cofactor (M2). This is the
verified substrate those build on. -/

section IncidenceLaplacian

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Oriented incidence matrix of a multigraph given by `head`/`tail`: column `e` has
`+1` at its head and `-1` at its tail. -/
def incidence (head tail : E → V) : Matrix V E ℤ := fun i e =>
  (if i = head e then 1 else 0) - (if i = tail e then 1 else 0)

/-- Degree of `i`: the number of edges incident to `i`. -/
def deg (head tail : E → V) (i : V) : ℤ :=
  (Finset.univ.filter (fun e => i = head e ∨ i = tail e)).card

/-- Edge multiplicity between `i` and `j` (either orientation). -/
def adjc (head tail : E → V) (i j : V) : ℤ :=
  (Finset.univ.filter
    (fun e => (i = head e ∧ j = tail e) ∨ (j = head e ∧ i = tail e))).card

/-- The integer Laplacian `D − A` of the multigraph: degree on the diagonal, negative
edge-multiplicity off-diagonal. -/
def lap (head tail : E → V) : Matrix V V ℤ := fun i j =>
  if i = j then deg head tail i else - adjc head tail i j

omit [Fintype V] [DecidableEq E] in
/-- Diagonal of `B Bᵀ` is the degree (loopless ⇒ the two indicators never overlap, so
`(a − b)² = a + b`). -/
theorem incidence_mul_transpose_diag
    (head tail : E → V) (hloop : ∀ e, head e ≠ tail e) (i : V) :
    (incidence head tail * (incidence head tail)ᵀ) i i = deg head tail i := by
  simp only [Matrix.mul_apply, incidence, Matrix.transpose_apply, deg]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  by_cases hh : i = head e <;> by_cases ht : i = tail e
  · exact absurd (hh.symm.trans ht) (hloop e)
  all_goals simp [hh, ht, hloop e, (hloop e).symm]

omit [Fintype V] [DecidableEq E] in
/-- Off-diagonal `(i,j)` of `B Bᵀ` is `−` the edge multiplicity between `i` and `j`
(`i ≠ j` ⇒ only the cross terms `±1` survive). -/
theorem incidence_mul_transpose_offdiag
    (head tail : E → V) (i j : V) (hij : i ≠ j) :
    (incidence head tail * (incidence head tail)ᵀ) i j = - adjc head tail i j := by
  simp only [Matrix.mul_apply, incidence, Matrix.transpose_apply, adjc]
  rw [Finset.card_filter]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi_h : i = head e <;> by_cases hi_t : i = tail e <;>
    by_cases hj_h : j = head e <;> by_cases hj_t : j = tail e <;>
    simp_all

omit [Fintype V] [DecidableEq E] in
/-- **Oriented incidence ⇒ Laplacian** (M1a-i). For a loopless multigraph,
`B Bᵀ = D − A`. -/
theorem incidence_mul_transpose (head tail : E → V) (hloop : ∀ e, head e ≠ tail e) :
    incidence head tail * (incidence head tail)ᵀ = lap head tail := by
  ext i j
  by_cases h : i = j
  · subst h; simp [lap, incidence_mul_transpose_diag head tail hloop]
  · simp [lap, h, incidence_mul_transpose_offdiag head tail i j h]

/-! ### M1a-i′: the reduced Laplacian is a Gram matrix (Cauchy–Binet precondition)

The Matrix-Tree proof does not take the determinant of the *full* Laplacian `lap = B Bᵀ`
(that determinant is `0` — every row sums to zero, cf. Mathlib's `det_lapMatrix_eq_zero`).
It deletes the root row/column and takes the determinant of the resulting **reduced**
Laplacian.  The lemma below records the exact object Cauchy–Binet is then applied to: the
reduced Laplacian is itself the Gram matrix `B_f (B_f)ᵀ` of the *reduced incidence* `B_f`
(the incidence matrix with the deleted rows removed, i.e. `incidence` restricted along any
reindexing `f : V' → V` of the retained vertices).

This is a pure consequence of M1a-i (`incidence_mul_transpose`) and the submatrix/product
algebra (`Matrix.submatrix_mul`, `Matrix.transpose_submatrix`), for an *arbitrary* index map
`f` — in particular the classical "delete the root" specialization `f : {v // v ≠ r} ↪ V`.
It reduces the remaining Matrix-Tree gap to the two genuinely-absent pieces: Cauchy–Binet
`det (B_f B_fᵀ) = Σ_S det (B_f · col S)²` (M1a-ii) and the unimodularity `det ∈ {0, ±1}`
that identifies the nonzero terms with spanning trees. -/

omit [Fintype V] [DecidableEq E] in
/-- **Reduced Laplacian = Gram matrix of the reduced incidence.** For any reindexing
`f : V' → V` of a subset of vertices, the Laplacian restricted to those vertices equals
`B_f (B_f)ᵀ`, where `B_f = (incidence head tail).submatrix f id` keeps only the `f`-rows.
Applied with `f` the inclusion of the non-root vertices, the left side is the reduced
Laplacian whose determinant is the spanning-tree / arborescence count. -/
theorem reducedLaplacian_eq_gram
    (head tail : E → V) (hloop : ∀ e, head e ≠ tail e)
    {V' : Type*} (f : V' → V) :
    (lap head tail).submatrix f f
      = (incidence head tail).submatrix f id *
        ((incidence head tail).submatrix f id)ᵀ := by
  rw [← incidence_mul_transpose head tail hloop,
    Matrix.submatrix_mul (incidence head tail) (incidence head tail)ᵀ f id f
      Function.bijective_id,
    Matrix.transpose_submatrix]

/-! ### Concrete K₃ bridge

Realizes the general identity on a base case: the oriented incidence of K₃ (edges
`0→1`, `1→2`, `0→2`) satisfies `B Bᵀ = ` the full K₃ Laplacian, whose reduced
`(0,0)`-cofactor `[[2,-1],[-1,2]]` has determinant `3` — exactly
`spanningTreeCofactor_K3`. This closes the loop from the incidence substrate to the
base-case determinant oracle. -/

/-- K₃ edges as `head`/`tail` over `Fin 3`: `0→1`, `1→2`, `0→2`. -/
def k3head : Fin 3 → Fin 3 := ![1, 2, 2]
/-- K₃ edge tails (companion to `k3head`). -/
def k3tail : Fin 3 → Fin 3 := ![0, 1, 0]

theorem k3_loopless : ∀ e, k3head e ≠ k3tail e := by decide

/-- The oriented incidence of K₃ realizes the full K₃ Laplacian. -/
theorem k3_incidence_mul_transpose :
    incidence k3head k3tail * (incidence k3head k3tail)ᵀ =
      !![(2 : ℤ), -1, -1; -1, 2, -1; -1, -1, 2] := by
  rw [incidence_mul_transpose k3head k3tail k3_loopless]
  decide

end IncidenceLaplacian

end KonigsbergMatrixTree
