/-
# Erdős Problem #634 (OQ-01) — The square reptiling for ALL k

Source: open question `erdos-634-medial-congruence-oq-01`, the generalisation of
the base entry `Proofs.Erdos634MedialCongruence` (the medial `k = 2` subdivision)
to arbitrary `k`.

## The generalisation

The base entry proves the `k = 2` case: joining the midpoints of a triangle's
sides cuts it into `4 = 2²` mutually congruent half-scale copies.  This file
proves the **full square reptiling** for every number of subdivisions `k`:
dividing each side of triangle `A B C` into `k` equal parts and drawing the grid
of parallels produces `k²` congruent `(1/k)`-scale copies of `A B C`.

Concretely, let `P i j = A + (i/k)·(B-A) + (j/k)·(C-A)` be the triangular grid.
The sub-triangles come in two orientations:

  * **upward** copies `Up i j = (P i j, P (i+1) j, P i (j+1))` — same orientation
    as `A B C`, indexed by `i + j ≤ k-1`;
  * **downward** copies `Down i j = (P (i+1) (j+1), P i (j+1), P (i+1) j)` —
    reversed orientation, indexed by `i + j ≤ k-2`.

## What is proved (0 axioms, fully verified)

Working in an arbitrary real normed space `V`:

  * `cong_U0_Up`   : every upward piece is congruent to the base copy `U0`,
    witnessed by the **translation** by `(i/k)(B-A) + (j/k)(C-A)`;
  * `cong_U0_Down` : every downward piece is congruent to `U0`, witnessed by the
    **point reflection** `x ↦ (A + P(i+1,j+1)) - x` (a 180° rotation);
  * `cong_Up_Up`, `cong_Down_Down`, `cong_Up_Down` : hence *all* pieces are
    pairwise congruent (`TriCongruent` is an equivalence relation, from the base
    entry);
  * `U0_sides_scaled` : the base copy has side lengths exactly `dist A B / k`,
    `dist B C / k`, `dist C A / k` — a genuine `1/k`-scale copy;
  * `card_pieces` : the combinatorial accounting — a `(k+1)`-subdivision has
    `(k+1)²` index slots, split as the triangular numbers `T(k+1) + T(k)`
    (upward + downward).  This is the `k²` count, proved over all `k`.

The `k = 2` base case is recovered: `card_pieces 1` gives `3 + 1 = 4 = 2²`
(three upward medial pieces, one central downward piece), matching
`Erdos634MedialCongruence.medial_four_congruent`.

As in the base entry we capture the congruence of the pieces (the combinatorial
heart) unconditionally and axiom-free; the analytic covering/disjointness of the
tiling is not formalised.

Tags: geometry, erdos, dissection, congruence, isometry, reptile, reptiling
-/

import Mathlib
import Proofs.Erdos634MedialCongruence

set_option linter.unusedSectionVars false

open Erdos634MedialCongruence

namespace Erdos634MedialCongruenceOQ01

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Part I: The `k`-subdivision grid -/

variable (A B C : V) (k : ℕ)

/-- Grid point of the `k`-subdivision: `P i j = A + (i/k)(B-A) + (j/k)(C-A)`. -/
noncomputable def P (i j : ℕ) : V :=
  A + ((i : ℝ) / k) • (B - A) + ((j : ℝ) / k) • (C - A)

/-- The base scaled triangle (corner at `A`, side `1/k`). -/
noncomputable def U0 : V × V × V := (P A B C k 0 0, P A B C k 1 0, P A B C k 0 1)

/-- Upward sub-triangle with lower-left grid index `(i, j)`. -/
noncomputable def Up (i j : ℕ) : V × V × V :=
  (P A B C k i j, P A B C k (i + 1) j, P A B C k i (j + 1))

/-- Downward sub-triangle with index `(i, j)`. -/
noncomputable def Down (i j : ℕ) : V × V × V :=
  (P A B C k (i + 1) (j + 1), P A B C k i (j + 1), P A B C k (i + 1) j)

/-! ## Part II: Congruence of every sub-triangle to the base copy -/

/-- Every upward sub-triangle is congruent to the base copy `U0`, via the
translation by `(i/k)(B-A) + (j/k)(C-A)`. -/
theorem cong_U0_Up (i j : ℕ) : TriCongruent (U0 A B C k) (Up A B C k i j) := by
  refine ⟨IsometryEquiv.constVAdd
      (((i : ℝ) / k) • (B - A) + ((j : ℝ) / k) • (C - A)), ?_, ?_, ?_⟩ <;>
    simp only [U0, Up, P, constVAdd_apply'] <;> push_cast <;> module

/-- Every downward sub-triangle is congruent to the base copy `U0`, via the
point reflection about `A + P(i+1, j+1)` (a 180° rotation). -/
theorem cong_U0_Down (i j : ℕ) : TriCongruent (U0 A B C k) (Down A B C k i j) := by
  refine ⟨pointRefl (A + P A B C k (i + 1) (j + 1)), ?_, ?_, ?_⟩ <;>
    simp only [U0, Down, P, pointRefl_apply] <;> push_cast <;> module

/-- Any two upward sub-triangles are congruent. -/
theorem cong_Up_Up (i j i' j' : ℕ) :
    TriCongruent (Up A B C k i j) (Up A B C k i' j') :=
  (cong_U0_Up A B C k i j).symm.trans (cong_U0_Up A B C k i' j')

/-- Any two downward sub-triangles are congruent. -/
theorem cong_Down_Down (i j i' j' : ℕ) :
    TriCongruent (Down A B C k i j) (Down A B C k i' j') :=
  (cong_U0_Down A B C k i j).symm.trans (cong_U0_Down A B C k i' j')

/-- An upward and a downward sub-triangle are congruent. -/
theorem cong_Up_Down (i j i' j' : ℕ) :
    TriCongruent (Up A B C k i j) (Down A B C k i' j') :=
  (cong_U0_Up A B C k i j).symm.trans (cong_U0_Down A B C k i' j')

/-! ## Part III: The pieces are `1/k`-scale copies -/

private theorem norm_invk_smul (v : V) :
    ‖((k : ℝ))⁻¹ • v‖ = ‖v‖ / (k : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg k),
    div_eq_inv_mul]

/-- The base copy `U0` has side lengths exactly `1/k` of the original triangle
`A B C`, exhibiting the dissection as `k²` congruent `(1/k)`-scale copies. -/
theorem U0_sides_scaled :
    dist (U0 A B C k).1 (U0 A B C k).2.1 = dist A B / k ∧
    dist (U0 A B C k).2.1 (U0 A B C k).2.2 = dist B C / k ∧
    dist (U0 A B C k).2.2 (U0 A B C k).1 = dist C A / k := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_eq_norm,
      show (U0 A B C k).1 - (U0 A B C k).2.1 = ((k : ℝ))⁻¹ • (A - B) from by
        simp only [U0, P]; push_cast; module,
      norm_invk_smul, ← dist_eq_norm]
  · rw [dist_eq_norm,
      show (U0 A B C k).2.1 - (U0 A B C k).2.2 = ((k : ℝ))⁻¹ • (B - C) from by
        simp only [U0, P]; push_cast; module,
      norm_invk_smul, ← dist_eq_norm]
  · rw [dist_eq_norm,
      show (U0 A B C k).2.2 - (U0 A B C k).1 = ((k : ℝ))⁻¹ • (C - A) from by
        simp only [U0, P]; push_cast; module,
      norm_invk_smul, ← dist_eq_norm]

/-! ## Part IV: There are exactly `k²` pieces -/

/-- Index set `{(i, j) : i + j < n}` of grid cells, realised as the disjoint
union of the antidiagonals `i + j = s` for `s < n`. -/
def triIdx (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).biUnion (fun s => Finset.antidiagonal s)

theorem card_triIdx (n : ℕ) :
    (triIdx n).card = ∑ s ∈ Finset.range n, (s + 1) := by
  rw [triIdx, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun s _ => Finset.Nat.card_antidiagonal s)
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 (fun p hp hp' => ?_)
    rw [Finset.mem_antidiagonal] at hp hp'
    exact hxy (hp.symm.trans hp')

private theorem sum_range_succ_mul_two (n : ℕ) :
    (∑ s ∈ Finset.range n, (s + 1)) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

/-- **The `k²` count.** A `(k+1)`-subdivision of the triangle has `(k+1)²`
sub-triangle index slots, split as the triangular numbers `T(k+1)` upward and
`T(k)` downward pieces.  (`k = 1` gives `3 + 1 = 4 = 2²`, the medial base case.) -/
theorem card_pieces (m : ℕ) :
    (triIdx (m + 1)).card + (triIdx m).card = (m + 1) ^ 2 := by
  have h : ((triIdx (m + 1)).card + (triIdx m).card) * 2 = (m + 1) ^ 2 * 2 := by
    rw [add_mul, card_triIdx, card_triIdx, sum_range_succ_mul_two,
      sum_range_succ_mul_two]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

/-- Cross-check: the `k = 2` medial subdivision (the base entry) has
`3 + 1 = 4 = 2²` pieces — three upward, one central downward. -/
example : (triIdx 2).card + (triIdx 1).card = 4 := card_pieces 1

end Erdos634MedialCongruenceOQ01
