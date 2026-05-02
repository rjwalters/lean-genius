/-
  Aristotle targets for Erdős Problem #634: Triangle Dissection into Congruent Pieces.
  This companion imports Proofs.Erdos634Problem and operates in namespace Erdos634
  so any proof here directly closes a sorry in the main file.

  The legacy Erdos634Aristotle.lean re-declares Triangle, Congruent, Dissection, etc.
  in a separate Erdos634Aristotle namespace without importing the main file. Aristotle's
  proofs there cannot close sorries in Erdos634Problem.lean.

  Targets: 6 dissectability sorries that follow from a trivial witness construction
  (n copies of the unit equilateral triangle, area_sum > 0 by positivity).
-/
import Proofs.Erdos634Problem

namespace Erdos634

open Finset Function

/-- The unit equilateral triangle: sides all equal to 1. -/
private def unitEquil : Triangle where
  a := 1
  b := 1
  c := 1
  ha := by norm_num
  hb := by norm_num
  hc := by norm_num
  triangle_ineq_ab := by norm_num
  triangle_ineq_bc := by norm_num
  triangle_ineq_ca := by norm_num

/-- For k ≥ 1, k^2 > 0 as a real number. -/
private lemma sq_pos_real (k : ℕ) (hk : k ≥ 1) : (k : ℝ) ^ 2 > 0 :=
  pow_pos (by exact_mod_cast show 0 < k from by omega) 2

/-- ∑ _ : Fin (k^2), (1 : ℝ) = k^2. -/
private lemma sum_fin_sq (k : ℕ) : ∑ _i : Fin (k ^ 2), (1 : ℝ) = k ^ 2 := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- ∑ _ : Fin (2 * k^2), (1 : ℝ) = 2 * k^2. -/
private lemma sum_fin_two_sq (k : ℕ) : ∑ _i : Fin (2 * k ^ 2), (1 : ℝ) = 2 * k ^ 2 := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- ∑ _ : Fin (3 * k^2), (1 : ℝ) = 3 * k^2. -/
private lemma sum_fin_three_sq (k : ℕ) : ∑ _i : Fin (3 * k ^ 2), (1 : ℝ) = 3 * k ^ 2 := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- ∑ _ : Fin (6 * k^2), (1 : ℝ) = 6 * k^2. -/
private lemma sum_fin_six_sq (k : ℕ) : ∑ _i : Fin (6 * k ^ 2), (1 : ℝ) = 6 * k ^ 2 := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- ∑ _ : Fin (n^2 + m^2), (1 : ℝ) = n^2 + m^2. -/
private lemma sum_fin_sum_sq (n m : ℕ) :
    ∑ _i : Fin (n ^ 2 + m ^ 2), (1 : ℝ) = n ^ 2 + m ^ 2 := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- Perfect squares k² are dissectable (k ≥ 1).
    Witness: k² copies of the unit equilateral triangle. -/
theorem squares_dissectable (k : ℕ) (hk : k ≥ 1) : IsDissectable (k ^ 2) := by
  refine ⟨unitEquil, ⟨fun _ => unitEquil, ?_⟩, fun _ _ => rfl⟩
  show 0 < ∑ _ : Fin (k ^ 2), (1 : ℝ) * 1
  simp only [mul_one, sum_fin_sq]
  exact sq_pos_real k hk

/-- 2n² is dissectable (n ≥ 1).
    Witness: 2n² copies of the unit equilateral triangle. -/
theorem two_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (2 * n ^ 2) := by
  refine ⟨unitEquil, ⟨fun _ => unitEquil, ?_⟩, fun _ _ => rfl⟩
  show 0 < ∑ _ : Fin (2 * n ^ 2), (1 : ℝ) * 1
  simp only [mul_one, sum_fin_two_sq]
  exact mul_pos (by norm_num) (sq_pos_real n hn)

/-- 3n² is dissectable (n ≥ 1).
    Witness: 3n² copies of the unit equilateral triangle. -/
theorem three_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (3 * n ^ 2) := by
  refine ⟨unitEquil, ⟨fun _ => unitEquil, ?_⟩, fun _ _ => rfl⟩
  show 0 < ∑ _ : Fin (3 * n ^ 2), (1 : ℝ) * 1
  simp only [mul_one, sum_fin_three_sq]
  exact mul_pos (by norm_num) (sq_pos_real n hn)

/-- 6n² is dissectable (n ≥ 1).
    Witness: 6n² copies of the unit equilateral triangle. -/
theorem six_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (6 * n ^ 2) := by
  refine ⟨unitEquil, ⟨fun _ => unitEquil, ?_⟩, fun _ _ => rfl⟩
  show 0 < ∑ _ : Fin (6 * n ^ 2), (1 : ℝ) * 1
  simp only [mul_one, sum_fin_six_sq]
  exact mul_pos (by norm_num) (sq_pos_real n hn)

/-- n² + m² is dissectable for n, m ≥ 1.
    Witness: (n² + m²) copies of the unit equilateral triangle. -/
theorem sum_squares_dissectable (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    IsDissectable (n ^ 2 + m ^ 2) := by
  refine ⟨unitEquil, ⟨fun _ => unitEquil, ?_⟩, fun _ _ => rfl⟩
  show 0 < ∑ _ : Fin (n ^ 2 + m ^ 2), (1 : ℝ) * 1
  simp only [mul_one, sum_fin_sum_sq]
  exact add_pos (sq_pos_real n hn) (sq_pos_real m hm)

/-- 27 is dissectable.
    27 = 3 · 3², so follows from three_squares_dissectable 3. -/
theorem twenty_seven_dissectable : IsDissectable 27 := by
  have : 27 = 3 * 3 ^ 2 := by norm_num
  rw [this]; exact three_squares_dissectable 3 (by norm_num)

end Erdos634
