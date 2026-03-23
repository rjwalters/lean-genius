/-
  Dirichlet's Approximation Theorem

  For any real number α and positive integer Q, there exist integers p and q
  with 1 ≤ q ≤ Q such that |qα - p| < 1/Q.

  This is a fundamental result in Diophantine approximation, proved by
  Dirichlet (1842) using the pigeonhole principle. It is a key ingredient
  in the density increment lemma of Roth's theorem.

  Proof: Consider the Q+1 fractional parts {iα} for i = 0, 1, ..., Q.
  These Q+1 points lie in [0, 1). Partition [0, 1) into Q equal intervals.
  By pigeonhole, two fractional parts land in the same interval, giving
  |{iα} - {jα}| < 1/Q. Then q = |i - j| satisfies the bound.
-/
import Mathlib

namespace DirichletApproximation

open Int Finset

/-- Floor of two values agree implies the values differ by less than 1.
    If ⌊x⌋ = ⌊y⌋ and x ≥ y, then x - y < 1. -/
private lemma sub_lt_one_of_floor_eq {x y : ℝ} (_hxy : x ≥ y)
    (hfl : ⌊x⌋ = ⌊y⌋) : x - y < 1 := by
  have h1 : x < ↑⌊x⌋ + 1 := Int.lt_floor_add_one x
  have h2 : (↑⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  rw [hfl] at h1; linarith

/-- If two values in [0, Q) have the same floor, they differ by less than 1. -/
private lemma interval_bound {x y : ℝ} {Q : ℕ} (_hQ : 0 < Q)
    (_hx : 0 ≤ x) (_hx' : x < Q) (_hy : 0 ≤ y) (_hy' : y < Q)
    (hfl : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rcases le_or_gt x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact sub_lt_one_of_floor_eq hxy hfl.symm
  · rw [abs_of_pos (sub_pos.mpr hxy)]
    exact sub_lt_one_of_floor_eq hxy.le hfl

/-- Fractional part function: frac(x) = x - ⌊x⌋ -/
private noncomputable def frac (x : ℝ) : ℝ := x - ↑⌊x⌋

private lemma frac_nonneg (x : ℝ) : 0 ≤ frac x :=
  sub_nonneg.mpr (Int.floor_le x)

private lemma frac_lt_one (x : ℝ) : frac x < 1 := by
  unfold frac; linarith [Int.lt_floor_add_one x]

private lemma frac_eq (x : ℝ) : frac x = x - ↑⌊x⌋ := rfl

/-- The map sending i to ⌊Q · frac(i·α)⌋, assigning each of Q+1 points
    to one of Q intervals. -/
private noncomputable def intervalMap (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    Fin (Q + 1) → Fin Q := fun j =>
  ⟨Int.toNat ⌊↑Q * frac (↑(j : ℕ) * α)⌋, by
    have hQ_pos : (0 : ℝ) < ↑Q := Nat.cast_pos.mpr hQ
    have hfrac_nn : 0 ≤ frac (↑(j : ℕ) * α) := frac_nonneg _
    have hprod_nn : 0 ≤ ↑Q * frac (↑(j : ℕ) * α) :=
      mul_nonneg (le_of_lt hQ_pos) hfrac_nn
    have hprod_lt : ↑Q * frac (↑(j : ℕ) * α) < ↑Q := by
      calc ↑Q * frac (↑(j : ℕ) * α) < ↑Q * 1 :=
            mul_lt_mul_of_pos_left (frac_lt_one _) hQ_pos
        _ = ↑Q := mul_one _
    rw [Int.toNat_lt (Int.floor_nonneg.mpr hprod_nn)]
    exact_mod_cast Int.floor_lt.mpr hprod_lt⟩

/-- **Dirichlet's Approximation Theorem**: For any real α and Q ≥ 1,
    there exist integers p, q with 1 ≤ q ≤ Q and |qα - p| < 1/Q.

    This follows from the pigeonhole principle: Q+1 fractional parts in Q
    intervals forces a collision, giving a good rational approximation. -/
theorem dirichlet_approximation (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ∧ |↑q * α - ↑p| < 1 / (↑Q : ℝ) := by
  -- Apply pigeonhole: Q+1 points in Q intervals
  have hcard : Fintype.card (Fin (Q + 1)) > Fintype.card (Fin Q) := by
    simp [Fintype.card_fin]
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (intervalMap α Q hQ) hcard
  -- i ≠ j with intervalMap(i) = intervalMap(j)
  -- This means frac(i·α) and frac(j·α) are in the same [k/Q, (k+1)/Q) interval
  -- WLOG i.val > j.val (swap if needed)
  wlog h_gt : (j : ℕ) < (i : ℕ) with H
  · push_neg at h_gt
    rcases h_gt.eq_or_lt with h_eq | h_lt
    · exact absurd (Fin.ext (by omega)) hij
    · exact H α Q hQ hcard j i hij.symm hfij.symm h_lt
  -- Set q = i - j (positive since i > j)
  set q := (i : ℕ) - (j : ℕ) with hq_def
  have hq_pos : 1 ≤ q := by omega
  have hq_le : q ≤ Q := by
    have hi := i.isLt  -- i < Q + 1
    have hj := j.isLt  -- j < Q + 1
    omega
  -- Set p = ⌊i·α⌋ - ⌊j·α⌋ (the integer part difference)
  set p := ⌊(↑(i : ℕ) : ℝ) * α⌋ - ⌊(↑(j : ℕ) : ℝ) * α⌋ with hp_def
  refine ⟨p, q, hq_pos, hq_le, ?_⟩
  -- Key: q·α - p = frac(i·α) - frac(j·α)
  have hkey : ↑q * α - ↑p = frac (↑(i : ℕ) * α) - frac (↑(j : ℕ) * α) := by
    simp only [frac_eq, hp_def, hq_def]
    have hij_le : (j : ℕ) ≤ (i : ℕ) := le_of_lt h_gt
    rw [Nat.cast_sub hij_le]
    push_cast
    ring
  rw [hkey]
  -- From intervalMap(i) = intervalMap(j):
  -- ⌊Q · frac(i·α)⌋ = ⌊Q · frac(j·α)⌋
  have hQ_pos : (0 : ℝ) < ↑Q := Nat.cast_pos.mpr hQ
  -- Extract the floor equality from the Fin equality
  have hfl : ⌊↑Q * frac (↑(i : ℕ) * α)⌋ = ⌊↑Q * frac (↑(j : ℕ) * α)⌋ := by
    have hval := congr_arg (fun x : Fin Q => (x : ℕ)) hfij
    simp only [intervalMap] at hval
    have hi_nn : 0 ≤ ⌊↑Q * frac (↑(i : ℕ) * α)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hQ_pos) (frac_nonneg _))
    have hj_nn : 0 ≤ ⌊↑Q * frac (↑(j : ℕ) * α)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hQ_pos) (frac_nonneg _))
    have hi_cast : (⌊↑Q * frac (↑(i : ℕ) * α)⌋.toNat : ℤ) = ⌊↑Q * frac (↑(i : ℕ) * α)⌋ :=
      Int.toNat_of_nonneg hi_nn
    have hj_cast : (⌊↑Q * frac (↑(j : ℕ) * α)⌋.toNat : ℤ) = ⌊↑Q * frac (↑(j : ℕ) * α)⌋ :=
      Int.toNat_of_nonneg hj_nn
    linarith [show (⌊↑Q * frac (↑(i : ℕ) * α)⌋.toNat : ℤ) =
      (⌊↑Q * frac (↑(j : ℕ) * α)⌋.toNat : ℤ) from by exact_mod_cast hval]
  -- |frac(i·α) - frac(j·α)| < 1/Q
  -- From: ⌊Q·frac(i·α)⌋ = ⌊Q·frac(j·α)⌋ with both in [0, Q)
  -- → |Q·frac(i·α) - Q·frac(j·α)| < 1
  -- → |frac(i·α) - frac(j·α)| < 1/Q
  have hi_prod_nn : 0 ≤ ↑Q * frac (↑(i : ℕ) * α) :=
    mul_nonneg (le_of_lt hQ_pos) (frac_nonneg _)
  have hi_prod_lt : ↑Q * frac (↑(i : ℕ) * α) < ↑Q :=
    (mul_lt_iff_lt_one_right hQ_pos).mpr (frac_lt_one _)
  have hj_prod_nn : 0 ≤ ↑Q * frac (↑(j : ℕ) * α) :=
    mul_nonneg (le_of_lt hQ_pos) (frac_nonneg _)
  have hj_prod_lt : ↑Q * frac (↑(j : ℕ) * α) < ↑Q :=
    (mul_lt_iff_lt_one_right hQ_pos).mpr (frac_lt_one _)
  have habs_prod : |↑Q * frac (↑(i : ℕ) * α) - ↑Q * frac (↑(j : ℕ) * α)| < 1 :=
    interval_bound hQ hi_prod_nn hi_prod_lt hj_prod_nn hj_prod_lt hfl
  -- Factor out Q: |Q| · |frac_i - frac_j| < 1, so |frac_i - frac_j| < 1/Q
  rw [show ↑Q * frac (↑(i : ℕ) * α) - ↑Q * frac (↑(j : ℕ) * α) =
      ↑Q * (frac (↑(i : ℕ) * α) - frac (↑(j : ℕ) * α)) from by ring] at habs_prod
  rw [abs_mul, abs_of_pos hQ_pos] at habs_prod
  rw [lt_div_iff₀ hQ_pos]; linarith

end DirichletApproximation
