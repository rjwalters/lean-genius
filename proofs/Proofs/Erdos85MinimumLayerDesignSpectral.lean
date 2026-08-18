import Proofs.Erdos85MinimumLayerDesignMatrix
import Proofs.Erdos85EqualCycleTerminal

/-!
# Spectral constraints on a minimum-layer design matrix

When the transverse scalar `s - 3` is nonsquare, the nonprincipal part of
the quotient has trace zero.  Thus the full trace is its common row sum `s`;
a diagonal bound by two then forces `s ≤ 2u`.
-/

namespace Erdos85

open Matrix

noncomputable section

/-- Nonsquare transverse scalar plus diagonal entries at most two bounds the
common row sum by twice the matrix order. -/
theorem minimumLayer_rowSum_le_two_mul_card_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (R : Matrix I I ℤ) (w : ℤ) (s : ℕ)
    (hs3 : 3 ≤ s) (hcard : 1 < Fintype.card I)
    (hsymm : R.IsSymm)
    (hsq : R * R = minimumLayerDesignMatrix R w)
    (hrow : ∀ i, minimumLayerRowSum R i = s)
    (hnonsquare : ¬ IsSquare (s - 3))
    (hdiag : ∀ i, R i i ≤ 2) :
    (s : ℤ) ≤ 2 * Fintype.card I := by
  let Q : Matrix I I ℚ := R.map (Int.castRingHom ℚ)
  have hrowQ : ∀ i, ∑ j, Q i j = (s : ℚ) := by
    intro i
    change (∑ j, (R i j : ℚ)) = (s : ℚ)
    rw [← Int.cast_sum]
    exact_mod_cast hrow i
  have hcolQ : ∀ j, ∑ i, Q i j = (s : ℚ) := by
    intro j
    calc
      (∑ i, Q i j) = ∑ i, Q j i := by
        apply Finset.sum_congr rfl
        intro i hi
        change (R i j : ℚ) = (R j i : ℚ)
        rw [hsymm.apply i j]
      _ = s := hrowQ j
  have hsqQ : Q * Q = (((s - 3 : ℕ) : ℚ)) •
      (1 : Matrix I I ℚ) + (w : ℚ) • Matrix.of (fun _ _ ↦ 1) := by
    ext i j
    have hij := congrFun (congrFun hsq i) j
    simp only [Matrix.mul_apply] at hij
    have hijZ : (∑ x, R i x * R x j) =
        w + if i = j then (s : ℤ) - 3 else 0 := by
      rw [hij]
      simp [minimumLayerDesignMatrix, hrow]
    change (∑ x, (R i x : ℚ) * (R x j : ℚ)) = _
    calc
      _ = ((∑ x, R i x * R x j : ℤ) : ℚ) := by push_cast; rfl
      _ = ((w + if i = j then (s : ℤ) - 3 else 0 : ℤ) : ℚ) := by
        rw [hijZ]
      _ = _ := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.of_apply, smul_eq_mul]
        by_cases h : i = j
        · subst j
          simp only [if_pos, one_mul]
          rw [Nat.cast_sub hs3]
          push_cast
          ring
        · simp [h]
  have htraceQ : Matrix.trace Q = (s : ℚ) :=
    Matrix.trace_eq_degree_of_sq_rankOne_of_nonsquare
      Q hcard hrowQ hcolQ (w : ℚ) hsqQ hnonsquare
  have htraceR : (∑ i, R i i) = (s : ℤ) := by
    change (∑ i, Q i i) = (s : ℚ) at htraceQ
    change (∑ i, (R i i : ℚ)) = (s : ℚ) at htraceQ
    rw [← Int.cast_sum] at htraceQ
    exact_mod_cast htraceQ
  rw [← htraceR]
  calc
    (∑ i, R i i) ≤ ∑ _i : I, (2 : ℤ) :=
      Finset.sum_le_sum (fun i _ ↦ hdiag i)
    _ = 2 * Fintype.card I := by simp; ring

end

end Erdos85
