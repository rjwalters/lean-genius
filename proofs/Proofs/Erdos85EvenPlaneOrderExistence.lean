import Proofs.Erdos85PolarityEven
import Proofs.Erdos85PlaneOrderDropCriterion
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Cofinal characteristic-two plane-order witnesses

The even-polarity construction supplies the existence half of the proposed
plane-order drop family at every power of two.  This file records explicitly
that these orders are cofinal.
-/

namespace Erdos85

theorem exists_large_evenPlaneOrder_pred_witness (Q : Nat) :
    ∃ q : Nat, Q ≤ q ∧
      C4FreeMinDegreeWitness (q * q - 1) q := by
  let e := Q + 1
  let K := GaloisField 2 e
  letI : DecidableEq K := Classical.decEq K
  let q := Nat.card K
  have he : e ≠ 0 := by simp [e]
  have hqcard : q = 2 ^ e := GaloisField.card 2 e he
  have hQq : Q ≤ q := by
    rw [hqcard]
    have hpow := Nat.mul_le_pow (a := 2) (by decide : 2 ≠ 1) e
    exact (by omega : Q ≤ 2 * e).trans hpow
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine ⟨q, hQq, ?_⟩
  exact Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus K h2

theorem frequently_evenPlaneOrder_pred_witness :
    ∀ N : Nat, ∃ q : Nat, N ≤ q * q - 1 ∧
      C4FreeMinDegreeWitness (q * q - 1) q := by
  intro N
  obtain ⟨q, hNq, hw⟩ := exists_large_evenPlaneOrder_pred_witness (N + 3)
  refine ⟨q, ?_, hw⟩
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q * q := Nat.le_mul_of_pos_right q hq1
  omega

/-- Since characteristic two supplies the predecessor witnesses uniformly,
the negative solution is reduced to square-order nonexistence along large
powers of two. -/
theorem not_erdos85Question_of_eventual_twoPower_square_nonexistence
    (hno : ∀ᶠ e in Filter.atTop,
      ¬ C4FreeMinDegreeWitness ((2 ^ e) * (2 ^ e)) (2 ^ e)) :
    ¬ Erdos85Question := by
  apply erdos85Negation_iff_not_erdos85Question.mp
  apply erdos85Negation_of_unbounded_planeOrder_witness_gap
  intro N
  obtain ⟨E, hE⟩ := Filter.eventually_atTop.1 hno
  let e := max E (N + 3)
  let K := GaloisField 2 e
  letI : DecidableEq K := Classical.decEq K
  let q := Nat.card K
  have he : e ≠ 0 := by simp [e]
  have hqcard : q = 2 ^ e := GaloisField.card 2 e he
  have heE : E ≤ e := Nat.le_max_left _ _
  have heN : N + 3 ≤ e := Nat.le_max_right _ _
  have hqLower : e ≤ q := by
    rw [hqcard]
    have hpow := Nat.mul_le_pow (a := 2) (by decide : 2 ≠ 1) e
    exact (by omega : e ≤ 2 * e).trans hpow
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hw : C4FreeMinDegreeWitness (q * q - 1) q :=
    Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus K h2
  have hnot : ¬ C4FreeMinDegreeWitness (q * q) q := by
    simpa [hqcard] using hE e heE
  refine ⟨q, by omega, ?_, hw, hnot⟩
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q * q := Nat.le_mul_of_pos_right q hq1
  omega

end Erdos85
