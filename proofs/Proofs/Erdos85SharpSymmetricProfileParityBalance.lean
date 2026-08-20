import Mathlib

/-!
# Parity balance in a symmetric sharp-profile matrix

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

This is the abstract double count behind the binary sharp-defect system.
When the two parity classes have the same size, a symmetric matrix whose
cross-class row degrees differ from the balanced value by a sign must have
equally many rows of the two signs.
-/

namespace Erdos85

noncomputable section

/-- A symmetric sharp-profile matrix with balanced parity classes has exactly
one parity class worth of positive-oriented rows.

In the cyclic application, `positive v` means that the duplicated target
difference of row `v` is odd.  The two degree hypotheses are the local
one-duplicate/one-missing profile after those exceptional differences are
known to have opposite parity. -/
theorem sharpSymmetricProfile_positive_card_eq_parityCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (parity positive : V → Prop) [DecidablePred parity]
    [DecidablePred positive]
    (W : V → V → ℕ)
    (hsymm : ∀ v w, W v w = W w v)
    (N : ℕ)
    (hparity : ((Finset.univ : Finset V).filter parity).card = N)
    (hnotParity :
      ((Finset.univ : Finset V).filter fun v => ¬parity v).card = N)
    (hdegreeParity : ∀ v,
      (∑ w ∈ (Finset.univ : Finset V).filter parity, (W v w : ℤ)) =
        (N : ℤ) + if positive v then 1 else -1)
    (hdegreeNotParity : ∀ v,
      (∑ w ∈ (Finset.univ : Finset V).filter (fun w => ¬parity w),
        (W v w : ℤ)) =
          (N : ℤ) - if positive v then 1 else -1) :
    ((Finset.univ : Finset V).filter positive).card = N := by
  classical
  let E := (Finset.univ : Finset V).filter parity
  let O := (Finset.univ : Finset V).filter fun v => ¬parity v
  let sign : V → ℤ := fun v => if positive v then 1 else -1
  have hcross :
      (∑ v ∈ O, ∑ w ∈ E, (W v w : ℤ)) =
        ∑ w ∈ E, ∑ v ∈ O, (W w v : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    exact_mod_cast hsymm v w
  have hsignZero :
      (∑ v ∈ (Finset.univ : Finset V), sign v) = 0 := by
    have hEO : E.card = N := by simpa [E] using hparity
    have hOO : O.card = N := by simpa [O] using hnotParity
    have hcross' :
        (∑ v ∈ O, ((N : ℤ) + sign v)) =
          ∑ w ∈ E, ((N : ℤ) - sign w) := by
      calc
        _ = ∑ v ∈ O, ∑ w ∈ E, (W v w : ℤ) := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa [E, sign] using (hdegreeParity v).symm
        _ = ∑ w ∈ E, ∑ v ∈ O, (W w v : ℤ) := hcross
        _ = _ := by
          apply Finset.sum_congr rfl
          intro w hw
          simpa [O, sign] using hdegreeNotParity w
    have hparts :
        (∑ v ∈ (Finset.univ : Finset V), sign v) =
          (∑ v ∈ E, sign v) + ∑ v ∈ O, sign v := by
      rw [← Finset.sum_union]
      · apply Finset.sum_congr
        · ext v
          by_cases hp : parity v <;> simp [E, O, hp]
        · intro v hv
          rfl
      · simp [E, O, Finset.disjoint_filter]
    rw [hparts]
    have hcrossExpanded := hcross'
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul] at hcrossExpanded
    rw [hEO, hOO] at hcrossExpanded
    omega
  have hsignCard :
      (∑ v ∈ (Finset.univ : Finset V), sign v) =
        2 * (((Finset.univ : Finset V).filter positive).card : ℤ) -
          (Fintype.card V : ℤ) := by
    calc
      _ = ∑ v ∈ (Finset.univ : Finset V),
          (2 * (if positive v then (1 : ℤ) else 0) - 1) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hp : positive v <;> simp [sign, hp]
      _ = 2 * (((Finset.univ : Finset V).filter positive).card : ℤ) -
          (Fintype.card V : ℤ) := by
        rw [Finset.sum_sub_distrib]
        rw [show (∑ v : V, 2 * (if positive v then (1 : ℤ) else 0)) =
            2 * (((Finset.univ : Finset V).filter positive).card : ℤ) by
          rw [← Finset.mul_sum]
          simp]
        simp
  have hcardV : Fintype.card V = 2 * N := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) parity
    simp only [Finset.card_univ] at hpartition
    rw [hparity, hnotParity] at hpartition
    omega
  rw [hsignCard, hcardV] at hsignZero
  push_cast at hsignZero
  omega

end

end Erdos85

#print axioms Erdos85.sharpSymmetricProfile_positive_card_eq_parityCard
