import Proofs.Erdos85UniqueNeighborMulVecSupport

/-!
# Support bounds for integer zero-sum vectors

Every nonzero integer coordinate contributes at least one to the square
energy, so support size is at most `sum y_i^2`.  A nonzero vector whose
coordinate sum is zero cannot have singleton support, hence has support at
least two.  These are the generic bounds `2 <= m <= delta` for the centered
cut vector in the maximal defect-connectivity argument.
-/

namespace Erdos85

noncomputable section

/-- Integer support cardinality is bounded by square energy. -/
theorem card_finiteVectorSupport_le_sum_sq_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) :
    ((finiteVectorSupport y).card : ℤ) ≤ ∑ v, y v ^ 2 := by
  calc
    ((finiteVectorSupport y).card : ℤ) =
        ∑ v ∈ finiteVectorSupport y, (1 : ℤ) := by simp
    _ ≤ ∑ v ∈ finiteVectorSupport y, y v ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have hyv : y v ≠ 0 := (mem_finiteVectorSupport y v).mp hv
      have habsPos : 0 < (y v).natAbs := Int.natAbs_pos.mpr hyv
      have honeAbs : (1 : ℤ) ≤ ((y v).natAbs : ℤ) := by
        exact_mod_cast habsPos
      exact honeAbs.trans (Int.natAbs_le_self_sq (y v))
    _ = ∑ v, y v ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hvnot
      have hyv : y v = 0 := not_ne_iff.mp
        ((mem_finiteVectorSupport y v).not.mp hvnot)
      simp [hyv]

/-- A nonzero zero-sum integer vector has at least two support coordinates. -/
theorem two_le_card_finiteVectorSupport_of_ne_zero_of_sum_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) (hy : y ≠ 0) (hsum : ∑ v, y v = 0) :
    2 ≤ (finiteVectorSupport y).card := by
  have hpos : 0 < (finiteVectorSupport y).card := by
    rw [Finset.card_pos]
    by_contra hnot
    have hempty : finiteVectorSupport y = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hy
    funext v
    have hvnot : v ∉ finiteVectorSupport y := by
      rw [hempty]
      simp
    exact not_ne_iff.mp ((mem_finiteVectorSupport y v).not.mp hvnot)
  by_contra hnotTwo
  have hcard : (finiteVectorSupport y).card = 1 := by omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  have hwmem : w ∈ finiteVectorSupport y := by rw [hw]; simp
  have hsum' : ∑ v, y v = y w := by
    apply Finset.sum_eq_single w
    · intro v _ hvw
      have hvnot : v ∉ finiteVectorSupport y := by
        intro hv
        rw [hw] at hv
        exact hvw (Finset.mem_singleton.mp hv)
      exact not_ne_iff.mp ((mem_finiteVectorSupport y v).not.mp hvnot)
    · simp
  have hyw : y w ≠ 0 := (mem_finiteVectorSupport y w).mp hwmem
  have hyw0 : y w = 0 := hsum'.symm.trans hsum
  exact hyw hyw0

/-- Combined support interval when the square energy is a natural cast. -/
theorem integerZeroSum_support_card_bounds_of_sq_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {delta : ℕ} (hy : y ≠ 0)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (delta : ℤ)) :
    2 ≤ (finiteVectorSupport y).card ∧
      (finiteVectorSupport y).card ≤ delta := by
  refine ⟨two_le_card_finiteVectorSupport_of_ne_zero_of_sum_eq_zero
    y hy hsum, ?_⟩
  have hle := card_finiteVectorSupport_le_sum_sq_int y
  rw [henergy] at hle
  exact_mod_cast hle

end

end Erdos85

#print axioms Erdos85.card_finiteVectorSupport_le_sum_sq_int
#print axioms Erdos85.two_le_card_finiteVectorSupport_of_ne_zero_of_sum_eq_zero
#print axioms Erdos85.integerZeroSum_support_card_bounds_of_sq_sum_eq
