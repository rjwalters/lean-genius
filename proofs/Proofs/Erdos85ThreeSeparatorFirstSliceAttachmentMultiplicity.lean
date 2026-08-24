import Proofs.Erdos85ThreeSeparatorFirstSliceWLocation

/-!
# Attachment multiplicities on the first non-endpoint slice

At `a = 1`, every point of `X` has zero, one, or two defect attachments to
the separator.  The vertex count and total attachment count differ by two,
forcing two more attachment-free points than twice-attached points (B26).
-/

open Finset

namespace Erdos85

/-- B26 directly from a bounded attachment-count function on `X`. -/
theorem firstSlice_attachmentMultiplicity_zero_eq_two_add_two
    {V : Type*} [DecidableEq V]
    (X : Finset V) (t : V → ℕ) (q : ℕ)
    (hq : 2 ≤ q)
    (ht : ∀ x ∈ X, t x ≤ 2)
    (hXcard : X.card = 2 * q - 2)
    (hattach : (∑ x ∈ X, t x) = 2 * q - 4) :
    (X.filter fun x ↦ t x = 0).card =
        (X.filter fun x ↦ t x = 2).card + 2 ∧
      2 ≤ (X.filter fun x ↦ t x = 0).card := by
  let N0 := X.filter fun x ↦ t x = 0
  let N1 := X.filter fun x ↦ t x = 1
  let N2 := X.filter fun x ↦ t x = 2
  have hcover : N0 ∪ N1 ∪ N2 = X := by
    ext x
    constructor
    · simp only [Finset.mem_union, Finset.mem_filter, N0, N1, N2]
      tauto
    · intro hx
      have htx := ht x hx
      simp only [Finset.mem_union, Finset.mem_filter, N0, N1, N2]
      interval_cases t x <;> simp [hx]
  have h01 : Disjoint N0 N1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp only [Finset.mem_filter, N0] at hx0
    simp only [Finset.mem_filter, N1] at hx1
    omega
  have h02 : Disjoint N0 N2 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    simp only [Finset.mem_filter, N0] at hx0
    simp only [Finset.mem_filter, N2] at hx2
    omega
  have h12 : Disjoint N1 N2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter, N1] at hx1
    simp only [Finset.mem_filter, N2] at hx2
    omega
  have h012 : Disjoint (N0 ∪ N1) N2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rcases Finset.mem_union.mp hx with hx0 | hx1
    · exact (Finset.disjoint_left.mp h02) hx0 hx2
    · exact (Finset.disjoint_left.mp h12) hx1 hx2
  have hcard : N0.card + N1.card + N2.card = X.card := by
    rw [← hcover, Finset.card_union_of_disjoint h012,
      Finset.card_union_of_disjoint h01]
  have hsum0 : (∑ x ∈ N0, t x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hsum1 : (∑ x ∈ N1, t x) = N1.card := by
    calc
      (∑ x ∈ N1, t x) = ∑ _x ∈ N1, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = N1.card := by simp
  have hsum2 : (∑ x ∈ N2, t x) = 2 * N2.card := by
    calc
      (∑ x ∈ N2, t x) = ∑ _x ∈ N2, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = 2 * N2.card := by simp [mul_comm]
  have hsum : (∑ x ∈ X, t x) = N1.card + 2 * N2.card := by
    rw [← hcover, Finset.sum_union h012, Finset.sum_union h01,
      hsum0, hsum1, hsum2]
    omega
  change N0.card = N2.card + 2 ∧ 2 ≤ N0.card
  omega

#print axioms firstSlice_attachmentMultiplicity_zero_eq_two_add_two

end Erdos85
