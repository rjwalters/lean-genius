import Mathlib

/-!
# Integral energy of the connected incidence bottleneck

The `NONBIP-CONNECTED [q]` incidence bottleneck has integral rows, each with
sum zero.  Once connectivity shows that none of those rows vanishes, the
lemmas below turn that qualitative statement into the uniform Frobenius
lower bound used by the spectral side of the argument.
-/

namespace Erdos85

open scoped BigOperators

/-- A nonzero integral vector with zero coordinate sum has squared energy at
least two.  Integrality is essential: a nonzero zero-sum real vector can have
arbitrarily small energy. -/
theorem two_le_sum_sq_of_int_sum_zero_of_exists_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ)
    (hsum : ∑ i, f i = 0)
    (hne : ∃ i, f i ≠ 0) :
    2 ≤ ∑ i, (f i) ^ 2 := by
  obtain ⟨i, hi⟩ := hne
  have hiu : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have herase : ∑ j ∈ (Finset.univ.erase i), f j = -f i := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι) f hiu
    rw [hsum] at hsplit
    omega
  have herase_ne : ∑ j ∈ (Finset.univ.erase i), f j ≠ 0 := by
    rw [herase]
    exact neg_ne_zero.mpr hi
  obtain ⟨j, hjmem, hj⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero herase_ne
  have hji : j ≠ i := by
    exact (Finset.mem_erase.mp hjmem).1
  have hpair : ({i, j} : Finset ι) ⊆ Finset.univ := by
    intro x hx
    exact Finset.mem_univ x
  have hle : ∑ x ∈ ({i, j} : Finset ι), (f x) ^ 2 ≤
      ∑ x ∈ (Finset.univ : Finset ι), (f x) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hpair
      (fun x _ _ ↦ sq_nonneg (f x))
  have hi_sq : 1 ≤ (f i) ^ 2 := by
    have := sq_pos_of_ne_zero hi
    omega
  have hj_sq : 1 ≤ (f j) ^ 2 := by
    have := sq_pos_of_ne_zero hj
    omega
  have htwo : 2 ≤ (f i) ^ 2 + (f j) ^ 2 := by omega
  rw [Finset.sum_insert (by simpa [eq_comm] using hji),
    Finset.sum_singleton] at hle
  exact htwo.trans hle

/-- Rowwise aggregation: an integral matrix whose every row is nonzero and
has sum zero has total squared-entry energy at least twice its row count. -/
theorem two_mul_card_le_sum_matrix_sq_of_rows_sum_zero_nonzero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (E : ι → κ → ℤ)
    (hsum : ∀ i, ∑ j, E i j = 0)
    (hne : ∀ i, ∃ j, E i j ≠ 0) :
    2 * Fintype.card ι ≤ ∑ i, ∑ j, (E i j) ^ 2 := by
  have hrow : ∀ i, (2 : ℤ) ≤ ∑ j, (E i j) ^ 2 := by
    intro i
    exact two_le_sum_sq_of_int_sum_zero_of_exists_ne_zero
      (E i) (hsum i) (hne i)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ ↦ hrow i)
  simpa [mul_comm] using h

#print axioms two_le_sum_sq_of_int_sum_zero_of_exists_ne_zero
#print axioms two_mul_card_le_sum_matrix_sq_of_rows_sum_zero_nonzero

end Erdos85
