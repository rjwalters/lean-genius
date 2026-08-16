import Mathlib.Algebra.BigOperators.Ring.Nat

namespace Erdos85

open scoped BigOperators

/-- An even finite incidence sum cannot have exactly one odd summand. -/
theorem exists_ne_odd_of_even_sum_of_odd
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (i : ι)
    (hi : i ∈ s)
    (hsum : Even (∑ j ∈ s, f j))
    (hodd : Odd (f i)) :
    ∃ j ∈ s, j ≠ i ∧ Odd (f j) := by
  by_contra h
  push Not at h
  have hfilter : {j ∈ s | Odd (f j)} = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact (h j hj.1 hji) hj.2
    · intro hji
      subst j
      exact ⟨hi, hodd⟩
  have hcard : Even ({j ∈ s | Odd (f j)}.card) :=
    (Finset.even_sum_iff_even_card_odd f).mp hsum
  rw [hfilter] at hcard
  simp at hcard

/-- Type-indexed form of `exists_ne_odd_of_even_sum_of_odd`. -/
theorem exists_ne_odd_of_even_univ_sum_of_odd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι)
    (hsum : Even (∑ j, f j))
    (hodd : Odd (f i)) :
    ∃ j, j ≠ i ∧ Odd (f j) := by
  obtain ⟨j, _, hji, hjodd⟩ :=
    exists_ne_odd_of_even_sum_of_odd Finset.univ f i (by simp) hsum hodd
  exact ⟨j, hji, hjodd⟩

end Erdos85
