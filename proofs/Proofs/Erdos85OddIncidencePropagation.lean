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

/-- For symmetric data stored under canonical unordered keys, parity at one
endpoint propagates past a given odd edge.  An even diagonal rules out the
degenerate choice of the endpoint itself. -/
theorem exists_odd_canonical_neighbor_of_even_incidence
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (m : ι × ι → ℕ) (i k : ι)
    (hsum : Even (∑ j, m (min i j, max i j)))
    (hik : Odd (m (min i k, max i k)))
    (hdiag : Even (m (i, i))) :
    ∃ j, j ≠ i ∧ j ≠ k ∧ Odd (m (min i j, max i j)) := by
  obtain ⟨j, hjk, hjodd⟩ :=
    exists_ne_odd_of_even_univ_sum_of_odd
      (fun j => m (min i j, max i j)) k hsum hik
  refine ⟨j, ?_, hjk, hjodd⟩
  intro hji
  subst j
  simp only [min_self, max_self] at hjodd
  exact (Nat.not_odd_iff_even.mpr hdiag) hjodd

end Erdos85
