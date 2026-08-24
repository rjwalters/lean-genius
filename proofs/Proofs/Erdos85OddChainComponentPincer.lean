import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity

/-!
# Odd-chain component pincer

An odd selected edge chain in a degree-two factor either exposes a nonzero
boundary or, when the boundary vanishes, contains a fully selected odd
component.  This is the finite parity core of `(73rnz_cjibkzzt)--
(73rnz_cjibkzzv)`.
-/

namespace Erdos85

open scoped BigOperators

/-- An odd finite sum has an odd summand. -/
theorem exists_odd_summand_of_odd_sum
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → ℕ)
    (hodd : Odd (∑ i ∈ I, f i)) :
    ∃ i ∈ I, Odd (f i) := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ i ∈ I, Even (f i) := by
    intro i hi
    exact Nat.not_odd_iff_even.mp (hnone i hi)
  have heven : Even (∑ i ∈ I, f i) := by
    exact Finset.even_sum f fun i hi => hall i hi
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- **Odd-chain pincer.**  Suppose the selected chain cardinality is the sum
of its componentwise cardinalities.  If zero boundary forces each component
intersection to be empty or the whole component, odd augmentation forces a
fully selected odd component. -/
theorem oddChain_boundary_ne_zero_or_exists_full_odd_component
    {E ι B : Type*} [DecidableEq E] [DecidableEq ι] [Zero B]
    (selected : Finset E) (I : Finset ι) (component : ι → Finset E)
    (boundary : B)
    (hcard : selected.card =
      ∑ i ∈ I, (selected ∩ component i).card)
    (hcomponentLaw : boundary = 0 → ∀ i ∈ I,
      selected ∩ component i = ∅ ∨ selected ∩ component i = component i)
    (hodd : Odd selected.card) :
    boundary ≠ 0 ∨
      ∃ i ∈ I, component i ⊆ selected ∧ Odd (component i).card := by
  by_cases hboundary : boundary = 0
  · right
    have hoddSum : Odd (∑ i ∈ I, (selected ∩ component i).card) := by
      rw [← hcard]
      exact hodd
    obtain ⟨i, hi, hiOdd⟩ := exists_odd_summand_of_odd_sum
      I (fun i => (selected ∩ component i).card) hoddSum
    rcases hcomponentLaw hboundary i hi with hempty | hfull
    · rw [hempty] at hiOdd
      simp at hiOdd
    · refine ⟨i, hi, ?_, ?_⟩
      · intro e he
        have : e ∈ selected ∩ component i := by simpa [hfull] using he
        exact (Finset.mem_inter.mp this).1
      · simpa [hfull] using hiOdd
  · exact Or.inl hboundary

end Erdos85

#print axioms Erdos85.exists_odd_summand_of_odd_sum
#print axioms Erdos85.oddChain_boundary_ne_zero_or_exists_full_odd_component
