import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

/-!
# Aggregate target parity of a closed curl

The rank-one component interaction law fixes the uncolored target support of
a closed odd curl: it is exactly the set of odd incidence components.  Since
the total shore has even parity and the source component is odd, an odd
number of other odd components receive exported switches.
-/

namespace Erdos85

open scoped BigOperators

/-- The color-resolved target sum has exactly the prescribed component
parity support. -/
theorem closedCurl_targetSupport_eq_oddComponents
    {A J : Type*} [DecidableEq A] [DecidableEq J]
    (colors : Finset A) (components : Finset J)
    (t : A → J → ZMod 2) (s : J → ZMod 2)
    (hrow : ∀ j ∈ components, ∑ a ∈ colors, t a j = s j) :
    components.filter (fun j => (∑ a ∈ colors, t a j) = 1) =
      components.filter (fun j => s j = 1) := by
  ext j
  simp only [Finset.mem_filter]
  by_cases hj : j ∈ components
  · simp [hj, hrow j hj]
  · simp [hj]

/-- Removing an odd source from an even total component parity leaves total
parity one on the other components. -/
theorem closedCurl_sum_other_componentParity_eq_one
    {J : Type*} [DecidableEq J]
    (components : Finset J) (source : J) (s : J → ZMod 2)
    (hsource : source ∈ components) (hsourceOdd : s source = 1)
    (htotal : ∑ j ∈ components, s j = 0) :
    ∑ j ∈ components.erase source, s j = 1 := by
  have hsplit := Finset.sum_erase_add
    (s := components) (f := s) hsource
  rw [hsourceOdd, htotal] at hsplit
  calc
    (∑ j ∈ components.erase source, s j) =
        (∑ j ∈ components.erase source, s j) + (1 + 1) := by
          rw [show (1 + 1 : ZMod 2) = 0 by decide, add_zero]
    _ = ((∑ j ∈ components.erase source, s j) + 1) + 1 := by
      rw [add_assoc]
    _ = 0 + 1 := by rw [hsplit]
    _ = 1 := zero_add 1

/-- Therefore some component distinct from the source is odd. -/
theorem exists_other_odd_closedCurl_target
    {J : Type*} [DecidableEq J]
    (components : Finset J) (source : J) (s : J → ZMod 2)
    (hsource : source ∈ components) (hsourceOdd : s source = 1)
    (htotal : ∑ j ∈ components, s j = 0) :
    ∃ j ∈ components, j ≠ source ∧ s j = 1 := by
  have hsum := closedCurl_sum_other_componentParity_eq_one
    components source s hsource hsourceOdd htotal
  by_contra hnone
  push Not at hnone
  have hzero : ∀ j ∈ components.erase source, s j = 0 := by
    intro j hj
    have hj' := Finset.mem_erase.mp hj
    have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hbinary (s j) with hz | ho
    · exact hz
    · exact (hnone j hj'.2 hj'.1 ho).elim
  have : (∑ j ∈ components.erase source, s j) = 0 :=
    Finset.sum_eq_zero hzero
  rw [this] at hsum
  exact zero_ne_one hsum

/-- In fact the number of other odd target components is itself odd. -/
theorem odd_card_other_closedCurl_targets
    {J : Type*} [DecidableEq J]
    (components : Finset J) (source : J) (s : J → ZMod 2)
    (hsource : source ∈ components) (hsourceOdd : s source = 1)
    (htotal : ∑ j ∈ components, s j = 0) :
    Odd ((components.erase source).filter (fun j => s j = 1)).card := by
  rw [← ZMod.natCast_eq_one_iff_odd]
  have hsum := closedCurl_sum_other_componentParity_eq_one
    components source s hsource hsourceOdd htotal
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hcast :
    (((components.erase source).filter (fun j => s j = 1)).card : ZMod 2) =
        ∑ j ∈ components.erase source, s j := by
    calc
      (((components.erase source).filter (fun j => s j = 1)).card : ZMod 2) =
          ∑ j ∈ components.erase source, if s j = 1 then 1 else 0 := by simp
      _ = ∑ j ∈ components.erase source, s j := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hbinary (s j) with hj | hj <;> simp [hj]
  rw [hcast, hsum]

end Erdos85

#print axioms Erdos85.closedCurl_targetSupport_eq_oddComponents
#print axioms Erdos85.closedCurl_sum_other_componentParity_eq_one
#print axioms Erdos85.exists_other_odd_closedCurl_target
#print axioms Erdos85.odd_card_other_closedCurl_targets
