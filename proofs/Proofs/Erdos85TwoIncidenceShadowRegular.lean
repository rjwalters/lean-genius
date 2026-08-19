import Mathlib

/-!
# Regular shadows of degree-two incidence systems

If every column of a finite incidence relation contains two points, then
each incidence at a point selects the other endpoint of that column.  When
two distinct points occur together in at most one column, this selection is
a bijection from a row to the neighbors in the resulting shadow graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph joining two points when they occur in a common incidence
column. -/
def twoIncidenceShadow {X Z : Type*} (R : X → Z → Prop) : SimpleGraph X where
  Adj x y := x ≠ y ∧ ∃ z, R x z ∧ R y z
  symm := ⟨by
    intro x y
    rintro ⟨hxy, z, hxz, hyz⟩
    exact ⟨hxy.symm, z, hyz, hxz⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

instance twoIncidenceShadow_decidableAdj
    {X Z : Type*} (R : X → Z → Prop) [DecidableRel R] :
    DecidableRel (twoIncidenceShadow R).Adj := by
  classical
  unfold twoIncidenceShadow
  infer_instance

/-- A degree-two incidence system with no repeated point-pair has shadow
degree equal to its row degree. -/
theorem twoIncidenceShadow_degree_eq_rowCard
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    (R : X → Z → Prop) [DecidableRel R]
    (hcol : ∀ z,
      ((Finset.univ : Finset X).filter fun x => R x z).card = 2)
    (hpair : ∀ ⦃x y z w⦄, x ≠ y →
      R x z → R y z → R x w → R y w → z = w)
    (x : X) :
    (twoIncidenceShadow R).degree x =
      ((Finset.univ : Finset Z).filter fun z => R x z).card := by
  classical
  let row : Finset Z := (Finset.univ : Finset Z).filter fun z => R x z
  have hother : ∀ z, R x z → ∃! y, y ≠ x ∧ R y z := by
    intro z hxz
    obtain ⟨a, b, hab, hcolumn⟩ := Finset.card_eq_two.mp (hcol z)
    have hxmem : x ∈ ({a, b} : Finset X) := by
      rw [← hcolumn]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
    have hx : x = a ∨ x = b := by simpa using hxmem
    rcases hx with rfl | rfl
    · refine ⟨b, ⟨hab.symm, ?_⟩, ?_⟩
      · have : b ∈ (Finset.univ : Finset X).filter fun y => R y z := by
          rw [hcolumn]
          simp
        exact (Finset.mem_filter.mp this).2
      · intro y hy
        have hymem : y ∈ ({x, b} : Finset X) := by
          rw [← hcolumn]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2⟩
        rcases (by simpa using hymem : y = x ∨ y = b) with rfl | rfl
        · exact (hy.1 rfl).elim
        · rfl
    · refine ⟨a, ⟨hab, ?_⟩, ?_⟩
      · have : a ∈ (Finset.univ : Finset X).filter fun y => R y z := by
          rw [hcolumn]
          simp
        exact (Finset.mem_filter.mp this).2
      · intro y hy
        have hymem : y ∈ ({a, x} : Finset X) := by
          rw [← hcolumn]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2⟩
        rcases (by simpa using hymem : y = a ∨ y = x) with rfl | rfl
        · rfl
        · exact (hy.1 rfl).elim
  let other : (z : Z) → R x z → X := fun z hz => Classical.choose (hother z hz)
  have hotherSpec (z : Z) (hz : R x z) :
      other z hz ≠ x ∧ R (other z hz) z :=
    (Classical.choose_spec (hother z hz)).1
  have hotherUnique (z : Z) (hz : R x z) {y : X}
      (hy : y ≠ x ∧ R y z) : y = other z hz :=
    (Classical.choose_spec (hother z hz)).2 y hy
  rw [← (twoIncidenceShadow R).card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun z hz => other z (Finset.mem_filter.mp hz).2)
  · intro z hz
    have hs := hotherSpec z (Finset.mem_filter.mp hz).2
    exact ((twoIncidenceShadow R).mem_neighborFinset x _).mpr
      ⟨hs.1.symm, z, (Finset.mem_filter.mp hz).2, hs.2⟩
  · intro z hz w hw heq
    have hzR := (Finset.mem_filter.mp hz).2
    have hwR := (Finset.mem_filter.mp hw).2
    have hs := hotherSpec z hzR
    have ht := hotherSpec w hwR
    exact hpair hs.1.symm hzR hs.2 hwR (heq ▸ ht.2)
  · intro y hy
    have hxy := ((twoIncidenceShadow R).mem_neighborFinset x y).mp hy
    obtain ⟨hneq, z, hxz, hyz⟩ := hxy
    have hzrow : z ∈ row := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
    refine ⟨z, hzrow, ?_⟩
    exact (hotherUnique z hxz ⟨hneq.symm, hyz⟩).symm

/-- Constant row size gives a regular shadow graph. -/
theorem twoIncidenceShadow_regular
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    (R : X → Z → Prop) [DecidableRel R]
    (r : ℕ)
    (hrow : ∀ x,
      ((Finset.univ : Finset Z).filter fun z => R x z).card = r)
    (hcol : ∀ z,
      ((Finset.univ : Finset X).filter fun x => R x z).card = 2)
    (hpair : ∀ ⦃x y z w⦄, x ≠ y →
      R x z → R y z → R x w → R y w → z = w) :
    ∀ x, (twoIncidenceShadow R).degree x = r := by
  intro x
  rw [twoIncidenceShadow_degree_eq_rowCard R hcol hpair x, hrow x]

end

end Erdos85

#print axioms Erdos85.twoIncidenceShadow_regular
