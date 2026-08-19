import Mathlib

/-! # Projecting a biregular subdivision to its two shores -/

open Finset

namespace Erdos85

noncomputable section

/-- The shore relation obtained by suppressing the middle vertices of a
subdivision. -/
def subdivisionProjection {X Y Z : Type*}
    (R : X → Z → Prop) (S : Y → Z → Prop) : X → Y → Prop :=
  fun x y => ∃ z, R x z ∧ S y z

/-- If every middle vertex has one endpoint on each shore, every shore
vertex has degree `r`, and an endpoint pair occurs at most once, suppressing
the middle vertices produces an `r`-biregular relation. -/
theorem subdivisionProjection_biregular
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (R : X → Z → Prop) (S : Y → Z → Prop)
    [DecidableRel R] [DecidableRel S]
    [DecidableRel (subdivisionProjection R S)]
    (r : ℕ)
    (hRX : ∀ x, ((Finset.univ : Finset Z).filter fun z => R x z).card = r)
    (hSY : ∀ y, ((Finset.univ : Finset Z).filter fun z => S y z).card = r)
    (hRZ : ∀ z, ((Finset.univ : Finset X).filter fun x => R x z).card = 1)
    (hSZ : ∀ z, ((Finset.univ : Finset Y).filter fun y => S y z).card = 1)
    (hpair : ∀ ⦃x y z w⦄,
      R x z → S y z → R x w → S y w → z = w) :
    (∀ x, ((Finset.univ : Finset Y).filter fun y =>
      subdivisionProjection R S x y).card = r) ∧
    ∀ y, ((Finset.univ : Finset X).filter fun x =>
      subdivisionProjection R S x y).card = r := by
  classical
  have hY : ∀ z, ∃! y, S y z := by
    intro z
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hSZ z)
    refine ⟨y, ?_, ?_⟩
    · have : y ∈ (Finset.univ : Finset Y).filter fun y => S y z := by
        rw [hy]
        simp
      exact (Finset.mem_filter.mp this).2
    · intro y' hy'
      have : y' ∈ ({y} : Finset Y) := by
        rw [← hy]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
      simpa using this
  have hX : ∀ z, ∃! x, R x z := by
    intro z
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hRZ z)
    refine ⟨x, ?_, ?_⟩
    · have : x ∈ (Finset.univ : Finset X).filter fun x => R x z := by
        rw [hx]
        simp
      exact (Finset.mem_filter.mp this).2
    · intro x' hx'
      have : x' ∈ ({x} : Finset X) := by
        rw [← hx]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩
      simpa using this
  let py : Z → Y := fun z => (hY z).choose
  let px : Z → X := fun z => (hX z).choose
  have hpy (z : Z) : S (py z) z := (hY z).choose_spec.1
  have hpx (z : Z) : R (px z) z := (hX z).choose_spec.1
  constructor
  · intro x
    let ZX := (Finset.univ : Finset Z).filter fun z => R x z
    let YX := (Finset.univ : Finset Y).filter fun y =>
      subdivisionProjection R S x y
    have hcard : ZX.card = YX.card := by
      apply Finset.card_bij (fun z _hz => py z)
      · intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, (Finset.mem_filter.mp hz).2,
          hpy z⟩
      · intro z hz w hw heq
        apply hpair (Finset.mem_filter.mp hz).2 (hpy z)
          (Finset.mem_filter.mp hw).2
        simpa [heq] using hpy w
      · intro y hy
        obtain ⟨z, hxz, hyz⟩ := (Finset.mem_filter.mp hy).2
        have hz : z ∈ ZX := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
        refine ⟨z, hz, ?_⟩
        exact ((hY z).choose_spec.2 y hyz).symm
    rw [← hcard]
    exact hRX x
  · intro y
    let ZY := (Finset.univ : Finset Z).filter fun z => S y z
    let XY := (Finset.univ : Finset X).filter fun x =>
      subdivisionProjection R S x y
    have hcard : ZY.card = XY.card := by
      apply Finset.card_bij (fun z _hz => px z)
      · intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hpx z,
          (Finset.mem_filter.mp hz).2⟩
      · intro z hz w hw heq
        apply hpair (hpx z) (Finset.mem_filter.mp hz).2
        · simpa [heq] using hpx w
        · exact (Finset.mem_filter.mp hw).2
      · intro x hx
        obtain ⟨z, hxz, hyz⟩ := (Finset.mem_filter.mp hx).2
        have hz : z ∈ ZY := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩
        refine ⟨z, hz, ?_⟩
        exact ((hX z).choose_spec.2 x hxz).symm
    rw [← hcard]
    exact hSY y

end

end Erdos85

#print axioms Erdos85.subdivisionProjection_biregular
