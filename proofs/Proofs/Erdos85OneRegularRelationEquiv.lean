import Proofs.Erdos85DisjointTwoFactorsOnFive

/-!
# One-regular relations as equivalences

A relation with one entry in every row and column is exactly the graph of an
equivalence of its two shores.
-/

namespace Erdos85

theorem existsUnique_of_filter_card_one
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Y → Prop) [DecidablePred P]
    (hcard : ((Finset.univ : Finset Y).filter P).card = 1) :
    ∃! y, P y := by
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hyP : P y := by
    have : y ∈ (Finset.univ : Finset Y).filter P := by rw [hy]; simp
    exact (Finset.mem_filter.mp this).2
  refine ⟨y, hyP, ?_⟩
  intro z hzP
  have : z ∈ (Finset.univ : Finset Y).filter P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzP⟩
  rw [hy] at this
  simpa using this

/-- A one-regular relation is the graph of an equivalence. -/
theorem oneRegularRelation_exists_equiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (R : X → Y → Prop) [DecidableRel R]
    (hR : RelationOneRegular R) :
    ∃ f : X ≃ Y, ∀ x y, R x y ↔ f x = y := by
  have hrow : ∀ x : X, ∃! y : Y, R x y := fun x =>
    existsUnique_of_filter_card_one (R x) (hR.1 x)
  let g : X → Y := fun x => Classical.choose (hrow x)
  have hg (x : X) : R x (g x) := (Classical.choose_spec (hrow x)).1
  have huniq (x : X) {y : Y} (hy : R x y) : y = g x :=
    (Classical.choose_spec (hrow x)).2 y hy
  have hinj : Function.Injective g := by
    intro x x' heq
    have hcol := existsUnique_of_filter_card_one
      (fun z => R z (g x)) (hR.2 (g x))
    have hx := (Classical.choose_spec hcol).2 x (hg x)
    have hx' := (Classical.choose_spec hcol).2 x' (by
      rw [heq]
      exact hg x')
    exact hx.trans hx'.symm
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hxy, _⟩ := existsUnique_of_filter_card_one
      (fun z => R z y) (hR.2 y)
    refine ⟨x, ?_⟩
    exact (huniq x hxy).symm
  let f : X ≃ Y := Equiv.ofBijective g ⟨hinj, hsurj⟩
  refine ⟨f, ?_⟩
  intro x y
  constructor
  · intro hxy
    exact (huniq x hxy).symm
  · intro hxy
    change g x = y at hxy
    simpa [hxy] using hg x

end Erdos85

#print axioms Erdos85.oneRegularRelation_exists_equiv
