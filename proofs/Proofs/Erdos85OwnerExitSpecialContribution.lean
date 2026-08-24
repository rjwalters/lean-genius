import Proofs.Erdos85OwnerAdaptedExitParity
import Proofs.Erdos85OwnerComplementSpecialContribution

/-!
# The owner vector carried by the unique special-leaf exit

The owner-adapted broken-fibre normal form produces exactly one exit in the
one-special-leaf case.  Retaining the leaf's Boolean owner shows that this
exit contributes precisely the corresponding owner unit.  It supplies the
complementary special correction exactly when the leaf owner is complementary
to the charged ordinary owner.
-/

namespace Erdos85

noncomputable section

/-- Owner-resolved parity vector of special leaves paired outside the leaf
subset. -/
def ownerExitContribution
    {V : Type*} [DecidableEq V]
    (leaves : Finset V) (mate : V → V) (leafOwner : V → Bool) :
    Bool → ZMod 2 :=
  fun i => ((ownerExitLeaves leaves mate).filter
    (fun l => leafOwner l = i)).card

private theorem ownerExitLeaves_subset
    {V : Type*} [DecidableEq V]
    (leaves : Finset V) (mate : V → V) :
    ownerExitLeaves leaves mate ⊆ leaves := by
  intro l hl
  exact (Finset.mem_filter.mp hl).1

/-- A one-leaf owner-adapted exit contributes exactly the unit at that
leaf's owner. -/
theorem exists_ownerAdapted_mate_ownerExitContribution_eq_unit
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (l : V) (leafOwner : V → Bool)
    (hlS : l ∈ S) (heven : Even S.card) :
    ∃ mate : V → V,
      (∀ v ∈ S, mate v ∈ S) ∧
      (∀ v ∈ S, mate (mate v) = v) ∧
      (∀ v ∈ S, mate v ≠ v) ∧
      ownerExitContribution {l} mate leafOwner =
        boolOwnerUnit (leafOwner l) := by
  have hsubset : ({l} : Finset V) ⊆ S := by
    intro x hx
    have hxl : x = l := by simpa using hx
    simpa [hxl] using hlS
  obtain ⟨mate, hclosed, hinvol, hfree, hcard⟩ :=
    exists_ownerAdapted_mate_ownerExit_card_eq
      S {l} hsubset heven (by simp)
  have hcardOne : (ownerExitLeaves {l} mate).card = 1 := by
    simpa using hcard
  obtain ⟨x, hExit⟩ := Finset.card_eq_one.mp hcardOne
  have hxLeaf : x ∈ ({l} : Finset V) := by
    apply ownerExitLeaves_subset {l} mate
    simp [hExit]
  have hxl : x = l := by simpa using hxLeaf
  have hExitLeaf : ownerExitLeaves {l} mate = {l} := by
    simpa [hxl] using hExit
  refine ⟨mate, hclosed, hinvol, hfree, ?_⟩
  funext i
  by_cases hli : leafOwner l = i
  · subst i
    have hfilter : ({l} : Finset V).filter
        (fun x => leafOwner x = leafOwner l) = {l} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩
        rfl
      · rintro rfl
        exact ⟨rfl, rfl⟩
    rw [show ownerExitContribution {l} mate leafOwner (leafOwner l) =
        ((({l} : Finset V).filter
          (fun x => leafOwner x = leafOwner l)).card : ZMod 2) by
          simp [ownerExitContribution, hExitLeaf]]
    rw [hfilter]
    norm_num [boolOwnerUnit]
  · have hil : i ≠ leafOwner l := by exact fun h => hli h.symm
    have hfilter : ({l} : Finset V).filter
        (fun x => leafOwner x = i) = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_filter.mp hy
        have hyl : y = l := by simpa using hy'.1
        subst y
        exact (hli hy'.2).elim
      · intro hy
        simp at hy
    rw [show ownerExitContribution {l} mate leafOwner i =
        ((({l} : Finset V).filter
          (fun x => leafOwner x = i)).card : ZMod 2) by
          simp [ownerExitContribution, hExitLeaf]]
    rw [hfilter]
    simp [boolOwnerUnit, hil]

/-- The unique special-leaf exit realizes the demanded complementary owner
unit if and only if the leaf itself has the complementary owner label. -/
theorem exists_ownerAdapted_mate_specialCorrection_iff_complementOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (l : V) (leafOwner : V → Bool)
    (hlS : l ∈ S) (heven : Even S.card) (charged : Bool) :
    ∃ mate : V → V,
      (∀ v ∈ S, mate v ∈ S) ∧
      (∀ v ∈ S, mate (mate v) = v) ∧
      (∀ v ∈ S, mate v ≠ v) ∧
      (ownerExitContribution {l} mate leafOwner =
          boolOwnerUnit (!charged) ↔
        leafOwner l = !charged) := by
  obtain ⟨mate, hclosed, hinvol, hfree, hunit⟩ :=
    exists_ownerAdapted_mate_ownerExitContribution_eq_unit
      S l leafOwner hlS heven
  refine ⟨mate, hclosed, hinvol, hfree, ?_⟩
  rw [hunit]
  constructor
  · intro h
    by_contra hne
    have happly := congrFun h (leafOwner l)
    simp [boolOwnerUnit, hne] at happly
  · intro h
    rw [h]

end

end Erdos85

#print axioms Erdos85.exists_ownerAdapted_mate_ownerExitContribution_eq_unit
#print axioms Erdos85.exists_ownerAdapted_mate_specialCorrection_iff_complementOwner
