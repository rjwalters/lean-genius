import Proofs.Erdos85ExceptionalCoreTwinPoles

/-!
# Exceptional-core clique saturation

The Baer neighborhood census follows from the structural facts that the
exceptional core is a clique of size `q` and every empty center has defect
degree `q-1`.  Its `q-1` clique neighbors already exhaust its degree.
-/

open SimpleGraph

namespace Erdos85

/-- A vertex of a `q`-point clique with degree `q-1` has no neighbors outside
the clique. -/
theorem neighborFinset_eq_clique_erase_of_degree_saturated
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (C : Finset V) {q : ℕ} (hCcard : C.card = q)
    (hclique : ∀ ⦃u v⦄, u ∈ C → v ∈ C → u ≠ v → D.Adj u v)
    (pole : V) (hpole : pole ∈ C) (hdegree : D.degree pole = q - 1) :
    D.neighborFinset pole = C.erase pole := by
  have hsub : C.erase pole ⊆ D.neighborFinset pole := by
    intro v hv
    have ⟨hvpole, hvC⟩ := Finset.mem_erase.mp hv
    exact (D.mem_neighborFinset pole v).mpr
      (hclique hpole hvC hvpole.symm)
  have hcardErase : (C.erase pole).card = q - 1 := by
    rw [Finset.card_erase_of_mem hpole, hCcard]
  have hcardN : (D.neighborFinset pole).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree, hdegree]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcardErase, hcardN])).symm

/-- Clique saturation plus the disjoint full/empty split gives the literal
exceptional-core census `N_D(e)=F ∪ (E.erase e)`. -/
theorem neighborFinset_eq_full_union_empty_erase_of_exceptionalCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (full empty : Finset V) (hdisj : Disjoint full empty)
    {q : ℕ} (hcard : (full ∪ empty).card = q)
    (hclique : ∀ ⦃u v⦄, u ∈ full ∪ empty → v ∈ full ∪ empty →
      u ≠ v → D.Adj u v)
    (pole : V) (hpole : pole ∈ empty)
    (hdegree : D.degree pole = q - 1) :
    D.neighborFinset pole = full ∪ empty.erase pole := by
  have hpoleC : pole ∈ full ∪ empty := Finset.mem_union_right _ hpole
  have hsat := neighborFinset_eq_clique_erase_of_degree_saturated
    D (full ∪ empty) hcard hclique pole hpoleC hdegree
  rw [hsat]
  ext v
  have hpoleNotFull : pole ∉ full := fun hp =>
    Finset.disjoint_left.mp hdisj hp hpole
  have hfull_ne : v ∈ full → v ≠ pole := by
    intro hv hvp
    subst v
    exact hpoleNotFull hv
  simp only [Finset.mem_erase, Finset.mem_union]
  constructor
  · rintro ⟨hne, hf | he⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hne, he⟩
  · rintro (hf | ⟨hne, he⟩)
    · exact ⟨hfull_ne hf, Or.inl hf⟩
    · exact ⟨hne, Or.inr he⟩

/-- Two empty centers in a saturated exceptional clique fix their binary
pair indicator under `D`. -/
theorem adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (full empty : Finset V) (hdisj : Disjoint full empty)
    {q : ℕ} (hcard : (full ∪ empty).card = q)
    (hclique : ∀ ⦃u v⦄, u ∈ full ∪ empty → v ∈ full ∪ empty →
      u ≠ v → D.Adj u v)
    (pole₁ pole₂ : V) (hpole₁ : pole₁ ∈ empty) (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂)
    (hdegree₁ : D.degree pole₁ = q - 1)
    (hdegree₂ : D.degree pole₂ = q - 1) :
    (D.adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hN₁ := neighborFinset_eq_full_union_empty_erase_of_exceptionalCore
    D full empty hdisj hcard hclique pole₁ hpole₁ hdegree₁
  have hN₂ := neighborFinset_eq_full_union_empty_erase_of_exceptionalCore
    D full empty hdisj hcard hclique pole₂ hpole₂ hdegree₂
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census
    D full empty pole₁ pole₂ hpole₂ hpoles hN₁ hN₂

end Erdos85

#print axioms Erdos85.neighborFinset_eq_clique_erase_of_degree_saturated
#print axioms Erdos85.neighborFinset_eq_full_union_empty_erase_of_exceptionalCore
#print axioms Erdos85.adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_clique
