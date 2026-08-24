import Proofs.Erdos85BinarySquareEmptyCoreSaturation

/-!
# Minority-clique exceptional saturation

Exact audit-facing version of empty-core saturation: the minority/empty
family is supplied directly as a second-order-defect clique.  No assertion
about defect edges within the full/majority family is made or needed.
-/

open SimpleGraph

namespace Erdos85

/-- A minority defect clique together with all full--empty cross edges and
total exceptional cardinality `q` exhausts every empty center's defect row. -/
theorem binarySquare_minorityClique_emptyCenter_neighborFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S full empty : Finset V)
    (hfull : ∀ x ∈ full, (G.neighborFinset x ∩ S).card = q)
    (hempty : ∀ x ∈ empty, (G.neighborFinset x ∩ S).card = 0)
    (hemptyClique : ∀ ⦃u v⦄, u ∈ empty → v ∈ empty → u ≠ v →
      (secondOrderDefectGraph G).Adj u v)
    (hcoreCard : (full ∪ empty).card = q)
    (pole : V) (hpole : pole ∈ empty) :
    (secondOrderDefectGraph G).neighborFinset pole =
      full ∪ empty.erase pole := by
  let D := secondOrderDefectGraph G
  have hdisj : Disjoint full empty := Finset.disjoint_left.mpr (by
    intro x hxFull hxEmpty
    have hf := hfull x hxFull
    have he := hempty x hxEmpty
    omega)
  have hsub : full ∪ empty.erase pole ⊆ D.neighborFinset pole := by
    intro v hv
    apply (D.mem_neighborFinset pole v).mpr
    rcases Finset.mem_union.mp hv with hvFull | hvEmpty
    · exact (binarySquare_full_empty_secondOrderDefect_adj
        G hfree (by omega) hreg S (hfull v hvFull) (hempty pole hpole)).symm
    · have hvData := Finset.mem_erase.mp hvEmpty
      exact hemptyClique hpole hvData.2 hvData.1.symm
  have htargetEq : full ∪ empty.erase pole = (full ∪ empty).erase pole := by
    ext v
    have hpoleNotFull : pole ∉ full := fun hp =>
      Finset.disjoint_left.mp hdisj hp hpole
    have hfull_ne : v ∈ full → v ≠ pole := by
      intro hv hvp
      subst v
      exact hpoleNotFull hv
    simp only [Finset.mem_erase, Finset.mem_union]
    constructor
    · rintro (hf | ⟨hne, he⟩)
      · exact ⟨hfull_ne hf, Or.inl hf⟩
      · exact ⟨hne, Or.inr he⟩
    · rintro ⟨hne, hf | he⟩
      · exact Or.inl hf
      · exact Or.inr ⟨hne, he⟩
  have hpoleCore : pole ∈ full ∪ empty := Finset.mem_union_right _ hpole
  have htargetCard : (full ∪ empty.erase pole).card = q - 1 := by
    rw [htargetEq, Finset.card_erase_of_mem hpoleCore, hcoreCard]
  have hDdegree : D.degree pole = q - 1 :=
    binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard pole
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [htargetCard, D.card_neighborFinset_eq_degree, hDdegree])).symm

/-- Two empty vertices of the saturated minority clique fix their pair
indicator under the second-order defect matrix. -/
theorem binarySquare_minorityClique_emptyCenters_mulVec_eq_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S full empty : Finset V)
    (hfull : ∀ x ∈ full, (G.neighborFinset x ∩ S).card = q)
    (hempty : ∀ x ∈ empty, (G.neighborFinset x ∩ S).card = 0)
    (hemptyClique : ∀ ⦃u v⦄, u ∈ empty → v ∈ empty → u ≠ v →
      (secondOrderDefectGraph G).Adj u v)
    (hcoreCard : (full ∪ empty).card = q)
    (pole₁ pole₂ : V) (hpole₁ : pole₁ ∈ empty) (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hN₁ := binarySquare_minorityClique_emptyCenter_neighborFinset_eq
    G hfree hq hreg hcard S full empty hfull hempty hemptyClique
    hcoreCard pole₁ hpole₁
  have hN₂ := binarySquare_minorityClique_emptyCenter_neighborFinset_eq
    G hfree hq hreg hcard S full empty hfull hempty hemptyClique
    hcoreCard pole₂ hpole₂
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census
    (secondOrderDefectGraph G) full empty pole₁ pole₂ hpole₂ hpoles hN₁ hN₂

end Erdos85

#print axioms Erdos85.binarySquare_minorityClique_emptyCenter_neighborFinset_eq
#print axioms Erdos85.binarySquare_minorityClique_emptyCenters_mulVec_eq_self
