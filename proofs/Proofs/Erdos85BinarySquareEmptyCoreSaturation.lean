import Proofs.Erdos85BinarySquareDyadicSignedTerminal
import Proofs.Erdos85ExceptionalCoreTwinPoles

/-!
# Empty exceptional-core saturation

This is the applicable graph-native Baer interface.  Only the empty
(minority) line family needs point replication at most one.  It is therefore
a defect clique, while incompatible full/empty shore occupancies supply all
cross defect edges.  If the total exceptional support has size `q`, these
`q-1` forced edges exhaust an empty center's defect degree.
-/

open SimpleGraph

namespace Erdos85

/-- An empty exceptional center sees exactly every full center and every
other empty center in the second-order defect graph. -/
theorem binarySquare_emptyCenter_secondOrderDefect_neighborFinset_eq
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
    (hemptyCap : ∀ v, (G.neighborFinset v ∩ empty).card ≤ 1)
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
      exact replicationAtMostOne_secondOrderDefect_adj
        G hfree empty hemptyCap hpole hvData.2 hvData.1.symm
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
  have hneighborCard : (D.neighborFinset pole).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree, hDdegree]
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [htargetCard, hneighborCard])).symm

/-- Two distinct empty exceptional centers give the fixed two-pole vector
needed by exceptional-line transport, using no hypothesis on full--full
defect adjacency. -/
theorem binarySquare_emptyCenters_adjMatrix_mulVec_twoCoordinate_eq_self
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
    (hemptyCap : ∀ v, (G.neighborFinset v ∩ empty).card ≤ 1)
    (hcoreCard : (full ∪ empty).card = q)
    (pole₁ pole₂ : V) (hpole₁ : pole₁ ∈ empty) (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hN₁ := binarySquare_emptyCenter_secondOrderDefect_neighborFinset_eq
    G hfree hq hreg hcard S full empty hfull hempty hemptyCap
    hcoreCard pole₁ hpole₁
  have hN₂ := binarySquare_emptyCenter_secondOrderDefect_neighborFinset_eq
    G hfree hq hreg hcard S full empty hfull hempty hemptyCap
    hcoreCard pole₂ hpole₂
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census
    (secondOrderDefectGraph G) full empty pole₁ pole₂ hpole₂ hpoles hN₁ hN₂

end Erdos85

#print axioms Erdos85.binarySquare_emptyCenter_secondOrderDefect_neighborFinset_eq
#print axioms Erdos85.binarySquare_emptyCenters_adjMatrix_mulVec_twoCoordinate_eq_self
