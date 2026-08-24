import Proofs.Erdos85ExceptionalSupportDefectCapacity

/-!
# Exact defect leakage from an exceptional empty pole

Below the saturated exceptional-support size, an empty pole has a precisely
measured set of defect neighbors outside the full/empty support.  This turns
the cardinal deficit from the capacity theorem into an actual family of
vertices available to structural arguments.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every exceptional-support vertex other than an empty pole is one of its
defect neighbors, and these are exactly its defect neighbors inside the
support. -/
theorem emptyPole_defect_neighbor_inter_full_union_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    (secondOrderDefectGraph G).neighborFinset pole ∩
        (fullLineCenters G S q ∪ emptyLineCenters G S) =
      (fullLineCenters G S q ∪ emptyLineCenters G S).erase pole := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨hxAdj, hxFull | hxEmpty⟩
    · exact ⟨fun h => by
        subst x
        exact (secondOrderDefectGraph G).loopless.irrefl pole
          (((secondOrderDefectGraph G).mem_neighborFinset pole pole).mp hxAdj),
        Or.inl hxFull⟩
    · exact ⟨fun h => by
        subst x
        exact (secondOrderDefectGraph G).loopless.irrefl pole
          (((secondOrderDefectGraph G).mem_neighborFinset pole pole).mp hxAdj),
        Or.inr hxEmpty⟩
  · rintro ⟨hxpole, hxFull | hxEmpty⟩
    constructor
    · rw [(secondOrderDefectGraph G).mem_neighborFinset]
      exact (binarySquare_full_empty_secondOrderDefect_adj
        G hfree hq hreg S
          ((mem_fullLineCenters G S q x).mp hxFull)
          ((mem_emptyLineCenters G S pole).mp hpole)).symm
    · exact Or.inl hxFull
    · constructor
      · rw [(secondOrderDefectGraph G).mem_neighborFinset]
        exact hemptyClique hpole hxEmpty hxpole.symm
      · exact Or.inr hxEmpty

/-- Exact leakage identity: an empty pole has `q-c` defect neighbors outside
an exceptional support of cardinality `c`. -/
theorem binarySquare_emptyPole_outsideExceptional_defectNeighbors_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    ((secondOrderDefectGraph G).neighborFinset pole \
      (fullLineCenters G S q ∪ emptyLineCenters G S)).card =
        q - (fullLineCenters G S q ∪ emptyLineCenters G S).card := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  change ((secondOrderDefectGraph G).neighborFinset pole \ C).card =
    q - C.card
  have hpoleC : pole ∈ C := Finset.mem_union_right _ hpole
  have hinter := emptyPole_defect_neighbor_inter_full_union_empty
    G hfree (by omega) hreg S hemptyClique pole hpole
  change (secondOrderDefectGraph G).neighborFinset pole ∩ C =
    C.erase pole at hinter
  rw [Finset.card_sdiff, Finset.inter_comm, hinter,
    Finset.card_erase_of_mem hpoleC,
    (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard]
  have hCcap : C.card ≤ q := by
    exact binarySquare_full_union_empty_card_le_of_emptyClique
      G hfree hq hreg hcard S hemptyClique ⟨pole, hpole⟩
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨pole, hpoleC⟩
  have hpred : 1 + (C.card - 1) = C.card := by omega
  rw [Nat.sub_sub, hpred]

/-- A strict exceptional-support deficit produces an actual defect neighbor
of the empty pole outside the exceptional family. -/
theorem binarySquare_emptyPole_exists_outsideExceptional_defectNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S)
    (hstrict :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card < q) :
    ∃ x, (secondOrderDefectGraph G).Adj pole x ∧
      x ∉ fullLineCenters G S q ∪ emptyLineCenters G S := by
  let T := (secondOrderDefectGraph G).neighborFinset pole \
    (fullLineCenters G S q ∪ emptyLineCenters G S)
  have hTcard := binarySquare_emptyPole_outsideExceptional_defectNeighbors_card
    G hfree hq hreg hcard S hemptyClique pole hpole
  have hTpos : 0 < T.card := by
    change 0 < ((secondOrderDefectGraph G).neighborFinset pole \
      (fullLineCenters G S q ∪ emptyLineCenters G S)).card
    rw [hTcard]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hTpos
  have hx' := Finset.mem_sdiff.mp hx
  exact ⟨x,
    ((secondOrderDefectGraph G).mem_neighborFinset pole x).mp hx'.1,
    hx'.2⟩

end

end Erdos85

#print axioms Erdos85.emptyPole_defect_neighbor_inter_full_union_empty
#print axioms
  Erdos85.binarySquare_emptyPole_outsideExceptional_defectNeighbors_card
#print axioms
  Erdos85.binarySquare_emptyPole_exists_outsideExceptional_defectNeighbor
