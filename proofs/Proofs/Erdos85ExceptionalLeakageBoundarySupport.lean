import Proofs.Erdos85ExceptionalEmptyLeakageAggregate

/-!
# Boundary support forced by exceptional leakage

The exact empty-pole leakage mass cannot concentrate arbitrarily: every
outside vertex has total defect degree `q-1`.  Hence a nonsaturated empty
exceptional family forces a quantitatively large set of outside vertices in
its defect component.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Outside exceptional vertices incident in the defect graph with at least
one canonical empty center. -/
def exceptionalEmptyLeakageBoundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (S : Finset V) (q : ℕ) : Finset V :=
  (fullLineCenters G S q ∪ emptyLineCenters G S)ᶜ.filter fun x =>
    0 < ((secondOrderDefectGraph G).neighborFinset x ∩
      emptyLineCenters G S).card

/-- Defect degree caps the load carried by each boundary-support vertex, so
the exact aggregate leakage forces a lower bound on boundary support. -/
theorem binarySquare_exceptionalEmpty_leakageBoundary_card_lower
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
        (secondOrderDefectGraph G).Adj u v) :
    (emptyLineCenters G S).card *
        (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card) ≤
      (q - 1) * (exceptionalEmptyLeakageBoundary G S q).card := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let E := emptyLineCenters G S
  let D := secondOrderDefectGraph G
  let T := exceptionalEmptyLeakageBoundary G S q
  let load : V → ℕ := fun x => (D.neighborFinset x ∩ E).card
  have hsum := binarySquare_emptyPoles_outsideExceptional_defectIncidence_sum
    G hfree hq hreg hcard S hemptyClique
  change (∑ x ∈ Cᶜ, load x) = E.card * (q - C.card) at hsum
  have hTsub : T ⊆ Cᶜ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hrestrict : (∑ x ∈ Cᶜ, load x) = ∑ x ∈ T, load x := by
    symm
    apply Finset.sum_subset hTsub
    intro x hxC hxT
    have hxNotPos : ¬ 0 < load x := by
      intro hxPos
      exact hxT (Finset.mem_filter.mpr ⟨hxC, hxPos⟩)
    omega
  have hload : ∀ x ∈ T, load x ≤ q - 1 := by
    intro x _hx
    calc
      load x ≤ (D.neighborFinset x).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = D.degree x := D.card_neighborFinset_eq_degree x
      _ = q - 1 := binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard x
  have hupper := Finset.sum_le_card_nsmul T load (q - 1) hload
  change (∑ x ∈ T, load x) ≤ T.card * (q - 1) at hupper
  change E.card * (q - C.card) ≤ (q - 1) * T.card
  rw [← hsum, hrestrict]
  simpa [Nat.mul_comm] using hupper

/-- The exceptional support and every vertex carrying empty-pole leakage lie
in the single defect component of any chosen empty pole. -/
theorem exceptional_union_leakageBoundary_component_eq_emptyPole
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
    ∀ x ∈ (fullLineCenters G S q ∪ emptyLineCenters G S) ∪
        exceptionalEmptyLeakageBoundary G S q,
      (secondOrderDefectGraph G).connectedComponentMk x =
        (secondOrderDefectGraph G).connectedComponentMk pole := by
  let D := secondOrderDefectGraph G
  intro x hx
  rcases Finset.mem_union.mp hx with hxC | hxT
  · rcases Finset.mem_union.mp hxC with hxFull | hxEmpty
    · exact ConnectedComponent.connectedComponentMk_eq_of_adj
        (binarySquare_full_empty_secondOrderDefect_adj
          G hfree hq hreg S
            ((mem_fullLineCenters G S q x).mp hxFull)
            ((mem_emptyLineCenters G S pole).mp hpole))
    · by_cases hxp : x = pole
      · subst x
        rfl
      · exact ConnectedComponent.connectedComponentMk_eq_of_adj
          (hemptyClique hxEmpty hpole hxp)
  · have hxData := Finset.mem_filter.mp hxT
    have hloadPos := hxData.2
    obtain ⟨e, he⟩ := Finset.card_pos.mp hloadPos
    have heData := Finset.mem_inter.mp he
    have hxe : D.connectedComponentMk x = D.connectedComponentMk e :=
      ConnectedComponent.connectedComponentMk_eq_of_adj
        ((D.mem_neighborFinset x e).mp heData.1)
    have hep : D.connectedComponentMk e = D.connectedComponentMk pole := by
      by_cases hepEq : e = pole
      · subst e
        rfl
      · exact ConnectedComponent.connectedComponentMk_eq_of_adj
          (hemptyClique heData.2 hpole hepEq)
    exact hxe.trans hep

/-- Cardinal form of the component embedding: exceptional vertices and the
entire first leakage boundary contribute disjointly to the empty pole's
defect component. -/
theorem exceptional_card_add_leakageBoundary_card_le_component
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
    (fullLineCenters G S q ∪ emptyLineCenters G S).card +
        (exceptionalEmptyLeakageBoundary G S q).card ≤
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let T := exceptionalEmptyLeakageBoundary G S q
  let U := C ∪ T
  let comp := (secondOrderDefectGraph G).connectedComponentMk pole
  have hcomp := exceptional_union_leakageBoundary_component_eq_emptyPole
    G hfree hq hreg S hemptyClique pole hpole
  have hsub : (↑U : Set V) ⊆ comp.supp := by
    intro x hx
    rw [ConnectedComponent.mem_supp_iff]
    exact hcomp x hx
  have hncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at hncard
  have hdisj : Disjoint C T := by
    rw [Finset.disjoint_left]
    intro x hxC hxT
    have hxTc : x ∈ Cᶜ := (Finset.mem_filter.mp hxT).1
    exact (Finset.mem_compl.mp hxTc) hxC
  change C.card + T.card ≤ comp.supp.ncard
  rw [← Finset.card_union_of_disjoint hdisj]
  exact hncard

/-- Fraction-free component-order consequence of leakage: the empty-pole
component must accommodate both the exceptional core and enough boundary
vertices to carry all `|E|(q-c)` leaking incidences. -/
theorem binarySquare_exceptionalEmpty_leakage_component_order_lower
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
    (emptyLineCenters G S).card *
          (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card) +
        (q - 1) *
          (fullLineCenters G S q ∪ emptyLineCenters G S).card ≤
      (q - 1) *
        ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let E := emptyLineCenters G S
  let T := exceptionalEmptyLeakageBoundary G S q
  let m := ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard
  have hboundary := binarySquare_exceptionalEmpty_leakageBoundary_card_lower
    G hfree hq hreg hcard S hemptyClique
  change E.card * (q - C.card) ≤ (q - 1) * T.card at hboundary
  have hcomponent := exceptional_card_add_leakageBoundary_card_le_component
    G hfree (by omega) hreg S hemptyClique pole hpole
  change C.card + T.card ≤ m at hcomponent
  have hmul := Nat.mul_le_mul_left (q - 1) hcomponent
  rw [Nat.mul_add] at hmul
  change E.card * (q - C.card) + (q - 1) * C.card ≤ (q - 1) * m
  omega

end

end Erdos85

#print axioms
  Erdos85.binarySquare_exceptionalEmpty_leakageBoundary_card_lower
#print axioms
  Erdos85.exceptional_union_leakageBoundary_component_eq_emptyPole
#print axioms
  Erdos85.exceptional_card_add_leakageBoundary_card_le_component
#print axioms
  Erdos85.binarySquare_exceptionalEmpty_leakage_component_order_lower
