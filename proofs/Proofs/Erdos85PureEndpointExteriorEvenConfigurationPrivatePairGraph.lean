import Proofs.Erdos85PureEndpointExteriorEvenConfigurationPrivatePairDegree

/-!
# The private-pair graph of an equality circuit

The private partner relation is packaged as a native simple graph on the
circuit rows.  Its degree sequence is the row-hole sequence.  At minimum
hole mass the handshake lemma therefore gives exactly `m` private edges.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- The private-pair graph on a selected family of rows. -/
def privatePairGraph
    {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (owner : β → Finset γ) (T : Finset α) :
    SimpleGraph {a // a ∈ T} where
  Adj a b := a ≠ b ∧ ∃ y ∈ B a.1, y ∈ B b.1 ∧ (owner y).card = 1
  symm := ⟨by
      intro a b hab
      refine ⟨Ne.symm hab.1, ?_⟩
      obtain ⟨y, hya, hyb, hyOne⟩ := hab.2
      exact ⟨y, hyb, hya, hyOne⟩⟩
  loopless := ⟨by
      intro a haa
      exact haa.1 rfl⟩

noncomputable instance privatePairGraph.instDecidableRel
    {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (owner : β → Finset γ) (T : Finset α) :
    DecidableRel (privatePairGraph B owner T).Adj := Classical.decRel _

/-- The degree in `privatePairGraph` is the cardinality of the corresponding
filtered partner set in the ambient row type. -/
theorem privatePairGraph_degree_eq_filter_card
    {α β γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (owner : β → Finset γ) (T : Finset α)
    (a : {a // a ∈ T}) :
    (privatePairGraph B owner T).degree a =
      ((T.erase a.1).filter fun b =>
        ∃ y ∈ B a.1, y ∈ B b ∧ (owner y).card = 1).card := by
  classical
  let H := privatePairGraph B owner T
  letI : DecidableRel H.Adj := Classical.decRel _
  let Q := (T.erase a.1).filter fun b =>
    ∃ y ∈ B a.1, y ∈ B b ∧ (owner y).card = 1
  rw [← H.card_neighborFinset_eq_degree]
  change (H.neighborFinset a).card = Q.card
  apply Finset.card_bij (fun b _hb => b.1)
  · intro b hb
    have hab : H.Adj a b := (H.mem_neighborFinset a b).mp hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, b.2⟩, hab.2⟩
    exact fun h => hab.1 (Subtype.ext h.symm)
  · intro b hb c hc hbc
    exact Subtype.ext hbc
  · intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbErase := Finset.mem_erase.mp hbData.1
    let bb : {b // b ∈ T} := ⟨b, hbErase.2⟩
    have hab : H.Adj a bb := ⟨by
      intro habEq
      exact hbErase.1 (congrArg Subtype.val habEq).symm, hbData.2⟩
    refine ⟨bb, (H.mem_neighborFinset a bb).mpr hab, rfl⟩

/-- At minimum hole mass, the private-pair graph has the row-hole degree
sequence and exactly `m` edges. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privatePairGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      (∑ w ∈ T, (K w).card) = q →
      let H := privatePairGraph B owner T
      (∀ w, H.degree w = (K w.1).card) ∧ H.edgeFinset.card = m := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard hmass
  let H := privatePairGraph B owner T
  letI : DecidableRel H.Adj := Classical.decRel _
  have hprivate :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privatePairDegree
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri T heven hTcard
  have hdegree : ∀ w : {w // w ∈ T}, H.degree w = (K w.1).card := by
    intro w
    rw [privatePairGraph_degree_eq_filter_card]
    simpa [H, B, owner, K, F] using hprivate w.1 w.2
  refine ⟨hdegree, ?_⟩
  have hsumDeg : (∑ w, H.degree w) = q := by
    calc
      (∑ w, H.degree w) = ∑ w : {w // w ∈ T}, (K w.1).card := by
        apply Finset.sum_congr rfl
        intro w _hw
        exact hdegree w
      _ = ∑ w ∈ T, (K w).card := by
        symm
        exact Finset.sum_subtype T (fun _ => Iff.rfl) fun w => (K w).card
      _ = q := by simpa [K, F] using hmass
  have hhandshake := H.sum_degrees_eq_twice_card_edges
  rw [hsumDeg, hqm] at hhandshake
  change H.edgeFinset.card = m
  omega

end

end Erdos85

#print axioms Erdos85.privatePairGraph_degree_eq_filter_card
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privatePairGraph
