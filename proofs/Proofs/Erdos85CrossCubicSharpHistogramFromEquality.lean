import Proofs.Erdos85CrossCubicFiberBounds
import Proofs.Erdos85CrossCubicEqualityLocalization
import Proofs.Erdos85CubicResidualFiberEqualityPatterns

/-! # Sharp cross histograms from equality in the cubic row bound -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
private theorem h305_offset_class_iff : ∀ i k : ZMod 8,
    (k ∈ h305CubicOffsetOneCoordinates i ↔
      (i = k - 1 ∨ i = k + 1)) ∧
    (k ∈ h305CubicOffsetThreeCoordinates i ↔
      (i = k - 3 ∨ i = k + 3)) := by
  native_decide

/-- The three coordinate classes are exactly the three service-budget
classes `(25,0)`, `(27,1)`, and `(28,1)`. -/
theorem h305_cross_cubicBudget_neighborCard_by_class
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j}) :
    let X25 := h305CrossCubicOffsetOneVertices u v i j
    let X16 := h305CrossCubicOffsetThreeVertices u v i j
    let X17 := h305CrossCubicRemainingVertices u v i j
    (∀ x ∈ X25, incidentServiceCubicWalkMass R Cedge x a = 25 ∧
      (incidentServiceNeighborFiber R Cedge x a).card = 0) ∧
    (∀ x ∈ X16, incidentServiceCubicWalkMass R Cedge x a = 27 ∧
      (incidentServiceNeighborFiber R Cedge x a).card = 1) ∧
    (∀ x ∈ X17, incidentServiceCubicWalkMass R Cedge x a = 28 ∧
      (incidentServiceNeighborFiber R Cedge x a).card = 1) := by
  classical
  dsimp only
  have shore_u (k : ZMod 8) := cross_oneShore_cubicBudget_neighborCard
    H R Cedge hservice hHreg hCreg u huinj hu (v j)
      (fun q ↦ hdisj q j) (fun q ↦ hzeroUV q j) a i k ha
  have ha' : a.1.toFinset = {v j, u i} := by
    simpa [Finset.pair_comm] using ha
  have shore_v (k : ZMod 8) := cross_oneShore_cubicBudget_neighborCard
    H R Cedge hservice hHreg hCreg v hvinj hv (u i)
      (fun q ↦ (hdisj i q).symm) (fun q ↦ hzeroVU i q) a j k ha'
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hn := (h305_offset_class_iff i k).1.mp hk
      simpa [hn] using shore_u k
    · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hn := (h305_offset_class_iff j k).1.mp hk
      simpa [hn] using shore_v k
  · constructor
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hf := (h305_offset_class_iff i k).2.mp hk
        have hn : ¬ (i = k - 1 ∨ i = k + 1) := by
          intro hn
          exact Finset.disjoint_left.mp
            (h305CubicCoordinatePartition_finiteFacts i).2.2.2.1
            ((h305_offset_class_iff i k).1.mpr hn) hk
        simpa [hn, hf] using shore_u k
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hf := (h305_offset_class_iff j k).2.mp hk
        have hn : ¬ (j = k - 1 ∨ j = k + 1) := by
          intro hn
          exact Finset.disjoint_left.mp
            (h305CubicCoordinatePartition_finiteFacts j).2.2.2.1
            ((h305_offset_class_iff j k).1.mpr hn) hk
        simpa [hn, hf] using shore_v k
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk' := Finset.mem_sdiff.mp hk
        have hn : ¬ (i = k - 1 ∨ i = k + 1) := fun hn ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inl ((h305_offset_class_iff i k).1.mpr hn)))
        have hf : ¬ (i = k - 3 ∨ i = k + 3) := fun hf ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inr ((h305_offset_class_iff i k).2.mpr hf)))
        simpa [hn, hf] using shore_u k
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk' := Finset.mem_sdiff.mp hk
        have hn : ¬ (j = k - 1 ∨ j = k + 1) := fun hn ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inl ((h305_offset_class_iff j k).1.mpr hn)))
        have hf : ¬ (j = k - 3 ∨ j = k + 3) := fun hf ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inr ((h305_offset_class_iff j k).2.mpr hf)))
        simpa [hn, hf] using shore_v k

set_option maxHeartbeats 800000 in
/-- Exact cross-row mass `550` supplies both hypotheses of the sharp marked
matching package: every exceptional histogram has moments `6/25/105`, and
every nonexceptional vertex has no value-five residual edge. -/
theorem h305_cross_mass_eq_550_sharpHistograms
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j})
    (hmass : ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 550) :
    (∀ x ∈ h305CrossCubicExceptionalCoordinates u v i j,
      let c := cubicResidualFiberHistogram R Cedge x a
      (∑ t ∈ Finset.range 7, c t) = 6 ∧
        (∑ t ∈ Finset.range 7, t * c t) = 25 ∧
        (∑ t ∈ Finset.range 7, t ^ 2 * c t) ≤ 105) ∧
    (∀ x ∉ h305CrossCubicExceptionalCoordinates u v i j,
      cubicResidualFiberHistogram R Cedge x a 5 = 0) := by
  classical
  let X25 := h305CrossCubicOffsetOneVertices u v i j
  let X16 := h305CrossCubicOffsetThreeVertices u v i j
  let X17 := h305CrossCubicRemainingVertices u v i j
  obtain ⟨h25card, h16card, h17card, h2516, h2517, h1617, hpart⟩ :=
    h305CrossCubicCoordinatePartition u v huinj hvinj hdisj hcover i j
  obtain ⟨hl25, hl16, hl17⟩ :=
    h305_cross_cubicResidualFiber_pointwise_bounds
      H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
        hdisj hzeroUV hzeroVU a i j ha
  obtain ⟨heq25, heq16, heq17⟩ :=
    cubicResidualEdge_squareMass_eq_550_localizes
      R Cedge a X25 X16 X17 h25card h16card h17card h2516 h2517 h1617
        hpart hl25 hl16 hl17 hmass
  obtain ⟨hbudget25, hbudget16, hbudget17⟩ :=
    h305_cross_cubicBudget_neighborCard_by_class
      H R Cedge hservice hHreg hCreg u v huinj hvinj hu hv hdisj
        hzeroUV hzeroVU a i j ha
  have hX25 : h305CrossCubicExceptionalCoordinates u v i j = X25 := by
    ext x
    simp only [h305CrossCubicExceptionalCoordinates, X25,
      h305CrossCubicOffsetOneVertices, h305CubicOffsetOneCoordinates,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Finset.mem_image]
    aesop
  constructor
  · intro x hx
    have hx25 : x ∈ X25 := by simpa [← hX25] using hx
    let c := cubicResidualFiberHistogram R Cedge x a
    obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
      R Cedge hfree hCreg x a
    have hcn := cubicResidualFiber_card_add_neighbor_card R Cedge x a
    obtain ⟨hb, hn⟩ := hbudget25 x hx25
    have hsq := heq25 x hx25
    rw [hRreg, hn] at hcn
    rw [hb, hn] at hs
    dsimp only
    have hc6 : (∑ t ∈ Finset.range 7,
        cubicResidualFiberHistogram R Cedge x a t) = 6 := by
      have hc' := hc
      omega
    have hs25 : (∑ t ∈ Finset.range 7,
        t * cubicResidualFiberHistogram R Cedge x a t) = 25 := by
      have hs' := hs
      omega
    refine ⟨hc6, hs25, ?_⟩
    have hq' := hq
    rw [hq', hsq]
  · intro x hx
    have hxnot25 : x ∉ X25 := by simpa [← hX25] using hx
    have hxall : x ∈ X25 ∪ X16 ∪ X17 := by
      rw [hpart]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxall with hx2516 | hx17
    · rcases Finset.mem_union.mp hx2516 with hx25 | hx16
      · exact (hxnot25 hx25).elim
      · obtain ⟨hb, hn⟩ := hbudget16 x hx16
        have hp := cubicResidualFiberHistogram_eq_pattern_16
          R Cedge hfree hRreg hCreg x a hb hn (by
            rw [heq16 x hx16])
        exact hp.2.2.2.2.2.1
    · obtain ⟨hb, hn⟩ := hbudget17 x hx17
      have hp := cubicResidualFiberHistogram_eq_pattern_17
        R Cedge hfree hRreg hCreg x a hb hn (by
          rw [heq17 x hx17])
      exact hp.2.2.2.2.2.1

end

end Erdos85

#print axioms Erdos85.h305_cross_cubicBudget_neighborCard_by_class
#print axioms Erdos85.h305_cross_mass_eq_550_sharpHistograms
