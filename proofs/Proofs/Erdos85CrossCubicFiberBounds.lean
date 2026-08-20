import Proofs.Erdos85CrossCubicCoordinatePartition
import Proofs.Erdos85CubicResidualFiberMinima
import Proofs.Erdos85CubicResidualRowLowerBound
import Proofs.Erdos85EdgeIndexedServiceCubicEightCycleCensus

/-! # Cubic residual-fiber bounds for a cross-shore target -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For a target with one endpoint on a C8 shore and the other endpoint
outside that internal component, only the same-shore endpoint contributes to
the internal cubic census. -/
theorem internalEndpointCubicWalkMass_cross_oneShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (w : V) (huw : ∀ k, u k ≠ w)
    (hcrosszero : ∀ k,
      Fintype.card {p : H.Walk (u k) w | p.length = 3} = 0)
    (a : R.edgeFinset) (i k : ZMod 8)
    (ha : a.1.toFinset = {u i, w}) :
    internalEndpointCubicWalkMass H R (u k) a =
      if i = k - 1 ∨ i = k + 1 then 3
      else if i = k - 3 ∨ i = k + 3 then 1 else 0 := by
  classical
  unfold internalEndpointCubicWalkMass
  rw [ha, ← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun x : V ↦
      x ∈ ({u i, w} : Finset V)) = {u i, w} := by
    ext x
    simp
  change (∑ x ∈ Finset.univ.filter (fun x : V ↦
      x ∈ ({u i, w} : Finset V)),
        Fintype.card {p : H.Walk (u k) x | p.length = 3}) = _
  rw [hfilter, Finset.sum_pair (huw i),
    eightCycle_lengthThreeWalk_card H u huinj hu k i,
    hcrosszero k]
  omega

/-- The corresponding internal neighbor count is one exactly at cyclic
offset `±1`. -/
theorem internalEndpointNeighbor_card_cross_oneShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (w : V) (huw : ∀ k, u k ≠ w)
    (a : R.edgeFinset) (i k : ZMod 8)
    (ha : a.1.toFinset = {u i, w}) :
    (internalEndpointNeighborFinset H R (u k) a).card =
      if i = k - 1 ∨ i = k + 1 then 1 else 0 := by
  classical
  have hui : H.Adj (u k) (u i) ↔ i = k - 1 ∨ i = k + 1 := by
    rw [← H.mem_neighborFinset, hu k]
    simp [huinj.eq_iff]
  have huwAdj : ¬ H.Adj (u k) w := by
    intro h
    have hm := (H.mem_neighborFinset (u k) w).mpr h
    rw [hu k] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact huw (k - 1) hm.symm
    · exact huw (k + 1) (Finset.mem_singleton.mp hm).symm
  unfold internalEndpointNeighborFinset
  rw [ha]
  by_cases hn : H.Adj (u k) (u i)
  · rw [if_pos (hui.mp hn)]
    have heq : ({u i, w} : Finset V).filter (H.Adj (u k)) = {u i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact (huwAdj hx).elim
      · intro hx
        subst x
        exact ⟨Or.inl rfl, hn⟩
    rw [heq]
    simp
  · rw [if_neg (fun h ↦ hn (hui.mpr h))]
    have heq : ({u i, w} : Finset V).filter (H.Adj (u k)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl)
      · exact hn
      · exact huwAdj
    rw [heq]
    simp

/-- Exact service cubic budget and residual-neighbor count on one shore of a
cross target. -/
theorem cross_oneShore_cubicBudget_neighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hCreg : ∀ b, Cedge.degree b = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (w : V) (huw : ∀ k, u k ≠ w)
    (hcrosszero : ∀ k,
      Fintype.card {p : H.Walk (u k) w | p.length = 3} = 0)
    (a : R.edgeFinset) (i k : ZMod 8)
    (ha : a.1.toFinset = {u i, w}) :
    let near := i = k - 1 ∨ i = k + 1
    let far := i = k - 3 ∨ i = k + 3
    (incidentServiceCubicWalkMass R Cedge (u k) a =
        (if near then 25 else if far then 27 else 28)) ∧
      (incidentServiceNeighborFiber R Cedge (u k) a).card =
        if near then 0 else 1 := by
  dsimp only
  have hcensus := edgeIndexedService_cubicWalkCensus
    H R Cedge hservice hHreg hCreg (u k) a
  rw [internalEndpointCubicWalkMass_cross_oneShore
    H R u huinj hu w huw hcrosszero a i k ha] at hcensus
  have hlaw :=
    internalEndpointNeighbor_card_add_incidentServiceNeighborFiber_card
      H R Cedge hservice (u k) a
  rw [internalEndpointNeighbor_card_cross_oneShore
    H R u huinj hu w huw a i k ha] at hlaw
  split_ifs at hcensus hlaw ⊢ <;> omega

set_option maxRecDepth 100000 in
private theorem offset_membership_facts : ∀ i k : ZMod 8,
    (k ∈ h305CubicOffsetOneCoordinates i ↔
      (i = k - 1 ∨ i = k + 1)) ∧
    (k ∈ h305CubicOffsetThreeCoordinates i ↔
      (i = k - 3 ∨ i = k + 3)) := by
  native_decide

/-- Pointwise sharp lower bounds on all three coordinate classes of a cross
target. The two `hzero` hypotheses are the explicit no-internal-walk bridge
between the two C8 components. -/
theorem h305_cross_cubicResidualFiber_pointwise_bounds
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
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j}) :
    let X25 := h305CrossCubicOffsetOneVertices u v i j
    let X16 := h305CrossCubicOffsetThreeVertices u v i j
    let X17 := h305CrossCubicRemainingVertices u v i j
    (∀ x ∈ X25, 105 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ∧
    (∀ x ∈ X16, 52 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ∧
    (∀ x ∈ X17, 59 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) := by
  classical
  dsimp only
  -- Each class is the union of its two shore images; the two shores use the
  -- same one-shore census after swapping the target endpoint order.
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hnear := (offset_membership_facts i k).1.mp hk
      obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
        H R Cedge hservice hHreg hCreg u huinj hu (v j)
        (fun q ↦ hdisj q j) (fun q ↦ hzeroUV q j) a i k ha
      rw [if_pos hnear] at hmass hnbr
      exact cubicResidualFiber_squareMass_ge_105_of_budget25
        R Cedge hfree hRreg hCreg (u k) a hmass hnbr
    · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have hnear := (offset_membership_facts j k).1.mp hk
      have ha' : a.1.toFinset = {v j, u i} := by simpa [Finset.pair_comm] using ha
      obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
        H R Cedge hservice hHreg hCreg v hvinj hv (u i)
        (fun q ↦ (hdisj i q).symm) (fun q ↦ hzeroVU i q) a j k ha'
      rw [if_pos hnear] at hmass hnbr
      exact cubicResidualFiber_squareMass_ge_105_of_budget25
        R Cedge hfree hRreg hCreg (v k) a hmass hnbr
  · constructor
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hfar := (offset_membership_facts i k).2.mp hk
        have hnotnear : ¬ (i = k - 1 ∨ i = k + 1) := by
          intro hn
          exact Finset.disjoint_left.mp
            (h305CubicCoordinatePartition_finiteFacts i).2.2.2.1
            ((offset_membership_facts i k).1.mpr hn) hk
        obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
          H R Cedge hservice hHreg hCreg u huinj hu (v j)
          (fun q ↦ hdisj q j) (fun q ↦ hzeroUV q j) a i k ha
        rw [if_neg hnotnear, if_pos hfar] at hmass
        rw [if_neg hnotnear] at hnbr
        exact cubicResidualFiber_squareMass_ge_52_of_budget27_neighborOne
          R Cedge hfree hRreg hCreg (u k) a hmass hnbr
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hfar := (offset_membership_facts j k).2.mp hk
        have hnotnear : ¬ (j = k - 1 ∨ j = k + 1) := by
          intro hn
          exact Finset.disjoint_left.mp
            (h305CubicCoordinatePartition_finiteFacts j).2.2.2.1
            ((offset_membership_facts j k).1.mpr hn) hk
        have ha' : a.1.toFinset = {v j, u i} := by simpa [Finset.pair_comm] using ha
        obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
          H R Cedge hservice hHreg hCreg v hvinj hv (u i)
          (fun q ↦ (hdisj i q).symm) (fun q ↦ hzeroVU i q) a j k ha'
        rw [if_neg hnotnear, if_pos hfar] at hmass
        rw [if_neg hnotnear] at hnbr
        exact cubicResidualFiber_squareMass_ge_52_of_budget27_neighborOne
          R Cedge hfree hRreg hCreg (v k) a hmass hnbr
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk' := Finset.mem_sdiff.mp hk
        have hnotnear : ¬ (i = k - 1 ∨ i = k + 1) := fun hn ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inl ((offset_membership_facts i k).1.mpr hn)))
        have hnotfar : ¬ (i = k - 3 ∨ i = k + 3) := fun hf ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inr ((offset_membership_facts i k).2.mpr hf)))
        obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
          H R Cedge hservice hHreg hCreg u huinj hu (v j)
          (fun q ↦ hdisj q j) (fun q ↦ hzeroUV q j) a i k ha
        rw [if_neg hnotnear, if_neg hnotfar] at hmass
        rw [if_neg hnotnear] at hnbr
        exact cubicResidualFiber_squareMass_ge_59_of_budget28_neighborOne
          R Cedge hfree hRreg hCreg (u k) a hmass hnbr
      · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk' := Finset.mem_sdiff.mp hk
        have hnotnear : ¬ (j = k - 1 ∨ j = k + 1) := fun hn ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inl ((offset_membership_facts j k).1.mpr hn)))
        have hnotfar : ¬ (j = k - 3 ∨ j = k + 3) := fun hf ↦
          hk'.2 (Finset.mem_union.mpr
            (Or.inr ((offset_membership_facts j k).2.mpr hf)))
        have ha' : a.1.toFinset = {v j, u i} := by simpa [Finset.pair_comm] using ha
        obtain ⟨hmass, hnbr⟩ := cross_oneShore_cubicBudget_neighborCard
          H R Cedge hservice hHreg hCreg v hvinj hv (u i)
          (fun q ↦ (hdisj i q).symm) (fun q ↦ hzeroVU i q) a j k ha'
        rw [if_neg hnotnear, if_neg hnotfar] at hmass
        rw [if_neg hnotnear] at hnbr
        exact cubicResidualFiber_squareMass_ge_59_of_budget28_neighborOne
          R Cedge hfree hRreg hCreg (v k) a hmass hnbr

/-- Fully assembled cross-target row bound on the two-C8 h305 model. -/
theorem h305_cross_cubicResidualEdge_squareMass_ge_550
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
    (ha : a.1.toFinset = {u i, v j}) :
    550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let X25 := h305CrossCubicOffsetOneVertices u v i j
  let X16 := h305CrossCubicOffsetThreeVertices u v i j
  let X17 := h305CrossCubicRemainingVertices u v i j
  obtain ⟨h25card, h16card, h17card, h2516, h2517, h1617, hcover'⟩ :=
    h305CrossCubicCoordinatePartition
      u v huinj hvinj hdisj hcover i j
  obtain ⟨h25, h16, h17⟩ :=
    h305_cross_cubicResidualFiber_pointwise_bounds
      H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hzeroUV hzeroVU a i j ha
  exact cubicResidualEdge_squareMass_ge_550_of_partition
    R Cedge a X25 X16 X17 h25card h16card h17card h2516 h2517 h1617
      hcover' h25 h16 h17

/-- Length-three walks vanish between coordinates parametrizing distinct
connected components. -/
theorem lengthThreeWalk_card_eq_zero_of_distinct_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (k l : ZMod 8) :
    Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  constructor
  rintro ⟨p, hp⟩
  have huA : u k ∈ A.supp := by
    rw [← hurange]
    exact ⟨k, rfl⟩
  have hvB : v l ∈ B.supp := by
    rw [← hvrange]
    exact ⟨l, rfl⟩
  have hucomp : H.connectedComponentMk (u k) = A :=
    (ConnectedComponent.mem_supp_iff A (u k)).mp huA
  have hvcomp : H.connectedComponentMk (v l) = B :=
    (ConnectedComponent.mem_supp_iff B (v l)).mp hvB
  have hreach : H.connectedComponentMk (u k) =
      H.connectedComponentMk (v l) := ConnectedComponent.sound p.reachable
  exact hAB (hucomp.symm.trans (hreach.trans hvcomp))

/-- The cross residual-row bound with cross-walk vanishing discharged from
the actual distinct-component geometry. -/
theorem h305_cross_cubicResidualEdge_squareMass_ge_550_of_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j}) :
    550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  apply h305_cross_cubicResidualEdge_squareMass_ge_550
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover
  · exact fun k l ↦ lengthThreeWalk_card_eq_zero_of_distinct_components
      H A B hAB u v hurange hvrange k l
  · exact fun k l ↦ lengthThreeWalk_card_eq_zero_of_distinct_components
      H B A hAB.symm v u hvrange hurange l k
  · exact ha

end

end Erdos85

#print axioms Erdos85.internalEndpointCubicWalkMass_cross_oneShore
#print axioms Erdos85.cross_oneShore_cubicBudget_neighborCard
#print axioms Erdos85.h305_cross_cubicResidualFiber_pointwise_bounds
#print axioms Erdos85.h305_cross_cubicResidualEdge_squareMass_ge_550
#print axioms Erdos85.lengthThreeWalk_card_eq_zero_of_distinct_components
#print axioms
  Erdos85.h305_cross_cubicResidualEdge_squareMass_ge_550_of_components
