import Proofs.Erdos85SizeTwoUnorderedPairOwnHitDistinct
import Proofs.Erdos85ExteriorPairTwoRegularOwnCount

/-! # The literal own-pair exterior-neighbour count -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exterior neighbours of `u` whose selected pair contains the internal
vertex `z`, expressed directly through ambient adjacency. -/
def outsideEndpointHitFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (u : {x : V // x ∉ c.supp}) (z : c.supp) :
    Finset {x : V // x ∉ c.supp} :=
  Finset.univ.filter fun v ↦ G.Adj u.1 v.1 ∧ G.Adj z.1 v.1

/-- Exterior neighbours of an owner that serve at least one endpoint of its
displayed unordered pair. -/
def outsideOwnPairNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (u : {x : V // x ∉ c.supp}) (z z' : c.supp) :
    Finset {x : V // x ∉ c.supp} :=
  outsideEndpointHitFinset G c u z ∪
    outsideEndpointHitFinset G c u z'

@[simp] theorem mem_outsideEndpointHitFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (u v : {x : V // x ∉ c.supp}) (z : c.supp) :
    v ∈ outsideEndpointHitFinset G c u z ↔
      G.Adj u.1 v.1 ∧ G.Adj z.1 v.1 := by
  simp [outsideEndpointHitFinset]

@[simp] theorem mem_outsideOwnPairNeighborFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (u v : {x : V // x ∉ c.supp}) (z z' : c.supp) :
    v ∈ outsideOwnPairNeighborFinset G c u z z' ↔
      G.Adj u.1 v.1 ∧ (G.Adj z.1 v.1 ∨ G.Adj z'.1 v.1) := by
  simp only [outsideOwnPairNeighborFinset, Finset.mem_union,
    mem_outsideEndpointHitFinset_iff]
  tauto

/-- Pair-language form: membership means that `v` is an exterior neighbour
of `u` and their two selected unordered pairs intersect. -/
theorem mem_outsideOwnPairNeighborFinset_iff_outsidePair_intersects
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (u v : {x : V // x ∉ c.supp}) (z z' : c.supp)
    (hpair : (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset =
      {z, z'}) :
    v ∈ outsideOwnPairNeighborFinset G c u z z' ↔
      G.Adj u.1 v.1 ∧ ∃ x,
        x ∈ (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset ∧
        x ∈ (outsidePair G (secondOrderDefectGraph G) c hcard v).toFinset := by
  rw [mem_outsideOwnPairNeighborFinset_iff]
  constructor
  · rintro ⟨huv, hzx | hz'x⟩
    · refine ⟨huv, z, ?_, ?_⟩
      · rw [hpair]
        simp
      · exact (mem_outsidePair_toFinset_iff_adj
          G (secondOrderDefectGraph G) c hcard v z).mpr hzx
    · refine ⟨huv, z', ?_, ?_⟩
      · rw [hpair]
        simp
      · exact (mem_outsidePair_toFinset_iff_adj
          G (secondOrderDefectGraph G) c hcard v z').mpr hz'x
  · rintro ⟨huv, x, hxu, hxv⟩
    have hxPair := (mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard v x).mp hxv
    rw [hpair] at hxu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxu
    rcases hxu with rfl | rfl
    · exact ⟨huv, Or.inl hxPair⟩
    · exact ⟨huv, Or.inr hxPair⟩

/-- The literal own-pair neighbour count is zero for an occupied internal
edge and two for an occupied internal nonedge. -/
theorem outsideOwnPairNeighborFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (u : {x : V // x ∉ c.supp}) (z z' : c.supp)
    (hpair : (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset =
      {z, z'}) (hzz' : z ≠ z') :
    (outsideOwnPairNeighborFinset G c u z z').card =
      if (G.induce c.supp).Adj z z' then 0 else 2 := by
  let F := fun x : c.supp ↦ outsideEndpointHitFinset G c u x
  have endpoint_card_one (x : c.supp)
      (hex : ∃! y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj x.1 y) :
      (F x).card = 1 := by
    obtain ⟨y, hy, hyuniq⟩ := hex
    let v : {w : V // w ∉ c.supp} := ⟨y, hy.2.1⟩
    rw [Finset.card_eq_one]
    refine ⟨v, ?_⟩
    ext w
    simp only [Finset.mem_singleton, F, mem_outsideEndpointHitFinset_iff]
    constructor
    · intro hw
      apply Subtype.ext
      exact hyuniq w.1 ⟨hw.1, w.2, hw.2⟩
    · intro hw
      subst w
      exact ⟨hy.1, hy.2.2⟩
  have endpoint_eq_empty (x : c.supp)
      (hno : ¬ ∃ y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj x.1 y) :
      F x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hno ⟨v.1,
      (mem_outsideEndpointHitFinset_iff G c u v x).mp hv |>.1,
      v.2,
      (mem_outsideEndpointHitFinset_iff G c u v x).mp hv |>.2⟩
  have hend := outsidePair_endpoint_unique_hits_iff_not_adj
    G hfree c hcard u z z' hpair
  by_cases hadj : (G.induce c.supp).Adj z z'
  · rw [if_pos hadj]
    have hnoz : ¬ ∃ y,
        G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj z.1 y := by
      intro hex
      have huniq :=
        (exists_exterior_common_iff_no_internal_common G hfree c z.2 u.2).2 hex
      exact (hend.1.mp huniq) hadj
    have hnoz' : ¬ ∃ y,
        G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj z'.1 y := by
      intro hex
      have huniq :=
        (exists_exterior_common_iff_no_internal_common G hfree c z'.2 u.2).2 hex
      exact (hend.2.mp huniq) hadj
    have hz0 := endpoint_eq_empty z hnoz
    have hz'0 := endpoint_eq_empty z' hnoz'
    change (F z ∪ F z').card = 0
    rw [hz0, hz'0]
    simp
  · rw [if_neg hadj]
    have hz1 := endpoint_card_one z (hend.1.mpr hadj)
    have hz'1 := endpoint_card_one z' (hend.2.mpr hadj)
    have hdisj : Disjoint (F z) (F z') := by
      apply Finset.disjoint_left.mpr
      intro v hvz hvz'
      have hvzData := (mem_outsideEndpointHitFinset_iff G c u v z).mp hvz
      have hvz'Data := (mem_outsideEndpointHitFinset_iff G c u v z').mp hvz'
      exact (outsidePair_endpoint_exterior_common_ne
        G hfree c hcard u z z' hpair hzz'
        ⟨hvzData.1, v.2, hvzData.2⟩
        ⟨hvz'Data.1, v.2, hvz'Data.2⟩) rfl
    change (F z ∪ F z').card = 2
    rw [Finset.card_union_of_disjoint hdisj, hz1, hz'1]

#print axioms Erdos85.outsideOwnPairNeighborFinset_card

end

end Erdos85
