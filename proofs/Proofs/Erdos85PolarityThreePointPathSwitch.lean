import Proofs.Erdos85PolarityThreePointCore

/-! The simultaneous two-arm pair-pole path and its degree obstruction. -/

open SimpleGraph

namespace Erdos85

def twoArmCrossEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y z : V) : Set (Sym2 V) :=
  crossEdgeSet (H.neighborFinset x) (H.neighborFinset y) ∪
    crossEdgeSet (H.neighborFinset x) (H.neighborFinset z)

def twoArmPathSwitch {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y z : V) : SimpleGraph V :=
  H.deleteEdges (twoArmCrossEdgeSet H x y z) ⊔
    SimpleGraph.edge x y ⊔ SimpleGraph.edge x z

/-- Two distinct incident edges selected by the two-arm deletion force a
two-unit degree drop away from the three path endpoints. -/
theorem twoArmPathSwitch_degree_add_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y z v r s : V)
    [DecidableRel (twoArmPathSwitch H x y z).Adj]
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z)
    (hrs : r ≠ s) (hvr : H.Adj v r) (hvs : H.Adj v s)
    (hrdel : s(v,r) ∈ twoArmCrossEdgeSet H x y z)
    (hsdel : s(v,s) ∈ twoArmCrossEdgeSet H x y z) :
    (twoArmPathSwitch H x y z).degree v + 2 ≤ H.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  let R := ((H.neighborFinset v).erase r).erase s
  have hsub : (twoArmPathSwitch H x y z).neighborFinset v ⊆ R := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    simp only [twoArmPathSwitch, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hu
    rcases hu with (hold | hxy) | hxz
    · have hold' := SimpleGraph.deleteEdges_adj.mp hold
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, by simpa only [SimpleGraph.mem_neighborFinset] using hold'.1⟩
      · intro hus
        subst u
        exact hold'.2 hsdel
      · intro hur
        subst u
        exact hold'.2 hrdel
    · rcases hxy.1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hvx h).elim
      · exact (hvy h).elim
    · rcases hxz.1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hvx h).elim
      · exact (hvz h).elim
  have hcard := Finset.card_le_card hsub
  have hrr : r ∈ H.neighborFinset v := by simpa using hvr
  have hss : s ∈ (H.neighborFinset v).erase r := by
    rw [Finset.mem_erase]
    exact ⟨hrs.symm, by simpa using hvs⟩
  have htwo : 2 ≤ (H.neighborFinset v).card := by
    have hpair : ({r,s} : Finset V) ⊆ H.neighborFinset v := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hrr
      · simpa using hvs
    have hc := Finset.card_le_card hpair
    simpa [hrs] using hc
  dsimp only [R] at hcard
  rw [Finset.card_erase_of_mem hss,
    Finset.card_erase_of_mem hrr] at hcard
  omega

end Erdos85

open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

/-- The simultaneous path on the three pair poles drops every clean center
neighbor from degree `q+1` to at most `q-1`. -/
theorem threePairPolePathSwitch_cleanCenter_degree_le_sub_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c))
    [DecidableRel (twoArmPathSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
      (threePointOuterPairDefectBC K ha hb hc hbc)).Adj] :
    (twoArmPathSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
      (threePointOuterPairDefectBC K ha hb hc hbc)).degree v ≤ Nat.card K - 1 := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointPairDefect K ha hb hc hab
  let y : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointOuterPairDefectAC K ha hb hc hac
  let z : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointOuterPairDefectBC K ha hb hc hbc
  obtain ⟨r, s, hrs, hvr, hry, hvs, hsz⟩ :=
    exists_two_distinct_outer_cross_edges_of_cleanCenter K
      h2 ha hb hc hab hac hbc v hv
  have hvxAdj : H.Adj v x := by
    rw [SimpleGraph.induce_adj]
    have hvm := Finset.mem_sdiff.mp hv
    have hvbase := (Finset.mem_sdiff.mp hvm.1).1
    have hadj := ((graph K).mem_neighborFinset
      (absolutePairCommonNeighbor K ha hb hab) v.1).mp hvbase
    simpa [H, x, threePointPairDefect] using hadj.symm
  have hvx : v ≠ x := fun h => H.loopless.irrefl v (by simpa [h] using hvxAdj)
  have hvy : v ≠ y := by
    intro heq
    have hvm := Finset.mem_sdiff.mp hv
    have hvnc : ¬ (graph K).Adj c v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    exact hvnc (by simpa [y, threePointOuterPairDefectAC, heq] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.1)
  have hvz : v ≠ z := by
    intro heq
    have hvm := Finset.mem_sdiff.mp hv
    have hvnc : ¬ (graph K).Adj c v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    exact hvnc (by simpa [z, threePointOuterPairDefectBC, heq] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.1)
  have hvNx : v ∈ H.neighborFinset x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hvxAdj.symm
  have hrdel : s(v,r) ∈ twoArmCrossEdgeSet H x y z := by
    apply Set.mem_union_left
    rw [pair_mem_crossEdgeSet_iff]
    exact Or.inl ⟨hvNx, hry⟩
  have hsdel : s(v,s) ∈ twoArmCrossEdgeSet H x y z := by
    apply Set.mem_union_right
    rw [pair_mem_crossEdgeSet_iff]
    exact Or.inl ⟨hvNx, hsz⟩
  have hdrop := twoArmPathSwitch_degree_add_two_le H x y z v r s
    hvx hvy hvz hrs hvr hvs hrdel hsdel
  have hvdeg := threePointCore_degree_of_mem_pairPoleCleanCenterNeighbors K
    h2 ha hb hc hab (Ne.symm hac) (Ne.symm hbc) v hv
  change H.degree v = Nat.card K + 1 at hvdeg
  change (twoArmPathSwitch H x y z).degree v ≤ Nat.card K - 1
  have hq := three_le_card_of_two_ne_zero K h2
  omega

/-- Consequently the simultaneous pair-pole path never reaches target
minimum degree `q`: its minimum degree is at most `q-1`. -/
theorem threePairPolePathSwitch_minDegree_le_sub_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableRel (twoArmPathSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
      (threePointOuterPairDefectBC K ha hb hc hbc)).Adj] :
    (twoArmPathSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
      (threePointOuterPairDefectBC K ha hb hc hbc)).minDegree ≤ Nat.card K - 1 := by
  classical
  have hcard := pairPoleCleanCenterNeighbors_card K h2
    ha hb hc hab (Ne.symm hac) (Ne.symm hbc)
  have hq := three_le_card_of_two_ne_zero K h2
  have hpos : 0 < (pairPoleCleanCenterNeighbors K ha hb hab (c := c)).card := by
    rw [hcard]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hpD : p ∉ ({a,b,c} : Finset (P K)) :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).2
  let v : {v : P K // v ∉ ({a,b,c} : Finset (P K))} := ⟨p, hpD⟩
  exact ((twoArmPathSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
    (threePointOuterPairDefectBC K ha hb hc hbc)).minDegree_le_degree v).trans
      (threePairPolePathSwitch_cleanCenter_degree_le_sub_one K
        h2 ha hb hc hab hac hbc v (by simpa [v] using hp))

end Erdos85.Polarity
