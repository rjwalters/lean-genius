import Proofs.Erdos85PolarityThreePointDynamicSwitch

open SimpleGraph
open scoped LinearAlgebra.Projectivization
namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

noncomputable def remainingPairPoleAnchor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    {v : P K // v ∉ ({a,b,c} : Finset (P K))} := by
  let r := pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc
    hab hac
  refine ⟨r, ?_⟩
  have hrnon : ¬ Projectivization.orthogonal r r := by
    exact pairPoleThirdAbsoluteAnchor_not_absolute K h2 hb hc ha hbc
      hab hac
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (hra | hrb | hrc)
  · exact hrnon (by simpa [hra] using ha)
  · exact hrnon (by simpa [hrb] using hb)
  · exact hrnon (by simpa [hrc] using hc)

theorem remainingPairPoleAnchor_adj_pairPole {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).Adj
      (threePointOuterPairDefectBC K ha hb hc hbc)
      (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) := by
  apply SimpleGraph.induce_adj.mpr
  have hm := (Finset.mem_inter.mp (pairPoleThirdAbsoluteAnchor_mem K h2
    hb hc ha hbc hab hac)).1
  simpa [threePointOuterPairDefectBC, remainingPairPoleAnchor] using
    ((graph K).mem_neighborFinset _ _).mp hm

theorem remainingPairPoleAnchor_adj_a {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (graph K).Adj a (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc).1 := by
  have hm := (Finset.mem_inter.mp (pairPoleThirdAbsoluteAnchor_mem K h2
    hb hc ha hbc hab hac)).2
  simpa [remainingPairPoleAnchor] using ((graph K).mem_neighborFinset _ _).mp hm

/-- The anchor lies on the tangent at `a`, while both first-switch pair poles
also lie on that tangent; hence neither pole is adjacent to the anchor. -/
theorem remainingPairPoleAnchor_not_adj_firstPairPoles {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (threePointCore K).Adj
        (threePointPairDefect K ha hb hc hab)
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) ∧
      ¬ (threePointCore K).Adj
        (threePointOuterPairDefectAC K ha hb hc hac)
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) := by
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  have hra := remainingPairPoleAnchor_adj_a K h2 ha hb hc hab hac hbc
  constructor
  · intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hxa : (graph K).Adj x.1 a := by
      simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hxa ha
    have hm : r.1 ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset a := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hra⟩
    rw [hempty] at hm
    simp at hm
  · intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hya : (graph K).Adj y.1 a := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hya ha
    have hm : r.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset a := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hra⟩
    rw [hempty] at hm
    simp at hm

/-- Every surviving absolute point lies in neither neighborhood used by the
first pair-pole switch. -/
theorem survivingAbsolute_not_adj_firstPairPoles {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c)
    (d : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hdabs : Projectivization.orthogonal d.1 d.1) :
    ¬ (threePointCore K).Adj (threePointPairDefect K ha hb hc hab) d ∧
      ¬ (threePointCore K).Adj
        (threePointOuterPairDefectAC K ha hb hc hac) d := by
  have hda : d.1 ≠ a := by intro h; exact d.2 (by simp [h])
  have hdb : d.1 ≠ b := by intro h; exact d.2 (by simp [h])
  have hdc : d.1 ≠ c := by intro h; exact d.2 (by simp [h])
  constructor
  · intro h
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab hdabs hda hdb)
        (by simpa [threePointPairDefect] using SimpleGraph.induce_adj.mp h)
  · intro h
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hc hac hdabs hda hdc)
        (by simpa [threePointOuterPairDefectAC] using SimpleGraph.induce_adj.mp h)

/-- The remaining pair pole lies in neither first-switch neighborhood. -/
theorem remainingPairPole_not_adj_firstPairPoles {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (threePointCore K).Adj (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectBC K ha hb hc hbc) ∧
      ¬ (threePointCore K).Adj (threePointOuterPairDefectAC K ha hb hc hac)
        (threePointOuterPairDefectBC K ha hb hc hbc) := by
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  constructor
  · intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hxb : (graph K).Adj x.1 b := by
      simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm
    have hzb : (graph K).Adj z.1 b := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hxb hb
    have hm : z.1 ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset b := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hzb.symm⟩
    rw [hem] at hm
    simp at hm
  · intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hyc : (graph K).Adj y.1 c := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm
    have hzc : (graph K).Adj z.1 c := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hyc hc
    have hm : z.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset c := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hzc.symm⟩
    rw [hem] at hm
    simp at hm

/-- The first `{a,b}` pole and remaining `{b,c}` pole have disjoint core
neighborhoods; their unique full-graph common neighbor `b` was deleted. -/
theorem firstPairPole_neighborFinset_inter_remainingPairPole_eq_empty
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab) ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectBC K ha hb hc hbc) = ∅ := by
  classical
  let x := threePointPairDefect K ha hb hc hab
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hne : x.1 ≠ z.1 := by
    intro h
    have hxa : (graph K).Adj a x.1 := by
      simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).1
    have hza := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    exact hza (by simpa [z, threePointOuterPairDefectBC, h] using hxa.symm)
  have hle := commonNeighbors_le_one x.1 z.1 hne
  rw [Finset.card_le_one_iff] at hle
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases Finset.mem_inter.mp ht with ⟨htx, htz⟩
  have htxb := SimpleGraph.induce_adj.mp
    ((threePointCore K).mem_neighborFinset x t |>.mp htx)
  have htzb := SimpleGraph.induce_adj.mp
    ((threePointCore K).mem_neighborFinset z t |>.mp htz)
  have hbm : b ∈ (graph K).neighborFinset x.1 ∩
      (graph K).neighborFinset z.1 := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨by simpa [x, threePointPairDefect] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm,
      by simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm⟩
  have htm : t.1 ∈ (graph K).neighborFinset x.1 ∩
      (graph K).neighborFinset z.1 := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨htxb, htzb⟩
  have htb : t.1 = b := hle htm hbm
  exact t.2 (by simp [htb])
theorem threePointCore_degree_remainingPairPoleAnchor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).degree
      (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) = Nat.card K := by
  classical
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hrz : (graph K).Adj z.1 r.1 := SimpleGraph.induce_adj.mp
    (remainingPairPoleAnchor_adj_pairPole K h2 ha hb hc hab hac hbc)
  have hra := remainingPairPoleAnchor_adj_a K h2 ha hb hc hab hac hbc
  have hrb : ¬ (graph K).Adj b r.1 := by
    intro hbr
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := z.1) (w := b)
      (by simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm) hb
    have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset b := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrz, hbr⟩
    rw [hempty] at hm
    simp at hm
  have hrc : ¬ (graph K).Adj c r.1 := by
    intro hcr
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := z.1) (w := c)
      (by simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm) hc
    have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset c := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrz, hcr⟩
    rw [hempty] at hm
    simp at hm
  have hinter : ((graph K).neighborFinset r.1 ∩
      ({a,b,c} : Finset (P K))).card = 1 := by
    have heq : (graph K).neighborFinset r.1 ∩
        ({a,b,c} : Finset (P K)) = {a} := by
      ext t
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨ht, rfl | rfl | rfl⟩
        · rfl
        · exact (hrb ht.symm).elim
        · exact (hrc ht.symm).elim
      · rintro rfl
        exact ⟨hra.symm, Or.inl rfl⟩
    rw [heq]
    simp
  have hrnon : ¬ Projectivization.orthogonal r.1 r.1 := by
    change ¬ Projectivization.orthogonal
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
    exact pairPoleThirdAbsoluteAnchor_not_absolute K h2 hb hc ha hbc hab hac
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) r
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hrnon] at hs
  change (threePointCore K).degree r + _ = Nat.card K + 1 at hs
  rw [hinter] at hs
  simp at hs
  omega

theorem remainingPairPoleAnchor_ne_firstPairPoles {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    remainingPairPoleAnchor K h2 ha hb hc hab hac hbc ≠
        threePointPairDefect K ha hb hc hab ∧
      remainingPairPoleAnchor K h2 ha hb hc hab hac hbc ≠
        threePointOuterPairDefectAC K ha hb hc hac := by
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hzr : (threePointCore K).Adj z r := by
    exact remainingPairPoleAnchor_adj_pairPole K h2 ha hb hc hab hac hbc
  have hzx : ¬ (threePointCore K).Adj z x := by
    intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hzb : (graph K).Adj z.1 b := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm
    have hxb : (graph K).Adj x.1 b := by
      simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hzb hb
    have hm : x.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset b := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hxb.symm⟩
    rw [hempty] at hm
    simp at hm
  have hzy : ¬ (threePointCore K).Adj z y := by
    intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hzc : (graph K).Adj z.1 c := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm
    have hyc : (graph K).Adj y.1 c := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hzc hc
    have hm : y.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset c := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hyc.symm⟩
    rw [hempty] at hm
    simp at hm
  constructor
  · intro h
    have h' : r = x := by simpa [r, x] using h
    exact hzx (h' ▸ hzr)
  · intro h
    have h' : r = y := by simpa [r, y] using h
    exact hzy (h' ▸ hzr)

theorem firstPairPoleSwitch_degree_remainingPairPoleAnchor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).degree
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) = Nat.card K := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  have hra := remainingPairPoleAnchor_adj_a K h2 ha hb hc hab hac hbc
  have hxr : ¬ H.Adj x r := by
    intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hxa : (graph K).Adj x.1 a := by
      simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hxa ha
    have hm : r.1 ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset a := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hra⟩
    rw [hempty] at hm
    simp at hm
  have hyr : ¬ H.Adj y r := by
    intro h
    have hbase := SimpleGraph.induce_adj.mp h
    have hya : (graph K).Adj y.1 a := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).1.symm
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) hya ha
    have hm : r.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset a := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, hra⟩
    rw [hempty] at hm
    simp at hm
  have hloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) r = 0 := by
    apply crossEdgeLoss_eq_zero_of_not_mem <;>
      simpa only [SimpleGraph.mem_neighborFinset]
  have hbase : H.degree r = Nat.card K := by
    exact threePointCore_degree_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  have hD : D.degree r = Nat.card K := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) r
    change H.degree r = D.degree r + _ at hs
    rw [hbase, hloss] at hs
    omega
  have hrne := remainingPairPoleAnchor_ne_firstPairPoles K h2 ha hb hc
    hab hac hbc
  rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints H x y r
    (by simpa [r, x] using hrne.1) (by simpa [r, y] using hrne.2)]
  exact hD

/-- The first switch does not delete the edge from the remaining pair-pole
defect to its canonical tight anchor. -/
theorem firstPairPoleSwitch_adj_remainingPairPoleAnchor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj
        (threePointOuterPairDefectBC K ha hb hc hbc)
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  have hzr : H.Adj z r := by
    exact remainingPairPoleAnchor_adj_pairPole K h2 ha hb hc hab hac hbc
  have hnot := remainingPairPoleAnchor_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc
  rw [crossEdgeSwitch_adj_iff]
  left
  refine ⟨hzr, ?_⟩
  rw [pair_mem_crossEdgeSet_iff]
  simp only [SimpleGraph.mem_neighborFinset]
  push Not
  exact ⟨fun _ => hnot.2, fun _ => hnot.1⟩

/-- No edge incident to the canonical anchor is changed by the first switch. -/
theorem firstPairPoleSwitch_adj_anchor_iff {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))}) :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) w ↔
      (threePointCore K).Adj
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) w := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  have hnot := remainingPairPoleAnchor_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hrne := remainingPairPoleAnchor_ne_firstPairPoles K h2 ha hb hc
    hab hac hbc
  change (crossEdgeSwitch H x y).Adj r w ↔ H.Adj r w
  have hxrn : ¬ H.Adj x r := hnot.1
  have hyrn : ¬ H.Adj y r := hnot.2
  have hrx : r ≠ x := hrne.1
  have hry : r ≠ y := hrne.2
  rw [crossEdgeSwitch_adj_iff, pair_mem_crossEdgeSet_iff]
  simp only [SimpleGraph.mem_neighborFinset]
  simp [hxrn, hyrn, hrx, hry]

/-- A neighbor of the anchor other than `a` is adjacent to neither first
pair pole; otherwise those two nonabsolute points would have both `a` and
that neighbor as common neighbors. -/
theorem anchor_neighbor_not_adj_firstPairPoles {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (t : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hrt : (threePointCore K).Adj
      (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) t) :
    ¬ (threePointCore K).Adj (threePointPairDefect K ha hb hc hab) t ∧
      ¬ (threePointCore K).Adj
        (threePointOuterPairDefectAC K ha hb hc hac) t := by
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  have hrtbase := SimpleGraph.induce_adj.mp hrt
  have hra := remainingPairPoleAnchor_adj_a K h2 ha hb hc hab hac hbc
  have hrne := remainingPairPoleAnchor_ne_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hta : t.1 ≠ a := by
    intro h
    exact t.2 (by simp [h])
  constructor
  · intro hxt
    have hbase := SimpleGraph.induce_adj.mp hxt
    have hne : r.1 ≠ x.1 := by
      intro h
      exact hrne.1 (Subtype.ext h)
    have hle := commonNeighbors_le_one r.1 x.1 hne
    rw [Finset.card_le_one_iff] at hle
    have ham : a ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset x.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hra.symm, by simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).1.symm⟩
    have htm : t.1 ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset x.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrtbase, hbase⟩
    exact hta (hle htm ham)
  · intro hyt
    have hbase := SimpleGraph.induce_adj.mp hyt
    have hne : r.1 ≠ y.1 := by
      intro h
      exact hrne.2 (Subtype.ext h)
    have hle := commonNeighbors_le_one r.1 y.1 hne
    rw [Finset.card_le_one_iff] at hle
    have ham : a ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset y.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hra.symm, by simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).1.symm⟩
    have htm : t.1 ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset y.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrtbase, hbase⟩
    exact hta (hle htm ham)

/-- Every old edge ending at a surviving neighbor of the anchor survives the
first switch. -/
theorem firstPairPoleSwitch_adj_of_adj_anchor_neighbor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w t : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hwt : (threePointCore K).Adj w t)
    (hrt : (threePointCore K).Adj
      (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) t) :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj w t := by
  classical
  have hnot := anchor_neighbor_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc t hrt
  rw [crossEdgeSwitch_adj_iff]
  left
  refine ⟨hwt, ?_⟩
  rw [pair_mem_crossEdgeSet_iff]
  simp only [SimpleGraph.mem_neighborFinset]
  push Not
  exact ⟨fun _ => hnot.2, fun _ => hnot.1⟩

/-- Any common neighbor of the canonical anchor and a proposed second
partner gives a cross edge incident to that tight anchor. -/
theorem one_le_anchor_secondCrossLoss_of_commonNeighbor {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w t : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    (hrt : (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) t)
    (hwt : (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj w t) :
    1 ≤ crossEdgeLoss
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)
      (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) := by
  apply one_le_crossEdgeLoss_neighborFinsets_of_commonNeighbor
  · exact firstPairPoleSwitch_adj_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  · exact hrt
  · exact hwt

/-- Unless the anchor itself is chosen as partner, a successful second switch
forces the proposed partner and the tight anchor to have no common neighbor
in the intermediate graph. -/
theorem successful_secondSwitch_anchor_commonNeighbors_eq_empty
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    (hrw : remainingPairPoleAnchor K h2 ha hb hc hab hac hbc ≠ w)
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) ∩
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w = ∅ := by
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  have hzr : J.Adj z r := by
    exact firstPairPoleSwitch_adj_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  have hrz : r ≠ z := by
    intro h
    exact J.loopless.irrefl z (by simpa [h] using hzr)
  have hdeg : J.degree r = Nat.card K := by
    exact firstPairPoleSwitch_degree_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  have hzero : crossEdgeLoss J (J.neighborFinset z)
      (J.neighborFinset w) r = 0 :=
    crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
      J z w r hfinal hdeg hrz (by simpa [r] using hrw)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases Finset.mem_inter.mp ht with ⟨hrt, hwt⟩
  have hp : 1 ≤ crossEdgeLoss J (J.neighborFinset z)
      (J.neighborFinset w) r := by
    apply one_le_crossEdgeLoss_neighborFinsets_of_commonNeighbor J z w r t
    · exact hzr
    · simpa only [SimpleGraph.mem_neighborFinset] using hrt
    · simpa only [SimpleGraph.mem_neighborFinset] using hwt
  omega

/-- The remaining defect and its anchor retain their unique projective common
neighbor through the first switch. -/
theorem exists_firstPairPoleSwitch_commonNeighbor_remainingPole_anchor
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ t : {v : P K // v ∉ ({a,b,c} : Finset (P K))},
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).Adj
          (threePointOuterPairDefectBC K ha hb hc hbc) t ∧
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).Adj
          (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) t := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  have hzrH : H.Adj z r := by
    exact remainingPairPoleAnchor_adj_pairPole K h2 ha hb hc hab hac hbc
  have hzr : (graph K).Adj z.1 r.1 := SimpleGraph.induce_adj.mp hzrH
  have hzne : z.1 ≠ r.1 := by
    intro h
    exact (graph K).loopless.irrefl z.1 (by simpa [h] using hzr)
  have hznon : ¬ Projectivization.orthogonal z.1 z.1 := by
    simpa [z, threePointOuterPairDefectBC] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
  have hrnon : ¬ Projectivization.orthogonal r.1 r.1 := by
    change ¬ Projectivization.orthogonal
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
    exact pairPoleThirdAbsoluteAnchor_not_absolute K h2 hb hc ha hbc hab hac
  have hone := card_commonNeighbors_eq_one_of_nonabsolute K hzne hznon hrnon
  have hpos : 0 < ((graph K).neighborFinset z.1 ∩
      (graph K).neighborFinset r.1).card := by omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_inter.mp ht with ⟨hztm, hrtm⟩
  have hzt : (graph K).Adj z.1 t := by
    simpa only [SimpleGraph.mem_neighborFinset] using hztm
  have hrt : (graph K).Adj r.1 t := by
    simpa only [SimpleGraph.mem_neighborFinset] using hrtm
  have hta : t ≠ a := by
    intro h
    have hza := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    exact hza (by simpa [z, threePointOuterPairDefectBC, h] using hzt)
  have htb : t ≠ b := by
    intro h
    have hrb : ¬ (graph K).Adj b r.1 := by
      intro hbr
      have hzb : (graph K).Adj z.1 b := by
        simpa [z, threePointOuterPairDefectBC] using
          (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) hzb hb
      have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
          (graph K).neighborFinset b := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hzr, hbr⟩
      rw [hempty] at hm
      simp at hm
    exact hrb (by simpa [h] using hrt.symm)
  have htc : t ≠ c := by
    intro h
    have hrc : ¬ (graph K).Adj c r.1 := by
      intro hcr
      have hzc : (graph K).Adj z.1 c := by
        simpa [z, threePointOuterPairDefectBC] using
          (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) hzc hc
      have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
          (graph K).neighborFinset c := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hzr, hcr⟩
      rw [hempty] at hm
      simp at hm
    exact hrc (by simpa [h] using hrt.symm)
  let tt : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    ⟨t, by simp [hta, htb, htc]⟩
  have htH_z : H.Adj z tt := SimpleGraph.induce_adj.mpr hzt
  have htH_r : H.Adj r tt := SimpleGraph.induce_adj.mpr hrt
  have hrne := remainingPairPoleAnchor_ne_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hra := remainingPairPoleAnchor_adj_a K h2 ha hb hc hab hac hbc
  have htx : ¬ H.Adj x tt := by
    intro hxt
    have hbase := SimpleGraph.induce_adj.mp hxt
    have hne : r.1 ≠ x.1 := by
      intro h
      exact hrne.1 (Subtype.ext h)
    have hle := commonNeighbors_le_one r.1 x.1 hne
    rw [Finset.card_le_one_iff] at hle
    have ham : a ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset x.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hra.symm, by simpa [x, threePointPairDefect] using
        (absolutePairCommonNeighbor_spec K ha hb hab).1.symm⟩
    have htm : t ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset x.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrt, hbase⟩
    exact hta (hle htm ham)
  have hty : ¬ H.Adj y tt := by
    intro hyt
    have hbase := SimpleGraph.induce_adj.mp hyt
    have hne : r.1 ≠ y.1 := by
      intro h
      exact hrne.2 (Subtype.ext h)
    have hle := commonNeighbors_le_one r.1 y.1 hne
    rw [Finset.card_le_one_iff] at hle
    have ham : a ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset y.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hra.symm, by simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).1.symm⟩
    have htm : t ∈ (graph K).neighborFinset r.1 ∩
        (graph K).neighborFinset y.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hrt, hbase⟩
    exact hta (hle htm ham)
  refine ⟨tt, ?_, ?_⟩
  · rw [crossEdgeSwitch_adj_iff]
    left
    refine ⟨htH_z, ?_⟩
    rw [pair_mem_crossEdgeSet_iff]
    simp only [SimpleGraph.mem_neighborFinset]
    push Not
    exact ⟨fun _ => hty, fun _ => htx⟩
  · rw [crossEdgeSwitch_adj_iff]
    left
    refine ⟨htH_r, ?_⟩
    rw [pair_mem_crossEdgeSet_iff]
    simp only [SimpleGraph.mem_neighborFinset]
    push Not
    exact ⟨fun _ => hty, fun _ => htx⟩

/-- A successful second-stage partner cannot be adjacent to the canonical
tight anchor.  Otherwise the retained common neighbor of the anchor and the
remaining defect supplies an incident cross edge at the anchor. -/
theorem successful_secondSwitch_not_adj_remainingPairPoleAnchor
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    ¬ (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) w := by
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  intro hrw
  have hrwne : r ≠ w := by
    intro h
    have hloop := hrw
    rw [← h] at hloop
    exact J.loopless.irrefl r hloop
  have hzr : J.Adj z r := by
    exact firstPairPoleSwitch_adj_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  have hrz : r ≠ z := by
    intro h
    exact J.loopless.irrefl z (by simpa [h] using hzr)
  have hdeg : J.degree r = Nat.card K := by
    exact firstPairPoleSwitch_degree_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  obtain ⟨t, hzt, hrt⟩ :=
    exists_firstPairPoleSwitch_commonNeighbor_remainingPole_anchor K h2
      ha hb hc hab hac hbc
  have hp : 1 ≤ crossEdgeLoss J (J.neighborFinset z)
      (J.neighborFinset w) r := by
    apply one_le_crossEdgeLoss_of_adj_of_pair_mem J _ _ hrt
    rw [pair_mem_crossEdgeSet_iff]
    right
    simp only [SimpleGraph.mem_neighborFinset]
    exact ⟨hrw.symm, hzt⟩
  have hzero := crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
    J z w r hfinal hdeg hrz hrwne
  omega

/-- Complete anchor-separation certificate for a hypothetical successful
second partner: it is distinct from the anchor, nonadjacent to it, and has no
common neighbor with it in the intermediate graph. -/
theorem successful_secondSwitch_partner_anchor_separated
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    let J := crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
    let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
    r ≠ w ∧ ¬ J.Adj r w ∧
      J.neighborFinset r ∩ J.neighborFinset w = ∅ := by
  dsimp only
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  have hzdeg : J.degree z = Nat.card K - 1 := by
    exact (firstPairPoleSwitch_unique_defect K h2 ha hb hc hab hac hbc).1
  have hzlt : J.degree z < Nat.card K := by
    have hq := three_le_card_of_two_ne_zero K h2
    omega
  have hzw : ¬ J.Adj z w :=
    successful_crossEdgeSwitch_not_adjacent_at_defect J z w hzlt (hfinal z)
  have hzr : J.Adj z r := by
    exact firstPairPoleSwitch_adj_remainingPairPoleAnchor K h2 ha hb hc
      hab hac hbc
  have hrw : r ≠ w := by
    intro h
    apply hzw
    rw [← h]
    exact hzr
  refine ⟨hrw, ?_, ?_⟩
  · exact successful_secondSwitch_not_adj_remainingPairPoleAnchor K h2
      ha hb hc hab hac hbc w hfinal
  · exact successful_secondSwitch_anchor_commonNeighbors_eq_empty K h2
      ha hb hc hab hac hbc w hrw hfinal

/-- The only surviving vertices beyond distance two from the canonical
anchor in the intermediate graph lie on the tangent at the deleted absolute
point `a`. -/
theorem adj_a_of_firstSwitch_anchor_separated
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    (hrw : remainingPairPoleAnchor K h2 ha hb hc hab hac hbc ≠ w)
    (hnadj : ¬ (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) w)
    (hempty : (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
        (remainingPairPoleAnchor K h2 ha hb hc hab hac hbc) ∩
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w = ∅) :
    (graph K).Adj a w.1 := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let J := crossEdgeSwitch H
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let r := remainingPairPoleAnchor K h2 ha hb hc hab hac hbc
  by_contra hwa
  have hHnot : ¬ H.Adj r w := by
    intro h
    exact hnadj ((firstPairPoleSwitch_adj_anchor_iff K h2 ha hb hc
      hab hac hbc w).2 h)
  have hrwval : r.1 ≠ w.1 := by
    intro h
    exact hrw (Subtype.ext h)
  have hrnon : ¬ Projectivization.orthogonal r.1 r.1 := by
    change ¬ Projectivization.orthogonal
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
      (pairPoleThirdAbsoluteAnchor K h2 hb hc ha hbc hab hac)
    exact pairPoleThirdAbsoluteAnchor_not_absolute K h2 hb hc ha hbc hab hac
  have hone : ((graph K).neighborFinset r.1 ∩
      (graph K).neighborFinset w.1).card = 1 := by
    by_cases hwabs : Projectivization.orthogonal w.1 w.1
    · apply card_commonNeighbors_eq_one_of_nonabsolute_absolute_notOrthogonal K
        hrnon hwabs
      intro hortho
      apply hHnot
      apply SimpleGraph.induce_adj.mpr
      exact (graph_adj_iff r.1 w.1).mpr ⟨hrwval, hortho⟩
    · exact card_commonNeighbors_eq_one_of_nonabsolute K hrwval hrnon hwabs
  have hpos : 0 < ((graph K).neighborFinset r.1 ∩
      (graph K).neighborFinset w.1).card := by omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_inter.mp ht with ⟨hrtm, hwtm⟩
  have hrt : (graph K).Adj r.1 t := by
    simpa only [SimpleGraph.mem_neighborFinset] using hrtm
  have hwt : (graph K).Adj w.1 t := by
    simpa only [SimpleGraph.mem_neighborFinset] using hwtm
  have hta : t ≠ a := by
    intro h
    exact hwa (by simpa [h] using hwt.symm)
  have hrz := remainingPairPoleAnchor_adj_pairPole K h2 ha hb hc hab hac hbc
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hzrb : (graph K).Adj z.1 r.1 := SimpleGraph.induce_adj.mp hrz
  have hrb : ¬ (graph K).Adj b r.1 := by
    intro hbr
    have hzb : (graph K).Adj z.1 b := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hzb hb
    have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset b := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hzrb, hbr⟩
    rw [hem] at hm
    simp at hm
  have hrc : ¬ (graph K).Adj c r.1 := by
    intro hcr
    have hzc : (graph K).Adj z.1 c := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hzc hc
    have hm : r.1 ∈ (graph K).neighborFinset z.1 ∩
        (graph K).neighborFinset c := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hzrb, hcr⟩
    rw [hem] at hm
    simp at hm
  have htb : t ≠ b := by
    intro h
    exact hrb (by simpa [h] using hrt.symm)
  have htc : t ≠ c := by
    intro h
    exact hrc (by simpa [h] using hrt.symm)
  let tt : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    ⟨t, by simp [hta, htb, htc]⟩
  have hrtH : H.Adj r tt := SimpleGraph.induce_adj.mpr hrt
  have hwtH : H.Adj w tt := SimpleGraph.induce_adj.mpr hwt
  have hrtJ : J.Adj r tt :=
    (firstPairPoleSwitch_adj_anchor_iff K h2 ha hb hc hab hac hbc tt).2 hrtH
  have hwtJ : J.Adj w tt :=
    firstPairPoleSwitch_adj_of_adj_anchor_neighbor K h2 ha hb hc hab hac hbc
      w tt hwtH hrtH
  have hm : tt ∈ J.neighborFinset r ∩ J.neighborFinset w := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hrtJ, hwtJ⟩
  change J.neighborFinset r ∩ J.neighborFinset w = ∅ at hempty
  rw [hempty] at hm
  simp at hm

/-- Every successful second-stage partner is forced onto the tangent at the
deleted shared absolute point `a`.  This reduces the full projective plane to
the `q-1` surviving tangent points other than the canonical anchor. -/
theorem successful_secondSwitch_partner_adj_deletedSharedAbsolute
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    (graph K).Adj a w.1 := by
  have hs := successful_secondSwitch_partner_anchor_separated K h2
    ha hb hc hab hac hbc w hfinal
  exact adj_a_of_firstSwitch_anchor_separated K h2 ha hb hc hab hac hbc w
    hs.1 hs.2.1 hs.2.2

/-- An ordinary surviving point on the tangent at `a` has a second absolute
neighbor which is not one of the three deleted points.  The only exceptions
are the two pair poles `{a,b}` and `{a,c}`. -/
theorem exists_surviving_second_absolute_of_adj_a_of_ne_pairPoles
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hwa : (graph K).Adj a w.1)
    (hwx : w ≠ threePointPairDefect K ha hb hc hab)
    (hwy : w ≠ threePointOuterPairDefectAC K ha hb hc hac) :
    ∃ d : {v : P K // v ∉ ({a,b,c} : Finset (P K))},
      Projectivization.orthogonal d.1 d.1 ∧ (graph K).Adj w.1 d.1 := by
  have hwnon : ¬ Projectivization.orthogonal w.1 w.1 :=
    not_selfOrthogonal_of_adj_selfOrthogonal hwa ha
  obtain ⟨d, hda, hdabs, hwd⟩ :=
    exists_second_absolute_neighbor K h2 hwnon ha hwa.symm
  have hdb : d ≠ b := by
    intro h
    have heq := (Classical.choose_spec
      (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hb hab)).2
        w.1 ⟨hwa, by simpa [h] using hwd.symm, hwnon⟩
    change w.1 = absolutePairCommonNeighbor K ha hb hab at heq
    exact hwx (Subtype.ext heq)
  have hdc : d ≠ c := by
    intro h
    have heq := (Classical.choose_spec
      (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hc hac)).2
        w.1 ⟨hwa, by simpa [h] using hwd.symm, hwnon⟩
    change w.1 = absolutePairCommonNeighbor K ha hc hac at heq
    exact hwy (Subtype.ext heq)
  exact ⟨⟨d, by simp [hda, hdb, hdc]⟩, hdabs, hwd⟩

/-- Every surviving absolute neighbor of a proposed partner suffers positive
loss in the second cross deletion centered at the remaining pair pole. -/
theorem one_le_secondCrossLoss_at_surviving_absolute
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w d : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hdabs : Projectivization.orthogonal d.1 d.1)
    (hwd : (graph K).Adj w.1 d.1)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj] :
    1 ≤ crossEdgeLoss
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w) d := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let J := crossEdgeSwitch H
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hda : d.1 ≠ a := by intro h; exact d.2 (by simp [h])
  have hdb : d.1 ≠ b := by intro h; exact d.2 (by simp [h])
  have hdc : d.1 ≠ c := by intro h; exact d.2 (by simp [h])
  have hone := card_pairPole_commonNeighbors_third_absolute_eq_one K h2
    hb hc hdabs hbc hdb hdc
  have hpos : 0 < ((graph K).neighborFinset z.1 ∩
      (graph K).neighborFinset d.1).card := by
    change 0 < ((graph K).neighborFinset
      (absolutePairCommonNeighbor K hb hc hbc) ∩
      (graph K).neighborFinset d.1).card
    rw [hone]
    decide
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_inter.mp hu with ⟨hzum, hdum⟩
  have hzu : (graph K).Adj z.1 u := by
    simpa only [SimpleGraph.mem_neighborFinset] using hzum
  have hdu : (graph K).Adj d.1 u := by
    simpa only [SimpleGraph.mem_neighborFinset] using hdum
  have hua : u ≠ a := by
    intro h
    have hza := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    exact hza (by simpa [z, threePointOuterPairDefectBC, h] using hzu)
  have hub : u ≠ b := by
    intro h
    have hbad : ¬ Projectivization.orthogonal b b :=
      not_selfOrthogonal_of_adj_selfOrthogonal
        (by simpa [h] using hdu) hdabs
    exact hbad hb
  have huc : u ≠ c := by
    intro h
    have hbad : ¬ Projectivization.orthogonal c c :=
      not_selfOrthogonal_of_adj_selfOrthogonal
        (by simpa [h] using hdu) hdabs
    exact hbad hc
  let uu : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    ⟨u, by simp [hua, hub, huc]⟩
  have hzuH : H.Adj z uu := SimpleGraph.induce_adj.mpr hzu
  have hduH : H.Adj d uu := SimpleGraph.induce_adj.mpr hdu
  have hwdH : H.Adj w d := SimpleGraph.induce_adj.mpr hwd
  have hdout := survivingAbsolute_not_adj_firstPairPoles K h2 ha hb hc
    hab hac d hdabs
  have hzout := remainingPairPole_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hwdJ : J.Adj w d := by
    exact (crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y d w
      hwdH.symm hdout.1 hdout.2).symm
  have hduJ : J.Adj d uu :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y d uu
      hduH hdout.1 hdout.2
  have hzuJ : J.Adj z uu :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y z uu
      hzuH hzout.1 hzout.2
  apply one_le_crossEdgeLoss_of_adj_of_pair_mem J _ _ hduJ
  rw [pair_mem_crossEdgeSet_iff]
  right
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨hwdJ, hzuJ⟩

/-- The tangent/secant obstruction eliminates every ordinary tangent point:
a successful second-stage partner would have to be one of the two pair poles
used by the first switch. -/
theorem successful_secondSwitch_partner_eq_firstPairPole_or_outerAC
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    w = threePointPairDefect K ha hb hc hab ∨
      w = threePointOuterPairDefectAC K ha hb hc hac := by
  by_contra h
  push Not at h
  have hwa := successful_secondSwitch_partner_adj_deletedSharedAbsolute K h2
    ha hb hc hab hac hbc w hfinal
  obtain ⟨d, hdabs, hwd⟩ :=
    exists_surviving_second_absolute_of_adj_a_of_ne_pairPoles K h2
      ha hb hc hab hac hbc w hwa h.1 h.2
  have hwnon : ¬ Projectivization.orthogonal w.1 w.1 :=
    not_selfOrthogonal_of_adj_selfOrthogonal hwa ha
  have hdw : d ≠ w := by
    intro heq
    exact hwnon (by simpa [heq] using hdabs)
  have hzero := secondPairPoleSwitch_avoids_surviving_absolute K h2
    ha hb hc hab hac hbc w d hdabs hdw hfinal
  have hp := one_le_secondCrossLoss_at_surviving_absolute K h2
    ha hb hc hab hac hbc w d hdabs hwd
  omega

/-- Every clean center neighbor becomes tight, of degree exactly `q`, after
the first pair-pole switch. -/
theorem firstPairPoleSwitch_degree_cleanCenter
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c))
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).degree v = Nat.card K := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  have hvx : H.Adj x v := by
    have hm := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1
    apply SimpleGraph.induce_adj.mpr
    simpa [x, threePointPairDefect] using
      ((graph K).mem_neighborFinset
        (absolutePairCommonNeighbor K ha hb hab) v.1).mp hm.1
  have hvNx : v ∈ H.neighborFinset x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hvx
  have hdisj := centerPairDefect_neighborFinset_inter_outerAC_eq_empty K
    h2 ha hb hc hab hac hbc
  have hvNy : v ∉ H.neighborFinset y := by
    intro h
    have hm : v ∈ H.neighborFinset x ∩ H.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hvNx, h⟩
    rw [hdisj] at hm
    simp at hm
  have hloss : crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset y) v = 1 := by
    rw [crossEdgeLoss_eq_card_neighbor_inter_right H _ _ v hvNx hvNy]
    exact cleanCenter_commonNeighbors_outerAC_card_one K h2 ha hb hc
      hab hac hbc v hv
  have hbase : H.degree v = Nat.card K + 1 := by
    exact threePointCore_degree_of_mem_pairPoleCleanCenterNeighbors K h2
      ha hb hc hab (Ne.symm hac) (Ne.symm hbc) v hv
  have hD : D.degree v = Nat.card K := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    change H.degree v = D.degree v + _ at hs
    rw [hbase, hloss] at hs
    omega
  have hvneX : v ≠ x := by
    intro h
    exact H.loopless.irrefl x (by simpa [h] using hvx)
  have hvneY : v ≠ y := by
    intro h
    have hvm := Finset.mem_sdiff.mp hv
    have hvnc : ¬ (graph K).Adj c v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    exact hvnc (by simpa [y, threePointOuterPairDefectAC, h] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.1)
  rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints H x y v
    hvneX hvneY]
  exact hD

/-- In the second switch using the first `{a,b}` pole as partner, every clean
center neighbor loses its other outer-arm edge. -/
theorem one_le_secondCrossLoss_at_cleanCenter_for_firstPairPole
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c))
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj] :
    1 ≤ crossEdgeLoss
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointPairDefect K ha hb hc hab)) v := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let J := crossEdgeSwitch H
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  obtain ⟨r, s, hrs, hvr, hry, hvs, hsz⟩ :=
    exists_two_distinct_outer_cross_edges_of_cleanCenter K h2
      ha hb hc hab hac hbc v hv
  have hvx : H.Adj x v := by
    have hm := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1
    apply SimpleGraph.induce_adj.mpr
    simpa [x, threePointPairDefect] using
      ((graph K).mem_neighborFinset
        (absolutePairCommonNeighbor K ha hb hab) v.1).mp hm.1
  have hsNx : s ∉ H.neighborFinset x := by
    intro hsx
    have hm : s ∈ H.neighborFinset x ∩ H.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hsx, hsz⟩
    rw [firstPairPole_neighborFinset_inter_remainingPairPole_eq_empty K
      h2 ha hb hc hab hac hbc] at hm
    simp at hm
  have hsNy : s ∉ H.neighborFinset y := by
    intro hsy
    have hm : s ∈ H.neighborFinset y ∩ H.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hsy, hsz⟩
    rw [outerPairDefects_neighborFinset_inter_eq_empty K h2
      ha hb hc hab hac hbc] at hm
    simp at hm
  have hsx : ¬ H.Adj x s := by
    simpa only [SimpleGraph.mem_neighborFinset] using hsNx
  have hsy : ¬ H.Adj y s := by
    simpa only [SimpleGraph.mem_neighborFinset] using hsNy
  have hvsJ : J.Adj v s := by
    exact (crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y s v
      hvs.symm hsx hsy).symm
  have hzout := remainingPairPole_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hzsH : H.Adj z s := by
    simpa only [SimpleGraph.mem_neighborFinset] using hsz
  have hzsJ : J.Adj z s :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y z s
      hzsH hzout.1 hzout.2
  have hxy := centerPairDefect_not_adj_outerAC K ha hb hc hab hac
  have hxvJ : J.Adj x v :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y x v hvx
      (H.loopless.irrefl x) (fun h => hxy h.symm)
  apply one_le_crossEdgeLoss_of_adj_of_pair_mem J _ _ hvsJ
  rw [pair_mem_crossEdgeSet_iff]
  right
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨hxvJ, hzsJ⟩

/-- The first `{a,b}` pole cannot serve as a successful second-stage partner. -/
theorem firstPairPole_not_successful_secondPartner
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc)
      (threePointPairDefect K ha hb hc hab)).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointPairDefect K ha hb hc hab))).Adj] :
    ¬ ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc)
        (threePointPairDefect K ha hb hc hab)).degree u := by
  intro hfinal
  classical
  have hcard := pairPoleCleanCenterNeighbors_card K h2 ha hb hc hab
    (Ne.symm hac) (Ne.symm hbc)
  have hq := three_le_card_of_two_ne_zero K h2
  have hpos : 0 < (pairPoleCleanCenterNeighbors K ha hb hab (c := c)).card := by
    rw [hcard]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hpD : p ∉ ({a,b,c} : Finset (P K)) :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).2
  let v : {v : P K // v ∉ ({a,b,c} : Finset (P K))} := ⟨p, hpD⟩
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let x := threePointPairDefect K ha hb hc hab
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hvdeg : J.degree v = Nat.card K :=
    firstPairPoleSwitch_degree_cleanCenter K h2 ha hb hc hab hac hbc v
      (by simpa [v] using hp)
  have hvxAdj : (threePointCore K).Adj x v := by
    have hm := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1
    apply SimpleGraph.induce_adj.mpr
    simpa [x, threePointPairDefect, v] using
      ((graph K).mem_neighborFinset
        (absolutePairCommonNeighbor K ha hb hab) p).mp hm.1
  have hvx : v ≠ x := by
    intro h
    exact (threePointCore K).loopless.irrefl x (by simpa [h] using hvxAdj)
  have hvz : v ≠ z := by
    intro h
    have hvm := Finset.mem_sdiff.mp hp
    have hvnc : ¬ (graph K).Adj c p := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    have hpz : p = z.1 := congrArg Subtype.val h
    exact hvnc (by
      rw [hpz]
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1)
  have hzero := crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
    J z x v hfinal hvdeg hvz hvx
  have hloss := one_le_secondCrossLoss_at_cleanCenter_for_firstPairPole K h2
    ha hb hc hab hac hbc v (by simpa [v] using hp)
  change crossEdgeLoss J (J.neighborFinset z) (J.neighborFinset x) v = 0 at hzero
  change 1 ≤ crossEdgeLoss J (J.neighborFinset z) (J.neighborFinset x) v at hloss
  rw [hzero] at hloss
  omega

/-- Clean neighbors centered at the other first-switch endpoint `{a,c}`. -/
noncomputable def outerACCleanCenterNeighbors {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hc : Projectivization.orthogonal c c) (hac : a ≠ c) : Finset (P K) :=
  ((graph K).neighborFinset (absolutePairCommonNeighbor K ha hc hac) \
      ({a,b,c} : Finset (P K))) \
    (graph K).neighborFinset b

theorem outerACCleanCenterNeighbors_card {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (outerACCleanCenterNeighbors K ha hc hac (b := b)).card = Nat.card K - 2 := by
  classical
  have hD : ({a,b,c} : Finset (P K)) = {a,c,b} := by
    ext t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [outerACCleanCenterNeighbors, hD]
  exact pairPoleCleanCenterNeighbors_card K h2 ha hc hb hac
    (Ne.symm hab) hbc

theorem outerACCleanCenter_spec {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ outerACCleanCenterNeighbors K ha hc hac (b := b)) :
    (threePointCore K).Adj (threePointOuterPairDefectAC K ha hb hc hac) v ∧
      ¬ (graph K).Adj a v.1 ∧ ¬ (graph K).Adj b v.1 ∧
      ¬ (graph K).Adj c v.1 ∧
      ¬ Projectivization.orthogonal v.1 v.1 ∧
      (threePointCore K).degree v = Nat.card K + 1 := by
  classical
  let y := threePointOuterPairDefectAC K ha hb hc hac
  have hvm := Finset.mem_sdiff.mp hv
  have hvfirst := Finset.mem_sdiff.mp hvm.1
  have hyvbase : (graph K).Adj y.1 v.1 := by
    change (graph K).Adj (absolutePairCommonNeighbor K ha hc hac) v.1
    exact
      ((graph K).mem_neighborFinset
        (absolutePairCommonNeighbor K ha hc hac) v.1).mp hvfirst.1
  have hyv : (threePointCore K).Adj y v := SimpleGraph.induce_adj.mpr hyvbase
  have hvb : ¬ (graph K).Adj b v.1 := by
    simpa [outerACCleanCenterNeighbors, SimpleGraph.mem_neighborFinset] using hvm.2
  have hva : ¬ (graph K).Adj a v.1 := by
    intro hav
    have hya : (graph K).Adj y.1 a := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hya ha
    have hm : v.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset a := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hyvbase, hav⟩
    rw [hem] at hm
    simp at hm
  have hvc : ¬ (graph K).Adj c v.1 := by
    intro hcv
    have hyc : (graph K).Adj y.1 c := by
      simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm
    have hem := neighborFinset_inter_eq_empty_of_adj_absolute (K := K) hyc hc
    have hm : v.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset c := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hyvbase, hcv⟩
    rw [hem] at hm
    simp at hm
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro hvabs
    have hvan : v.1 ≠ a := by intro h; exact v.2 (by simp [h])
    have hvcn : v.1 ≠ c := by intro h; exact v.2 (by simp [h])
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hc hac hvabs hvan hvcn)
        (by simpa [y, threePointOuterPairDefectAC] using hyvbase)
  exact ⟨hyv, hva, hvb, hvc, hvnon,
    threePointCore_degree_eq_card_add_one_of_clean K v hvnon hva hvb hvc⟩

theorem outerACCleanCenter_commonNeighbors_firstPair_card_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ outerACCleanCenterNeighbors K ha hc hac (b := b)) :
    ((threePointCore K).neighborFinset v ∩
      (threePointCore K).neighborFinset
        (threePointPairDefect K ha hb hc hab)).card = 1 := by
  classical
  let x := threePointPairDefect K ha hb hc hab
  have hs := outerACCleanCenter_spec K h2 ha hb hc hab hac hbc v hv
  have hxnon : ¬ Projectivization.orthogonal x.1 x.1 := by
    simpa [x, threePointPairDefect] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.2
  have hvx : v.1 ≠ x.1 := by
    intro h
    exact hs.2.2.1 (by simpa [x, threePointPairDefect, h] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.1)
  have hone := card_commonNeighbors_eq_one_of_nonabsolute K hvx hs.2.2.2.2.1 hxnon
  apply card_induce_commonNeighbors_eq_one_of_survives
    (graph K) ({a,b,c} : Finset (P K)) v x hone
  intro p hpv hpx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl)
  · exact hs.2.1 hpv.symm
  · exact hs.2.2.1 hpv.symm
  · exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab hc (Ne.symm hac) (Ne.symm hbc))
        (by simpa [x, threePointPairDefect] using hpx)

theorem outerACCleanCenter_commonNeighbors_remainingPair_card_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ outerACCleanCenterNeighbors K ha hc hac (b := b)) :
    ((threePointCore K).neighborFinset v ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectBC K ha hb hc hbc)).card = 1 := by
  classical
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hs := outerACCleanCenter_spec K h2 ha hb hc hab hac hbc v hv
  have hznon : ¬ Projectivization.orthogonal z.1 z.1 := by
    simpa [z, threePointOuterPairDefectBC] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
  have hvz : v.1 ≠ z.1 := by
    intro h
    exact hs.2.2.2.1 (by simpa [z, threePointOuterPairDefectBC, h] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.1)
  have hone := card_commonNeighbors_eq_one_of_nonabsolute K hvz hs.2.2.2.2.1 hznon
  apply card_induce_commonNeighbors_eq_one_of_survives
    (graph K) ({a,b,c} : Finset (P K)) v z hone
  intro p hpv hzp
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl)
  · exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac)
        (by simpa [z, threePointOuterPairDefectBC] using hzp)
  · exact hs.2.2.1 hpv.symm
  · exact hs.2.2.2.1 hpv.symm

theorem firstPairPoleSwitch_degree_outerACCleanCenter
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ outerACCleanCenterNeighbors K ha hc hac (b := b))
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).degree v = Nat.card K := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  have hs := outerACCleanCenter_spec K h2 ha hb hc hab hac hbc v hv
  have hvNy : v ∈ H.neighborFinset y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hs.1
  have hdisj := centerPairDefect_neighborFinset_inter_outerAC_eq_empty K
    h2 ha hb hc hab hac hbc
  have hvNx : v ∉ H.neighborFinset x := by
    intro h
    have hm : v ∈ H.neighborFinset x ∩ H.neighborFinset y :=
      Finset.mem_inter.mpr ⟨h, hvNy⟩
    rw [hdisj] at hm
    simp at hm
  have hloss : crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset y) v = 1 := by
    rw [crossEdgeLoss_eq_card_neighbor_inter_left H _ _ v hvNy hvNx]
    exact outerACCleanCenter_commonNeighbors_firstPair_card_one K h2
      ha hb hc hab hac hbc v hv
  have hbase : H.degree v = Nat.card K + 1 := hs.2.2.2.2.2
  have hD : D.degree v = Nat.card K := by
    have hsplit := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    change H.degree v = D.degree v + _ at hsplit
    rw [hbase, hloss] at hsplit
    omega
  have hvy : v ≠ y := by
    intro h
    have hloop : H.Adj y v := hs.1
    rw [h] at hloop
    exact H.loopless.irrefl y hloop
  have hvx : v ≠ x := by
    intro h
    exact hs.2.2.1 (by simpa [x, threePointPairDefect, h] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.1)
  rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints H x y v
    hvx hvy]
  exact hD

theorem one_le_secondCrossLoss_at_outerACCleanCenter
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ outerACCleanCenterNeighbors K ha hc hac (b := b))
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj] :
    1 ≤ crossEdgeLoss
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectAC K ha hb hc hac)) v := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let J := crossEdgeSwitch H
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hcard := outerACCleanCenter_commonNeighbors_remainingPair_card_one K h2
    ha hb hc hab hac hbc v hv
  rw [Finset.card_eq_one] at hcard
  obtain ⟨s, hs⟩ := hcard
  have hsm : s ∈ H.neighborFinset v ∩ H.neighborFinset z := by
    rw [hs]
    simp
  have hvs : H.Adj v s := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hsm).1
  have hzs : H.Adj z s := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hsm).2
  have hsNx : s ∉ H.neighborFinset x := by
    intro hsx
    have hm : s ∈ H.neighborFinset x ∩ H.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hsx, by simpa only [SimpleGraph.mem_neighborFinset] using hzs⟩
    rw [firstPairPole_neighborFinset_inter_remainingPairPole_eq_empty K
      h2 ha hb hc hab hac hbc] at hm
    simp at hm
  have hsNy : s ∉ H.neighborFinset y := by
    intro hsy
    have hm : s ∈ H.neighborFinset y ∩ H.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hsy, by simpa only [SimpleGraph.mem_neighborFinset] using hzs⟩
    rw [outerPairDefects_neighborFinset_inter_eq_empty K h2
      ha hb hc hab hac hbc] at hm
    simp at hm
  have hvsJ : J.Adj v s := by
    exact (crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y s v hvs.symm
      (by simpa only [SimpleGraph.mem_neighborFinset] using hsNx)
      (by simpa only [SimpleGraph.mem_neighborFinset] using hsNy)).symm
  have hzout := remainingPairPole_not_adj_firstPairPoles K h2 ha hb hc
    hab hac hbc
  have hzsJ : J.Adj z s :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y z s hzs
      hzout.1 hzout.2
  have hyv := (outerACCleanCenter_spec K h2 ha hb hc hab hac hbc v hv).1
  have hxy := centerPairDefect_not_adj_outerAC K ha hb hc hab hac
  have hyvJ : J.Adj y v :=
    crossEdgeSwitch_adj_of_adj_of_endpoint_outside H x y y v hyv
      hxy (H.loopless.irrefl y)
  apply one_le_crossEdgeLoss_of_adj_of_pair_mem J _ _ hvsJ
  rw [pair_mem_crossEdgeSet_iff]
  right
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨hyvJ, hzsJ⟩

/-- The other first-switch endpoint `{a,c}` cannot be a successful final
partner either. -/
theorem outerACPairPole_not_successful_secondPartner
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    ¬ ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc)
        (threePointOuterPairDefectAC K ha hb hc hac)).degree u := by
  intro hfinal
  classical
  have hcard := outerACCleanCenterNeighbors_card K h2 ha hb hc hab hac hbc
  have hq := three_le_card_of_two_ne_zero K h2
  have hpos : 0 < (outerACCleanCenterNeighbors K ha hc hac (b := b)).card := by
    rw [hcard]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hpD : p ∉ ({a,b,c} : Finset (P K)) :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).2
  let v : {v : P K // v ∉ ({a,b,c} : Finset (P K))} := ⟨p, hpD⟩
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hvdeg : J.degree v = Nat.card K :=
    firstPairPoleSwitch_degree_outerACCleanCenter K h2 ha hb hc hab hac hbc
      v (by simpa [v] using hp)
  have hs := outerACCleanCenter_spec K h2 ha hb hc hab hac hbc v
    (by simpa [v] using hp)
  have hvy : v ≠ y := by
    intro h
    have hloop : (threePointCore K).Adj y v := hs.1
    rw [h] at hloop
    exact (threePointCore K).loopless.irrefl y hloop
  have hvz : v ≠ z := by
    intro h
    exact hs.2.2.2.1 (by simpa [z, threePointOuterPairDefectBC, h] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.1)
  have hzero := crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
    J z y v hfinal hvdeg hvz hvy
  have hloss := one_le_secondCrossLoss_at_outerACCleanCenter K h2 ha hb hc
    hab hac hbc v (by simpa [v] using hp)
  change crossEdgeLoss J (J.neighborFinset z) (J.neighborFinset y) v = 0 at hzero
  change 1 ≤ crossEdgeLoss J (J.neighborFinset z) (J.neighborFinset y) v at hloss
  rw [hzero] at hloss
  omega

/-- **Uniform two-switch obstruction.**  After the canonical first switch
repairs two of the three pair-pole defects, no universal cross-edge switch
between the remaining defect and any partner can raise the minimum degree to
`q`. -/
theorem no_successful_secondPairPoleSwitch
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj] :
    ¬ ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u := by
  intro hfinal
  rcases successful_secondSwitch_partner_eq_firstPairPole_or_outerAC K h2
    ha hb hc hab hac hbc w hfinal with rfl | rfl
  · exact firstPairPole_not_successful_secondPartner K h2 ha hb hc
      hab hac hbc hfinal
  · exact outerACPairPole_not_successful_secondPartner K h2 ha hb hc
      hab hac hbc hfinal

end Erdos85.Polarity
