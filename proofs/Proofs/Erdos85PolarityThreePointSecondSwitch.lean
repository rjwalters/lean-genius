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

end Erdos85.Polarity
