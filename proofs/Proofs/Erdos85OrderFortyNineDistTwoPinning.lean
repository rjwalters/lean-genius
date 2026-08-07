import Proofs.Erdos85OrderFortyNineHighBranchGeometry
import Proofs.Erdos85OrderFortyNineLocalEdgePartition

/-!
# Pinning the three-high distance-two configuration at order 49

Suppose a degree-seven vertex is adjacent to three degree-eight vertices.
It is the unique common neighbor of each pair.  Relative to any one high
root, the other two highs therefore lie in the same five-vertex branch, and
the center's local matching partner is adjacent to neither of them.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A displayed common neighbor of two distinct high vertices is their
unique common neighbor. -/
theorem orderFortyNineDistTwo_common_highPair_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v w s : V} (hv : G.degree v = 8) (hw : G.degree w = 8)
    (hvw : v ≠ w) (hsv : G.Adj s v) (hsw : G.Adj s w) :
    G.neighborFinset v ∩ G.neighborFinset w = {s} := by
  have hone := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv hw hvw
  rw [Finset.card_eq_one] at hone
  rcases hone with ⟨q, hq⟩
  have hs : s ∈ G.neighborFinset v ∩ G.neighborFinset w := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hsv.symm, hsw.symm⟩
  have hsq : s = q := by simpa [hq] using hs
  simpa [hsq] using hq

/-- Relative to the first high root, both foreign highs lie in the branch
whose parent is the common low vertex. -/
theorem orderFortyNineDistTwo_foreign_highs_in_common_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3) :
    let parent : {z : V // z ∈ G.neighborSet v1} :=
      ⟨sStar, by simpa using hs1.symm⟩
    v2 ∈ secondLayerBranch G v1 parent ∧
      v3 ∈ secondLayerBranch G v1 parent := by
  dsimp
  have hnot12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv2
  have hnot13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv3
  constructor
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs2, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h12.symm, fun h => hnot12 h⟩
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs3, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h13.symm, fun h => hnot13 h⟩

/-- If the displayed vertices are exactly the three high vertices, removing
the two foreign highs from their common branch leaves precisely three low
vertices.  This is the canonical finset form of the five-point branch
decomposition, avoiding arbitrary labels for the three lows. -/
theorem orderFortyNineDistTwo_exists_three_low_branch_remainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3)
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3}) :
    let parent : {z : V // z ∈ G.neighborSet v1} :=
      ⟨sStar, by simpa using hs1.symm⟩
    ∃ L : Finset V,
      L.card = 3 ∧
      secondLayerBranch G v1 parent = insert v2 (insert v3 L) ∧
      (∀ z ∈ L, G.degree z = 7) := by
  dsimp
  let parent : {z : V // z ∈ G.neighborSet v1} :=
    ⟨sStar, by simpa using hs1.symm⟩
  let B := secondLayerBranch G v1 parent
  let L := B \ {v2, v3}
  have hforeign := orderFortyNineDistTwo_foreign_highs_in_common_branch
    G hfree hmin hcard hv1 hv2 hv3 h12 h13 hs1 hs2 hs3
  change v2 ∈ B ∧ v3 ∈ B at hforeign
  have hpairSub : ({v2, v3} : Finset V) ⊆ B := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hforeign.1, hforeign.2⟩
  have hBcard : B.card = 5 :=
    orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
      G hfree hmin hcard hv1 parent
  have hpairCard : ({v2, v3} : Finset V).card = 2 := by
    simp [h23]
  have hLcard : L.card = 3 := by
    change (B \ ({v2, v3} : Finset V)).card = 3
    rw [Finset.card_sdiff_of_subset hpairSub, hBcard, hpairCard]
  have hdecomp : B = insert v2 (insert v3 L) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton,
      L]
    constructor
    · intro hz
      by_cases hz2 : z = v2
      · exact Or.inl hz2
      by_cases hz3 : z = v3
      · exact Or.inr (Or.inl hz3)
      · exact Or.inr (Or.inr ⟨hz, by simpa [hz2, hz3]⟩)
    · rintro (rfl | rfl | ⟨hz, _⟩)
      · exact hforeign.1
      · exact hforeign.2
      · exact hz
  refine ⟨L, hLcard, hdecomp, ?_⟩
  intro z hzL
  rcases orderFortyNine_degree_eq_seven_or_eight
    G hfree hmin hcard z with hz7 | hz8
  · exact hz7
  · exfalso
    have hzHigh : z ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hz8]
    rw [hHigh] at hzHigh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzHigh
    have hzNotPair : z ∉ ({v2, v3} : Finset V) :=
      (Finset.mem_sdiff.mp hzL).2
    rcases hzHigh with hz1 | hz2 | hz3
    · have hzB : z ∈ B := (Finset.mem_sdiff.mp hzL).1
      have hzOutside := (Finset.mem_sdiff.mp hzB).2
      exact hzOutside (by simp [hz1])
    · exact hzNotPair (by simp [hz2])
    · exact hzNotPair (by simp [hz3])

/-- The common low vertex has a unique partner inside the first high
neighborhood.  That partner cannot see either foreign high, since it would
be a second common neighbor of the corresponding high pair. -/
theorem orderFortyNineDistTwo_exists_partner_not_adj_foreign_highs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3) :
    ∃! t : V, G.Adj sStar t ∧ G.Adj v1 t ∧
      ¬ G.Adj t v2 ∧ ¬ G.Adj t v3 := by
  let sLocal : {z : V // z ∈ G.neighborSet v1} :=
    ⟨sStar, by simpa using hs1.symm⟩
  have hdeg := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    G hfree hmin hcard hv1 sLocal
  rw [← (G.induce (G.neighborSet v1)).card_neighborFinset_eq_degree,
    Finset.card_eq_one] at hdeg
  rcases hdeg with ⟨tLocal, htLocal⟩
  refine ⟨tLocal.1, ?_, ?_⟩
  · have htmem : tLocal ∈
        (G.induce (G.neighborSet v1)).neighborFinset sLocal := by
      simp [htLocal]
    have hst : G.Adj sStar tLocal.1 := by
      exact ((G.induce (G.neighborSet v1)).mem_neighborFinset
        sLocal tLocal).mp htmem
    have ht1 : G.Adj v1 tLocal.1 := tLocal.2
    refine ⟨hst, ht1, ?_, ?_⟩
    · intro ht2
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv2 h12 hs1 hs2
      have htmem' : tLocal.1 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v2 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨ht1, ht2.symm⟩
      have hts : tLocal.1 = sStar := by simpa [hcommon] using htmem'
      exact G.loopless.irrefl sStar (hts ▸ hst)
    · intro ht3
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv3 h13 hs1 hs3
      have htmem' : tLocal.1 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v3 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨ht1, ht3.symm⟩
      have hts : tLocal.1 = sStar := by simpa [hcommon] using htmem'
      exact G.loopless.irrefl sStar (hts ▸ hst)
  · intro q hq
    have hqmem : (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1}) ∈
        (G.induce (G.neighborSet v1)).neighborFinset sLocal := by
      exact ((G.induce (G.neighborSet v1)).mem_neighborFinset sLocal
        (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1})).mpr hq.1
    have heq : (⟨q, hq.2.1⟩ : {z : V // z ∈ G.neighborSet v1}) =
        tLocal := by simpa [htLocal] using hqmem
    exact congrArg Subtype.val heq

/-- The matching partners of `sStar` in the two foreign high neighborhoods
are distinct low vertices in the same branch around `v1`. -/
theorem orderFortyNineDistTwo_exists_distinct_low_siblings_in_common_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3) :
    let parent : {z : V // z ∈ G.neighborSet v1} :=
      ⟨sStar, by simpa using hs1.symm⟩
    ∃ x2 x3 : V,
      x2 ≠ x3 ∧
      G.degree x2 = 7 ∧ G.degree x3 = 7 ∧
      G.Adj sStar x2 ∧ G.Adj v2 x2 ∧
      G.Adj sStar x3 ∧ G.Adj v3 x3 ∧
      x2 ∈ secondLayerBranch G v1 parent ∧
      x3 ∈ secondLayerBranch G v1 parent := by
  dsimp
  rcases (orderFortyNineDistTwo_exists_partner_not_adj_foreign_highs
    G hfree hmin hcard hv2 hv1 hv3 h12.symm h23 hs2 hs1 hs3).exists with
    ⟨x2, hx2s, hx2v2, hx2notv1, _hx2notv3⟩
  rcases (orderFortyNineDistTwo_exists_partner_not_adj_foreign_highs
    G hfree hmin hcard hv3 hv1 hv2 h13.symm h23.symm hs3 hs1 hs2).exists with
    ⟨x3, hx3s, hx3v3, hx3notv1, _hx3notv2⟩
  have hx2deg : G.degree x2 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv2 hx2v2
  have hx3deg : G.degree x3 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv3 hx3v3
  have hx2Branch : x2 ∈ secondLayerBranch G v1
      (⟨sStar, by simpa using hs1.symm⟩ :
        {z : V // z ∈ G.neighborSet v1}) := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hx2s, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨(fun h => by subst x2; omega), fun h => hx2notv1 h.symm⟩
  have hx3Branch : x3 ∈ secondLayerBranch G v1
      (⟨sStar, by simpa using hs1.symm⟩ :
        {z : V // z ∈ G.neighborSet v1}) := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hx3s, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨(fun h => by subst x3; omega), fun h => hx3notv1 h.symm⟩
  have hx23 : x2 ≠ x3 := by
    intro heq
    have hxCommon : x2 ∈
        G.neighborFinset v2 ∩ G.neighborFinset v3 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hx2v2, heq ▸ hx3v3⟩
    have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
      G hfree hmin hcard hv2 hv3 h23 hs2 hs3
    have hxStar : x2 = sStar := by simpa [hcommon] using hxCommon
    exact G.loopless.irrefl sStar (hxStar ▸ hx2s)
  exact ⟨x2, x3, hx23, hx2deg, hx3deg, hx2s, hx2v2,
    hx3s, hx3v3, hx2Branch, hx3Branch⟩

/-- Full pinned neighborhood census in the three-high distance-two case.
Besides the three highs and their three local partners, `sStar` has exactly
one residual low neighbor; that neighbor also belongs to the common branch
around `v1`. -/
theorem orderFortyNineDistTwo_exists_exact_pinned_neighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 sStar : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8) (hsLow : G.degree sStar = 7)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3)
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3}) :
    let parent : {z : V // z ∈ G.neighborSet v1} :=
      ⟨sStar, by simpa using hs1.symm⟩
    ∃ t x2 x3 l3 : V,
      G.neighborFinset sStar = {v1, v2, v3, t, x2, x3, l3} ∧
      G.degree t = 7 ∧ G.degree x2 = 7 ∧ G.degree x3 = 7 ∧
      G.degree l3 = 7 ∧
      G.Adj v1 t ∧ G.Adj v2 x2 ∧ G.Adj v3 x3 ∧
      t ∉ ({x2, x3} : Finset V) ∧ x2 ≠ x3 ∧
      l3 ∈ secondLayerBranch G v1 parent := by
  dsimp
  rcases orderFortyNineDistTwo_exists_partner_not_adj_foreign_highs
    G hfree hmin hcard hv1 hv2 hv3 h12 h13 hs1 hs2 hs3 with
    ⟨t, ⟨hts, ht1, htNot2, htNot3⟩, htUnique⟩
  rcases orderFortyNineDistTwo_exists_distinct_low_siblings_in_common_branch
    G hfree hmin hcard hv1 hv2 hv3 h12 h13 h23 hs1 hs2 hs3 with
    ⟨x2, x3, hx23, hx2deg, hx3deg, hx2s, hx2v2,
      hx3s, hx3v3, _hx2Branch, _hx3Branch⟩
  have htdeg : G.degree t = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv1 ht1
  have htx2 : t ≠ x2 := by
    intro h
    subst x2
    exact htNot2 hx2v2.symm
  have htx3 : t ≠ x3 := by
    intro h
    subst x3
    exact htNot3 hx3v3.symm
  have low_ne_high : ∀ {a b : V}, G.degree a = 7 →
      G.degree b = 8 → a ≠ b := by
    intro a b ha hb hab
    subst b
    omega
  have hv1t : v1 ≠ t := (low_ne_high htdeg hv1).symm
  have hv2t : v2 ≠ t := (low_ne_high htdeg hv2).symm
  have hv3t : v3 ≠ t := (low_ne_high htdeg hv3).symm
  have hv1x2 : v1 ≠ x2 := (low_ne_high hx2deg hv1).symm
  have hv2x2 : v2 ≠ x2 := (low_ne_high hx2deg hv2).symm
  have hv3x2 : v3 ≠ x2 := (low_ne_high hx2deg hv3).symm
  have hv1x3 : v1 ≠ x3 := (low_ne_high hx3deg hv1).symm
  have hv2x3 : v2 ≠ x3 := (low_ne_high hx3deg hv2).symm
  have hv3x3 : v3 ≠ x3 := (low_ne_high hx3deg hv3).symm
  let K : Finset V := {v1, v2, v3, t, x2, x3}
  have hKcard : K.card = 6 := by
    simp [K, h12, h13, h23, htx2, htx3, hx23,
      hv1t, hv2t, hv3t, hv1x2, hv2x2, hv3x2,
      hv1x3, hv2x3, hv3x3]
  have hKsub : K ⊆ G.neighborFinset sStar := by
    intro z hz
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hts
    · exact hx2s
    · exact hx3s
  have hNcard : (G.neighborFinset sStar).card = 7 := by
    rw [G.card_neighborFinset_eq_degree, hsLow]
  have hresCard : (G.neighborFinset sStar \ K).card = 1 := by
    rw [Finset.card_sdiff_of_subset hKsub, hNcard, hKcard]
  rw [Finset.card_eq_one] at hresCard
  rcases hresCard with ⟨l3, hl3res⟩
  have hl3mem : l3 ∈ G.neighborFinset sStar \ K := by simp [hl3res]
  have hl3adj : G.Adj sStar l3 := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp hl3mem).1
  have hl3notK : l3 ∉ K := (Finset.mem_sdiff.mp hl3mem).2
  have hNdecomp : G.neighborFinset sStar = insert l3 K := by
    ext z
    constructor
    · intro hz
      by_cases hzK : z ∈ K
      · exact Finset.mem_insert.mpr (Or.inr hzK)
      · have hzres : z ∈ G.neighborFinset sStar \ K :=
          Finset.mem_sdiff.mpr ⟨hz, hzK⟩
        have : z = l3 := by simpa [hl3res] using hzres
        exact Finset.mem_insert.mpr (Or.inl this)
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hzK
      · exact (Finset.mem_sdiff.mp hl3mem).1
      · exact hKsub hzK
  have hl3deg : G.degree l3 = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard l3 with h7 | h8
    · exact h7
    · exfalso
      have hl3High : l3 ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, h8]
      rw [hHigh] at hl3High
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl3High
      apply hl3notK
      rcases hl3High with h | h | h
      · simp [K, h]
      · simp [K, h]
      · simp [K, h]
  have hl3Branch : l3 ∈ secondLayerBranch G v1
      (⟨sStar, by simpa using hs1.symm⟩ :
        {z : V // z ∈ G.neighborSet v1}) := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hl3adj, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    constructor
    · intro h
      subst l3
      apply hl3notK
      simp [K]
    · intro h1l3
      have hl3Not2 : ¬ G.Adj l3 v2 := by
        intro hl32
        have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
          G hfree hmin hcard hv1 hv2 h12 hs1 hs2
        have hl3Common : l3 ∈
            G.neighborFinset v1 ∩ G.neighborFinset v2 := by
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨h1l3, hl32.symm⟩
        have hl3eq : l3 = sStar := by simpa [hcommon] using hl3Common
        exact G.loopless.irrefl sStar (hl3eq ▸ hl3adj)
      have hl3Not3 : ¬ G.Adj l3 v3 := by
        intro hl33
        have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
          G hfree hmin hcard hv1 hv3 h13 hs1 hs3
        have hl3Common : l3 ∈
            G.neighborFinset v1 ∩ G.neighborFinset v3 := by
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨h1l3, hl33.symm⟩
        have hl3eq : l3 = sStar := by simpa [hcommon] using hl3Common
        exact G.loopless.irrefl sStar (hl3eq ▸ hl3adj)
      have hl3t : l3 = t := htUnique l3
        ⟨hl3adj, h1l3, hl3Not2, hl3Not3⟩
      apply hl3notK
      simp [K, hl3t]
  have hNshape : G.neighborFinset sStar =
      {v1, v2, v3, t, x2, x3, l3} := by
    rw [hNdecomp]
    ext z
    simp [K, or_comm, or_left_comm, or_assoc]
  refine ⟨t, x2, x3, l3, hNshape, htdeg, hx2deg, hx3deg,
    hl3deg, ht1, hx2v2, hx3v3, ?_, hx23, hl3Branch⟩
  simp [htx2, htx3]

end

end Erdos85
