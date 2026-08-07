import Proofs.Erdos85OrderFortyNineDistTwoPinning

/-!
# Pinning the three-high distinct-common-neighbor configuration

Let `s12` and `s13` be the distinct common neighbors of `(v1,v2)` and
`(v1,v3)`.  Around the high root `v1`, the two foreign highs lie in the
branches rooted at `s12` and `s13`.  There is a sharp dichotomy: if the two
parents are locally paired, the branches have no cross edges; otherwise each
foreign high has exactly one neighbor in the opposite branch.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The three pairwise common neighbors of three high vertices are either
all the same or pairwise distinct.  A two-equal middle pattern collapses to
the all-equal distance-two case by uniqueness of high-pair common neighbors. -/
theorem orderFortyNine_common_highPair_witness_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 u12 u13 u23 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hu12_1 : G.Adj u12 v1) (hu12_2 : G.Adj u12 v2)
    (hu13_1 : G.Adj u13 v1) (hu13_3 : G.Adj u13 v3)
    (hu23_2 : G.Adj u23 v2) (hu23_3 : G.Adj u23 v3) :
    (u12 = u13 ∧ u13 = u23) ∨
      (u12 ≠ u13 ∧ u12 ≠ u23 ∧ u13 ≠ u23) := by
  have hcommon12 := orderFortyNineDistTwo_common_highPair_eq_singleton
    G hfree hmin hcard hv1 hv2 h12 hu12_1 hu12_2
  have hcommon13 := orderFortyNineDistTwo_common_highPair_eq_singleton
    G hfree hmin hcard hv1 hv3 h13 hu13_1 hu13_3
  have hcommon23 := orderFortyNineDistTwo_common_highPair_eq_singleton
    G hfree hmin hcard hv2 hv3 h23 hu23_2 hu23_3
  by_cases h1213 : u12 = u13
  · left
    refine ⟨h1213, ?_⟩
    have hu12Common23 : u12 ∈
        G.neighborFinset v2 ∩ G.neighborFinset v3 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hu12_2.symm, h1213 ▸ hu13_3.symm⟩
    have hu12u23 : u12 = u23 := by
      simpa [hcommon23] using hu12Common23
    exact h1213.symm.trans hu12u23
  · right
    refine ⟨h1213, ?_, ?_⟩
    · intro h1223
      have hu23Common13 : u23 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v3 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨h1223 ▸ hu12_1.symm, hu23_3.symm⟩
      have hu23u13 : u23 = u13 := by
        simpa [hcommon13] using hu23Common13
      exact h1213 (h1223.trans hu23u13)
    · intro h1323
      have hu23Common12 : u23 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v2 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨h1323 ▸ hu13_1.symm, hu23_2.symm⟩
      have hu23u12 : u23 = u12 := by
        simpa [hcommon12] using hu23Common12
      exact h1213 (hu23u12.symm.trans h1323.symm)

/-- Three distinct degree-eight vertices canonically determine their three
pairwise common-neighbor witnesses.  Those witnesses exhibit exactly the two
geometric strata used downstream: either one vertex is common to all three
highs, or the three pair witnesses are pairwise distinct. -/
theorem orderFortyNine_exists_common_highPair_witnesses_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ∃ u12 u13 u23 : V,
      G.neighborFinset v1 ∩ G.neighborFinset v2 = {u12} ∧
      G.neighborFinset v1 ∩ G.neighborFinset v3 = {u13} ∧
      G.neighborFinset v2 ∩ G.neighborFinset v3 = {u23} ∧
      ((u12 = u13 ∧ u13 = u23) ∨
        (u12 ≠ u13 ∧ u12 ≠ u23 ∧ u13 ≠ u23)) := by
  have hc12 := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv1 hv2 h12
  have hc13 := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv1 hv3 h13
  have hc23 := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard hv2 hv3 h23
  rw [Finset.card_eq_one] at hc12 hc13 hc23
  rcases hc12 with ⟨u12, hu12⟩
  rcases hc13 with ⟨u13, hu13⟩
  rcases hc23 with ⟨u23, hu23⟩
  have hu12mem : u12 ∈
      G.neighborFinset v1 ∩ G.neighborFinset v2 := by simp [hu12]
  have hu13mem : u13 ∈
      G.neighborFinset v1 ∩ G.neighborFinset v3 := by simp [hu13]
  have hu23mem : u23 ∈
      G.neighborFinset v2 ∩ G.neighborFinset v3 := by simp [hu23]
  have hu12adj : G.Adj u12 v1 ∧ G.Adj u12 v2 := by
    have h : G.Adj v1 u12 ∧ G.Adj v2 u12 := by
      simpa [SimpleGraph.mem_neighborFinset] using hu12mem
    exact ⟨h.1.symm, h.2.symm⟩
  have hu13adj : G.Adj u13 v1 ∧ G.Adj u13 v3 := by
    have h : G.Adj v1 u13 ∧ G.Adj v3 u13 := by
      simpa [SimpleGraph.mem_neighborFinset] using hu13mem
    exact ⟨h.1.symm, h.2.symm⟩
  have hu23adj : G.Adj u23 v2 ∧ G.Adj u23 v3 := by
    have h : G.Adj v2 u23 ∧ G.Adj v3 u23 := by
      simpa [SimpleGraph.mem_neighborFinset] using hu23mem
    exact ⟨h.1.symm, h.2.symm⟩
  refine ⟨u12, u13, u23, hu12, hu13, hu23, ?_⟩
  exact orderFortyNine_common_highPair_witness_trichotomy
    G hfree hmin hcard hv1 hv2 hv3 h12 h13 h23
      hu12adj.1 hu12adj.2 hu13adj.1 hu13adj.2 hu23adj.1 hu23adj.2

/-- The siblings of `u12` and `u13` in the two foreign high neighborhoods
cannot both be the third pairwise common neighbor `u23`. -/
theorem orderFortyNineDistOne_not_both_siblings_eq_u23
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {v1 v2 v3 u12 u13 u23 x2 x3 : V}
    (hv1 : G.degree v1 = 8)
    (hu23low : G.degree u23 = 7)
    (hu : u12 ≠ u13)
    (hu12_1 : G.Adj u12 v1) (hu13_1 : G.Adj u13 v1)
    (hx2 : G.Adj u12 x2) (hx3 : G.Adj u13 x3) :
    ¬(x2 = u23 ∧ x3 = u23) := by
  rintro ⟨hx2eq, hx3eq⟩
  have hv1u23 : v1 ≠ u23 := by
    intro h
    rw [h] at hv1
    omega
  have hu12u23 : G.Adj u12 u23 := by simpa [hx2eq] using hx2
  have hu13u23 : G.Adj u13 u23 := by simpa [hx3eq] using hx3
  exact hfree (containsC4_of_two_common hu hv1u23
    hu12_1.symm hu13_1.symm hu12u23.symm hu13u23.symm)

/-- In the partner case neither foreign sibling can coincide with `u23`.
Each proposed coincidence immediately gives a four-cycle through the partner
edge and the remaining high vertex. -/
theorem orderFortyNineDistOne_partner_forces_no_sibling_coincidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 u12 u13 u23 x2 x3 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (hu12_1 : G.Adj u12 v1) (hu12_2 : G.Adj u12 v2)
    (hu13_1 : G.Adj u13 v1) (hu13_3 : G.Adj u13 v3)
    (hu23_2 : G.Adj u23 v2) (hu23_3 : G.Adj u23 v3)
    (hpair : G.Adj u12 u13)
    (hx2 : G.Adj u12 x2) (hx3 : G.Adj u13 x3)
    (hu12u23 : u12 ≠ u23) (hu13u23 : u13 ≠ u23) :
    x2 ≠ u23 ∧ x3 ≠ u23 := by
  have hu12low : G.degree u12 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv1 hu12_1.symm
  have hu13low : G.degree u13 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv1 hu13_1.symm
  constructor
  · intro hx2eq
    have hu23u12 : G.Adj u23 u12 := by
      simpa [hx2eq] using hx2.symm
    have hv3u12 : v3 ≠ u12 := by
      intro h
      rw [h] at hv3
      omega
    exact hfree (containsC4_of_two_common hu13u23.symm hv3u12
      hu23_3.symm hu13_3.symm hu23u12.symm hpair)
  · intro hx3eq
    have hu23u13 : G.Adj u23 u13 := by
      simpa [hx3eq] using hx3.symm
    have hv2u13 : v2 ≠ u13 := by
      intro h
      rw [h] at hv2
      omega
    exact hfree (containsC4_of_two_common hu12u23.symm hv2u13
      hu23_2.symm hu12_2.symm hu23u13.symm hpair.symm)

/-- Every neighbor of a high vertex has a unique partner inside that high
vertex's induced neighborhood matching. -/
theorem orderFortyNine_existsUnique_local_partner_of_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v s : V} (hv : G.degree v = 8) (hsv : G.Adj s v) :
    ∃! x : V, G.Adj s x ∧ G.Adj v x := by
  let sLocal : {z : V // z ∈ G.neighborSet v} :=
    ⟨s, by simpa using hsv.symm⟩
  have hdeg := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    G hfree hmin hcard hv sLocal
  rw [← (G.induce (G.neighborSet v)).card_neighborFinset_eq_degree,
    Finset.card_eq_one] at hdeg
  rcases hdeg with ⟨xLocal, hxLocal⟩
  refine ⟨xLocal.1, ?_, ?_⟩
  · have hxmem : xLocal ∈
        (G.induce (G.neighborSet v)).neighborFinset sLocal := by
      simp [hxLocal]
    exact ⟨((G.induce (G.neighborSet v)).mem_neighborFinset
      sLocal xLocal).mp hxmem, xLocal.2⟩
  · intro y hy
    have hymem : (⟨y, hy.2⟩ : {z : V // z ∈ G.neighborSet v}) ∈
        (G.induce (G.neighborSet v)).neighborFinset sLocal := by
      exact ((G.induce (G.neighborSet v)).mem_neighborFinset sLocal
        (⟨y, hy.2⟩ : {z : V // z ∈ G.neighborSet v})).mpr hy.1
    have heq : (⟨y, hy.2⟩ : {z : V // z ∈ G.neighborSet v}) =
        xLocal := by simpa [hxLocal] using hymem
    exact congrArg Subtype.val heq

/-- Canonical siblings in the distinct-common-neighbor case, together with
the exhaustive (and mutually constrained) coincidence alternatives with
`u23`. -/
theorem orderFortyNineDistOne_exists_siblings_and_coincidence_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 u12 u13 u23 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hu12u13 : u12 ≠ u13)
    (hu12_1 : G.Adj u12 v1) (hu12_2 : G.Adj u12 v2)
    (hu13_1 : G.Adj u13 v1) (hu13_3 : G.Adj u13 v3)
    (hu23_2 : G.Adj u23 v2) (hu23_3 : G.Adj u23 v3) :
    let p12 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨u12, by simpa using hu12_1.symm⟩
    let p13 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨u13, by simpa using hu13_1.symm⟩
    ∃ x2 x3 : V,
      G.degree x2 = 7 ∧ G.degree x3 = 7 ∧
      G.Adj u12 x2 ∧ G.Adj v2 x2 ∧
      G.Adj u13 x3 ∧ G.Adj v3 x3 ∧
      x2 ∈ secondLayerBranch G v1 p12 ∧
      x3 ∈ secondLayerBranch G v1 p13 ∧
      ((x2 = u23 ∧ x3 ≠ u23) ∨
       (x2 ≠ u23 ∧ x3 = u23) ∨
       (x2 ≠ u23 ∧ x3 ≠ u23)) := by
  dsimp
  rcases (orderFortyNine_existsUnique_local_partner_of_high
    G hfree hmin hcard hv2 hu12_2).exists with ⟨x2, hx2u12, hx2v2⟩
  rcases (orderFortyNine_existsUnique_local_partner_of_high
    G hfree hmin hcard hv3 hu13_3).exists with ⟨x3, hx3u13, hx3v3⟩
  have hx2deg : G.degree x2 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv2 hx2v2
  have hx3deg : G.degree x3 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv3 hx3v3
  have hx2Branch : x2 ∈ secondLayerBranch G v1
      (⟨u12, by simpa using hu12_1.symm⟩ :
        {z : V // z ∈ G.neighborSet v1}) := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hx2u12, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    constructor
    · intro h
      have hdeg := hv1
      rw [← h] at hdeg
      omega
    · intro hv1x2
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv2 h12 hu12_1 hu12_2
      have hx2Common : x2 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v2 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hv1x2, hx2v2⟩
      have hx2eq : x2 = u12 := by simpa [hcommon] using hx2Common
      exact G.loopless.irrefl u12 (hx2eq ▸ hx2u12)
  have hx3Branch : x3 ∈ secondLayerBranch G v1
      (⟨u13, by simpa using hu13_1.symm⟩ :
        {z : V // z ∈ G.neighborSet v1}) := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hx3u13, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    constructor
    · intro h
      have hdeg := hv1
      rw [← h] at hdeg
      omega
    · intro hv1x3
      have hcommon := orderFortyNineDistTwo_common_highPair_eq_singleton
        G hfree hmin hcard hv1 hv3 h13 hu13_1 hu13_3
      have hx3Common : x3 ∈
          G.neighborFinset v1 ∩ G.neighborFinset v3 := by
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hv1x3, hx3v3⟩
      have hx3eq : x3 = u13 := by simpa [hcommon] using hx3Common
      exact G.loopless.irrefl u13 (hx3eq ▸ hx3u13)
  have hu23low : G.degree u23 = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv2 hu23_2.symm
  have hnotBoth := orderFortyNineDistOne_not_both_siblings_eq_u23
    G hfree (v2 := v2) (v3 := v3) hv1 hu23low hu12u13
      hu12_1 hu13_1 hx2u12 hx3u13
  refine ⟨x2, x3, hx2deg, hx3deg, hx2u12, hx2v2,
    hx3u13, hx3v3, hx2Branch, hx3Branch, ?_⟩
  by_cases h2 : x2 = u23
  · exact Or.inl ⟨h2, fun h3 => hnotBoth ⟨h2, h3⟩⟩
  by_cases h3 : x3 = u23
  · exact Or.inr (Or.inl ⟨h2, h3⟩)
  · exact Or.inr (Or.inr ⟨h2, h3⟩)

/-- The two foreign highs occupy the branches rooted at their respective
common neighbors with the first high. -/
theorem orderFortyNineDistOne_foreign_highs_in_respective_branches
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 s12 s13 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3)
    (hs12_1 : G.Adj s12 v1) (hs12_2 : G.Adj s12 v2)
    (hs13_1 : G.Adj s13 v1) (hs13_3 : G.Adj s13 v3) :
    let p12 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s12, by simpa using hs12_1.symm⟩
    let p13 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s13, by simpa using hs13_1.symm⟩
    v2 ∈ secondLayerBranch G v1 p12 ∧
      v3 ∈ secondLayerBranch G v1 p13 := by
  dsimp
  have hnot12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv2
  have hnot13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hv1 hv3
  constructor
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs12_2, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h12.symm, fun h => hnot12 h⟩
  · rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨by simpa [SimpleGraph.mem_neighborFinset] using hs13_3, ?_⟩
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨h13.symm, fun h => hnot13 h⟩

/-- Exact partner/non-partner dichotomy for the two occupied branches. -/
theorem orderFortyNineDistOne_branch_cross_incidence_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v1 v2 v3 s12 s13 : V}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (hs : s12 ≠ s13)
    (hs12_1 : G.Adj s12 v1) (hs12_2 : G.Adj s12 v2)
    (hs13_1 : G.Adj s13 v1) (hs13_3 : G.Adj s13 v3) :
    let p12 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s12, by simpa using hs12_1.symm⟩
    let p13 : {z : V // z ∈ G.neighborSet v1} :=
      ⟨s13, by simpa using hs13_1.symm⟩
    (G.Adj s12 s13 ∧
        (G.neighborFinset v2 ∩ secondLayerBranch G v1 p13).card = 0 ∧
        (G.neighborFinset v3 ∩ secondLayerBranch G v1 p12).card = 0) ∨
      (¬ G.Adj s12 s13 ∧
        (G.neighborFinset v2 ∩ secondLayerBranch G v1 p13).card = 1 ∧
        (G.neighborFinset v3 ∩ secondLayerBranch G v1 p12).card = 1) := by
  dsimp
  let p12 : {z : V // z ∈ G.neighborSet v1} :=
    ⟨s12, by simpa using hs12_1.symm⟩
  let p13 : {z : V // z ∈ G.neighborSet v1} :=
    ⟨s13, by simpa using hs13_1.symm⟩
  have hbranches := orderFortyNineDistOne_foreign_highs_in_respective_branches
    G hfree hmin hcard hv1 hv2 hv3 h12 h13
      hs12_1 hs12_2 hs13_1 hs13_3
  change v2 ∈ secondLayerBranch G v1 p12 ∧
    v3 ∈ secondLayerBranch G v1 p13 at hbranches
  by_cases hpaired : G.Adj s12 s13
  · left
    refine ⟨hpaired, ?_, ?_⟩
    · rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact orderFortyNine_not_adj_between_paired_highBranches
        G hfree hpaired hbranches.1 (Finset.mem_inter.mp hq).2
          ((G.mem_neighborFinset v2 q).mp (Finset.mem_inter.mp hq).1)
    · rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact orderFortyNine_not_adj_between_paired_highBranches
        G hfree hpaired.symm hbranches.2 (Finset.mem_inter.mp hq).2
          ((G.mem_neighborFinset v3 q).mp (Finset.mem_inter.mp hq).1)
  · right
    refine ⟨hpaired, ?_, ?_⟩
    · exact orderFortyNine_card_highNeighbors_in_unpaired_branch_eq_one
        G hfree hmin hcard hv1 hv2 hbranches.1 hpaired
    · exact orderFortyNine_card_highNeighbors_in_unpaired_branch_eq_one
        G hfree hmin hcard hv1 hv3 hbranches.2 (by
          simpa [G.adj_comm] using hpaired)

end

end Erdos85
