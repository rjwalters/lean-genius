import Proofs.Erdos85OrderFortyNineDefectWeightedIncidence

/-!
# Low neighborhoods partition the high sector at order 49

Every low--high pair has exactly one common neighbor.  Equivalently, for a
fixed low vertex, its seven neighbors collectively meet every high
neighborhood exactly once.  This is the graph-adjacency counterpart of the
closed-defect-neighborhood perfect-code identity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every low vertex and every high vertex have exactly one common neighbor.
The key short proof is that high vertices are isolated in the second-order
defect graph, so the C4-free common-neighbor dichotomy cannot take its zero
branch. -/
theorem orderFortyNine_low_high_card_common_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y w : V}
    (hy : G.degree y = 7) (hw : G.degree w = 8) :
    (G.neighborFinset y ∩ G.neighborFinset w).card = 1 := by
  let D := secondOrderDefectGraph G
  have hyw : y ≠ w := by
    intro h
    subst w
    omega
  have hwDzero : D.degree w = 0 :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hw).1
  have hwDempty : D.neighborFinset w = ∅ := by
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hwDzero]
  have hnotD : ¬ D.Adj y w := by
    intro hywD
    have : y ∈ D.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hywD
    rw [hwDempty] at this
    exact Finset.notMem_empty y this
  have hcommon := card_common_eq_if_secondOrderDefect G hfree y w hyw
  have hnotMem : w ∉ (secondOrderDefectGraph G).neighborFinset y := by
    simpa [SimpleGraph.mem_neighborFinset] using hnotD
  rw [if_neg hnotMem] at hcommon
  exact hcommon

/-- For every low `y` and high `w`, exactly one member of `N(y)` is adjacent
to `w`.  Thus the common-neighbor witnesses partition the high sector. -/
theorem orderFortyNine_low_neighborhood_partitions_highs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y : V}
    (hy : G.degree y = 7) {w : V}
    (hw : w ∈ orderFortyNineHighVertices G) :
    ∃! x, x ∈ G.neighborFinset y ∧ G.Adj x w := by
  have hw8 : G.degree w = 8 := (Finset.mem_filter.mp hw).2
  have hcardCommon := orderFortyNine_low_high_card_common_eq_one
    G hfree hmin hcard hy hw8
  rcases Finset.card_eq_one.mp hcardCommon with ⟨x, hx⟩
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset w := by
    simp [hx]
  refine ⟨x, ?_, ?_⟩
  · have hxy := (Finset.mem_inter.mp hxmem).1
    have hxw := (Finset.mem_inter.mp hxmem).2
    exact ⟨hxy, by simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hxw⟩
  · intro z hz
    have hzmem : z ∈ G.neighborFinset y ∩ G.neighborFinset w := by
      refine Finset.mem_inter.mpr ⟨hz.1, ?_⟩
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hz.2
    simpa [hx] using hzmem

/-- **Pointwise adjacency-weight identity.**  If `k(x)` is the number of
high neighbors of `x`, then the sum of `k` over the seven graph neighbors of
any low vertex is the total number of high vertices.  In matrix notation,
`A k = h 1` on the low sector. -/
theorem orderFortyNine_sum_highIncidence_over_lowNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y : V}
    (hy : G.degree y = 7) :
    (∑ x ∈ G.neighborFinset y,
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) =
      (orderFortyNineHighVertices G).card := by
  let H := orderFortyNineHighVertices G
  have hswap := sum_card_neighbor_inter_comm G (G.neighborFinset y) H
  rw [hswap]
  calc
    (∑ w ∈ H, (G.neighborFinset w ∩ G.neighborFinset y).card) =
        ∑ _w ∈ H, 1 := by
      apply Finset.sum_congr rfl
      intro w hw
      have hw8 : G.degree w = 8 := (Finset.mem_filter.mp hw).2
      rw [Finset.inter_comm]
      exact orderFortyNine_low_high_card_common_eq_one
        G hfree hmin hcard hy hw8
    _ = H.card := by simp

/-- At `h=9`, every low neighborhood carries total high-incidence weight
exactly nine. -/
theorem orderFortyNine_sum_highIncidence_over_lowNeighborhood_eq_nine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) {y : V}
    (hy : G.degree y = 7) :
    (∑ x ∈ G.neighborFinset y,
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) = 9 := by
  rw [orderFortyNine_sum_highIncidence_over_lowNeighborhood
    G hfree hmin hcard hy, hHigh]

/-- The second numerical `h=9` profile is impossible.  Its unique
three-high low vertex can be avoided by at least thirty-three low vertices.
For each such vertex the neighborhood weight identity forces a neighbor in
the three-element one-high fiber, but those three vertices have total degree
only twenty-one. -/
theorem orderFortyNine_not_highIncidence_profile_nine_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    ¬ (orderFortyNineHighIncidenceCount G 0 = 3 ∧
       orderFortyNineHighIncidenceCount G 1 = 3 ∧
       orderFortyNineHighIncidenceCount G 2 = 33 ∧
       orderFortyNineHighIncidenceCount G 3 = 1) := by
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  let S1 := L.filter fun x => k x = 1
  let S3 := L.filter fun x => k x = 3
  rintro ⟨_hn0, hn1, _hn2, hn3⟩
  have hS1card : S1.card = 3 := by
    simpa [S1, L, k, H, orderFortyNineHighIncidenceCount] using hn1
  have hS3card : S3.card = 1 := by
    simpa [S3, L, k, H, orderFortyNineHighIncidenceCount] using hn3
  rcases Finset.card_eq_one.mp hS3card with ⟨z, hS3⟩
  have hzS3 : z ∈ S3 := by simp [hS3]
  have hzL : z ∈ L := (Finset.mem_filter.mp hzS3).1
  have hkz : k z = 3 := (Finset.mem_filter.mp hzS3).2
  have hz7 : G.degree z = 7 := by
    have hznot : z ∉ H := (Finset.mem_sdiff.mp hzL).2
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard z with hz7 | hz8
    · exact hz7
    · exact (hznot (by simp [H, orderFortyNineHighVertices, hz8])).elim
  let T := L \ G.neighborFinset z
  have hLcard : L.card = 40 := by
    dsimp [L, orderFortyNineLowVertices]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp only [Finset.inter_univ]
    rw [hHigh]
  have hTcard : 33 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_sdiff]
    have hinter : (G.neighborFinset z ∩ L).card ≤ 7 := by
      calc
        (G.neighborFinset z ∩ L).card ≤ (G.neighborFinset z).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 7 := by rw [G.card_neighborFinset_eq_degree, hz7]
    rw [hLcard]
    omega
  have hhighWeightZero : ∀ x ∈ H, k x = 0 := by
    intro x hxH
    have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hxH).2
    apply Finset.card_eq_zero.mpr
    ext w
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨hwN, hwH⟩
    have hw8 : G.degree w = 8 := (Finset.mem_filter.mp hwH).2
    have hadj : G.Adj x w := by
      simpa [SimpleGraph.mem_neighborFinset] using hwN
    exact orderFortyNine_not_adj_degreeEight_degreeEight
      G hfree hmin hcard hx8 hw8 hadj
  have hcovered : ∀ y ∈ T, 1 ≤ (G.neighborFinset y ∩ S1).card := by
    intro y hyT
    have hyL : y ∈ L := (Finset.mem_sdiff.mp hyT).1
    have hyNotZ : y ∉ G.neighborFinset z := (Finset.mem_sdiff.mp hyT).2
    have hy7 : G.degree y = 7 := by
      have hynot : y ∉ H := (Finset.mem_sdiff.mp hyL).2
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · exact (hynot (by simp [H, orderFortyNineHighVertices, hy8])).elim
    by_contra hzero
    have hempty : G.neighborFinset y ∩ S1 = ∅ := by
      rw [← Finset.card_eq_zero]
      omega
    have htermEven : ∀ x ∈ G.neighborFinset y, Even (k x) := by
      intro x hxy
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · have hxL : x ∈ L := by
          have hxnot : x ∉ H := by
            intro hxH
            have : G.degree x = 8 := (Finset.mem_filter.mp hxH).2
            omega
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnot⟩
        have hk_le : k x ≤ 3 := by
          simpa [k, H] using orderFortyNine_highNeighborCount_le_three
            G hfree hmin hcard hx7
        have hk1 : k x ≠ 1 := by
          intro hkx
          have hxS1 : x ∈ S1 := Finset.mem_filter.mpr ⟨hxL, hkx⟩
          have : x ∈ G.neighborFinset y ∩ S1 :=
            Finset.mem_inter.mpr ⟨hxy, hxS1⟩
          rw [hempty] at this
          exact Finset.notMem_empty x this
        have hk3 : k x ≠ 3 := by
          intro hkx
          have hxS3 : x ∈ S3 := Finset.mem_filter.mpr ⟨hxL, hkx⟩
          have hxz : x = z := by simpa [hS3] using hxS3
          subst x
          have : y ∈ G.neighborFinset z := by
            simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hxy
          exact hyNotZ this
        rcases (show k x = 0 ∨ k x = 2 by omega) with hk0 | hk2
        · exact ⟨0, by simp [hk0]⟩
        · exact ⟨1, by simp [hk2]⟩
      · have hxH : x ∈ H := by
          simp [H, orderFortyNineHighVertices, hx8]
        rw [hhighWeightZero x hxH]
        exact Even.zero
    have hsumEven : Even (∑ x ∈ G.neighborFinset y, k x) :=
      Finset.even_sum _ fun x hx => htermEven x hx
    have hsumNine := orderFortyNine_sum_highIncidence_over_lowNeighborhood_eq_nine
      G hfree hmin hcard hHigh hy7
    change (∑ x ∈ G.neighborFinset y, k x) = 9 at hsumNine
    rw [hsumNine] at hsumEven
    norm_num at hsumEven
  have hlower : T.card ≤
      ∑ y ∈ T, (G.neighborFinset y ∩ S1).card := by
    calc
      T.card = ∑ _y ∈ T, 1 := by simp
      _ ≤ ∑ y ∈ T, (G.neighborFinset y ∩ S1).card := by
        exact Finset.sum_le_sum fun y hy => hcovered y hy
  have hswap := sum_card_neighbor_inter_comm G T S1
  have hupper : (∑ x ∈ S1, (G.neighborFinset x ∩ T).card) ≤ 21 := by
    calc
      (∑ x ∈ S1, (G.neighborFinset x ∩ T).card) ≤
          ∑ x ∈ S1, G.degree x := by
        apply Finset.sum_le_sum
        intro x hx
        rw [← G.card_neighborFinset_eq_degree]
        exact Finset.card_le_card Finset.inter_subset_left
      _ = ∑ _x ∈ S1, 7 := by
        apply Finset.sum_congr rfl
        intro x hxS1
        have hxL : x ∈ L := (Finset.mem_filter.mp hxS1).1
        have hxnot : x ∉ H := (Finset.mem_sdiff.mp hxL).2
        rcases orderFortyNine_degree_eq_seven_or_eight
            G hfree hmin hcard x with hx7 | hx8
        · exact hx7
        · exact (hxnot (by simp [H, orderFortyNineHighVertices, hx8])).elim
      _ = 21 := by simp [hS1card]
  rw [hswap] at hlower
  omega

/-- Combining the two certificate-free eliminations, an `h=9` graph must
lie in one of the final three incidence profiles. -/
theorem orderFortyNine_highIncidence_profile_of_nine_high_final_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    let n := orderFortyNineHighIncidenceCount G
    (n 0 = 2 ∧ n 1 = 6 ∧ n 2 = 30 ∧ n 3 = 2) ∨
    (n 0 = 1 ∧ n 1 = 9 ∧ n 2 = 27 ∧ n 3 = 3) ∨
    (n 0 = 0 ∧ n 1 = 12 ∧ n 2 = 24 ∧ n 3 = 4) := by
  dsimp only
  rcases orderFortyNine_highIncidence_profile_of_nine_high_reduced
      G hfree hmin hcard hHigh with hp | hp | hp | hp
  · exact (orderFortyNine_not_highIncidence_profile_nine_one
      G hfree hmin hcard hHigh hp).elim
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hp)

end

end Erdos85
