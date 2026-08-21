import Proofs.Erdos85OddSquareOrderNineThreeHighCoreOriginalEdgeConstraint

/-! # Triangle census at the three high roots of the q = 9 core

Node: B.3 / GAP B-CLASSIFY.  Every high root has degree ten and its induced
neighborhood is one-regular.  Hence it supports exactly five triangles.  In
the three-high branch the total rooted high-triangle contribution is exactly
fifteen, before the residual all-low triangles are counted.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A high root at square order `9^2` supports exactly five triangles. -/
theorem squareOrderNine_highRoot_localEdges_card_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {r : V}
    (hrH : r ∈ squareOrderHighVertices G 9) :
    (G.induce (G.neighborSet r)).edgeFinset.card = 5 := by
  let H := G.induce (G.neighborSet r)
  have hrDegree : G.degree r = 10 := (Finset.mem_filter.mp hrH).2
  have hlocal : ∀ s : {z : V // z ∈ G.neighborSet r}, H.degree s = 1 :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree (by norm_num) hmin hcard hrDegree).2.2
  have hvertices : Fintype.card {z : V // z ∈ G.neighborSet r} = 10 := by
    simpa [G.card_neighborFinset_eq_degree, hrDegree] using
      Fintype.card_coe (G.neighborFinset r)
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hsum : (∑ s : {z : V // z ∈ G.neighborSet r}, H.degree s) = 10 := by
    calc
      (∑ s : {z : V // z ∈ G.neighborSet r}, H.degree s) =
          ∑ _s : {z : V // z ∈ G.neighborSet r}, 1 := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact hlocal s
      _ = Fintype.card {z : V // z ∈ G.neighborSet r} := by simp
      _ = 10 := hvertices
  rw [hsum] at hhand
  change H.edgeFinset.card = 5
  omega

/-- Once the three high roots are named, their rooted triangle counts sum to
exactly fifteen.  High independence ensures this is also the unweighted
number of triangles containing a high vertex. -/
theorem squareOrderNine_threeHigh_localEdges_sum_eq_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81) {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9) :
    (G.induce (G.neighborSet a)).edgeFinset.card +
        (G.induce (G.neighborSet b)).edgeFinset.card +
        (G.induce (G.neighborSet c)).edgeFinset.card = 15 := by
  rw [squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard ha,
    squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard hb,
    squareOrderNine_highRoot_localEdges_card_eq_five G hfree hmin hcard hc]

/-- In the first three-high profile, the two bin-two vertices at a fixed high
root are either paired to each other, or both paired across to bin one.  Thus
the number of oriented bin-two-to-bin-one matching incidences is `0` or `2`;
the spurious intermediate value `1` is excluded by symmetry of the matching.
-/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
    let crossMass := ∑ x ∈ S,
      (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card
    crossMass = 0 ∨ crossMass = 2 := by
  classical
  dsimp only
  let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
  let K := G.induce (S : Set V)
  have hScard : S.card = 2 :=
    (squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc3 hc4 ha).2
  have hpoint : ∀ x ∈ S,
      (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card +
        (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card = 1 := by
    intro x hx
    exact squareOrderNine_threeHigh_firstProfile_binTwo_local_matching_dichotomy
      G hfree hmin hcard hp hc3 hc4
      (Finset.mem_inter.mp hx).2 ha (Finset.mem_inter.mp hx).1
  have hinternal : ∀ x : ↥(↑S : Set V),
      K.degree x =
        (G.neighborFinset a ∩ G.neighborFinset x.1 ∩
          squareOrderNineLowIncidenceBin G 2).card := by
    intro x
    rw [degree_induce_finset_eq_card_inter]
    congr 1
    ext y
    simp only [S, Finset.mem_inter]
    tauto
  have htotal :
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card) +
        (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card) = 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ S,
          ((G.neighborFinset a ∩ G.neighborFinset x ∩
              squareOrderNineLowIncidenceBin G 1).card +
            (G.neighborFinset a ∩ G.neighborFinset x ∩
              squareOrderNineLowIncidenceBin G 2).card)) =
          ∑ _x ∈ S, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpoint x hx
      _ = S.card := by simp
      _ = 2 := hScard
  have hevenInternal : Even
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 2).card) := by
    have hsum :
        (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card) =
          ∑ x : ↥(↑S : Set V), K.degree x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro x _hx
      exact (hinternal x).symm
    rw [hsum, K.sum_degrees_eq_twice_card_edges]
    exact ⟨K.edgeFinset.card, by omega⟩
  rcases hevenInternal with ⟨m, hm⟩
  have hmle : m ≤ 1 := by omega
  change
    (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
      squareOrderNineLowIncidenceBin G 1).card) = 0 ∨
    (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
      squareOrderNineLowIncidenceBin G 1).card) = 2
  interval_cases m <;> omega

/-- If the two bin-two neighbors of a high root are not paired together in
the original graph, then both matching incidences at that root cross to bin
one.  This is the pointwise bridge from the `0 ∨ 2` census to the global
three-witness obstruction below. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass_eq_two_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a x y : V} (ha : a ∈ squareOrderHighVertices G 9)
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 2)
    (hax : G.Adj a x) (hay : G.Adj a y) (hxy : x ≠ y)
    (hnotxy : ¬ G.Adj x y) :
    let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
    ∑ z ∈ S,
      (G.neighborFinset a ∩ G.neighborFinset z ∩
        squareOrderNineLowIncidenceBin G 1).card = 2 := by
  classical
  dsimp only
  let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
  have hxS : x ∈ S := Finset.mem_inter.mpr ⟨
    (G.mem_neighborFinset a x).mpr hax, hx⟩
  have hyS : y ∈ S := Finset.mem_inter.mpr ⟨
    (G.mem_neighborFinset a y).mpr hay, hy⟩
  have hScard : S.card = 2 :=
    (squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc3 hc4 ha).2
  have hSxy : S = {x, y} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hzEq : z = x ∨ z = y := by
        by_contra hzNe
        push Not at hzNe
        have hthree : ({x, y, z} : Finset V).card = 3 := by
          simp [hxy, hzNe.1.symm, hzNe.2.symm]
        have hsub : ({x, y, z} : Finset V) ⊆ S := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        omega
      simpa [hzEq]
    · rw [hScard]
      simp [hxy]
  have hcrossCases :
      (∑ z ∈ S, (G.neighborFinset a ∩ G.neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 1).card) = 0 ∨
      (∑ z ∈ S, (G.neighborFinset a ∩ G.neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 1).card) = 2 := by
    simpa [S] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 ha)
  rcases hcrossCases with hzero | htwo
  · exfalso
    have hpoint :=
      squareOrderNine_threeHigh_firstProfile_binTwo_local_matching_dichotomy
        G hfree hmin hcard hp hc3 hc4 hx ha
          ((G.mem_neighborFinset a x).mpr hax)
    have hxCrossLe :
        (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card ≤
        ∑ z ∈ S, (G.neighborFinset a ∩ G.neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 1).card := by
      let f : V → ℕ := fun z =>
        (G.neighborFinset a ∩ G.neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 1).card
      exact Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hxS
    have hxCross :
        (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card = 0 := by
      omega
    have hxInternal :
        (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card = 1 := by
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
      0 < (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 2).card)
    have hzData := Finset.mem_inter.mp hz
    have hzS : z ∈ S := Finset.mem_inter.mpr ⟨
      (Finset.mem_inter.mp hzData.1).1, hzData.2⟩
    have hzx : z ≠ x := by
      intro hzx
      subst z
      have hloop : G.Adj x x := (G.mem_neighborFinset x x).mp
        (Finset.mem_inter.mp hzData.1).2
      exact (G.ne_of_adj hloop) rfl
    have hzy : z = y := by
      rw [hSxy] at hzS
      simpa [hzx] using hzS
    exact hnotxy (hzy ▸ (G.mem_neighborFinset x z).mp
      (Finset.mem_inter.mp hzData.1).2)
  · exact htwo

/-- Conversely, zero crossing mass means that the two bin-two neighbors of
the high root are paired together. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a x y : V} (ha : a ∈ squareOrderHighVertices G 9)
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 2)
    (hax : G.Adj a x) (hay : G.Adj a y) (hxy : x ≠ y)
    (hzero :
      (∑ z ∈ G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2,
        (G.neighborFinset a ∩ G.neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 1).card) = 0) :
    G.Adj x y := by
  by_contra hnotxy
  have htwo :=
    squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass_eq_two_of_not_adj
      G hfree hmin hcard hp hhigh hc3 hc4 ha hx hy hax hay hxy hnotxy
  omega

/-- At one high root, the eight bin-one neighbors are matched either among
themselves or across to the two bin-two neighbors.  The exact handshake is
`2 * e(B₁,B₁) + crossMass = 8`. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_twice_add_crossMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let T := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 1
    let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
    2 * (G.induce (↑T : Set V)).edgeFinset.card +
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card) = 8 := by
  classical
  dsimp only
  let T := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 1
  let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
  let K := G.induce (↑T : Set V)
  have hsplit := squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
    G hfree hmin hcard hp hhigh hc3 hc4 ha
  have hTcard : T.card = 8 := hsplit.1
  have hScard : S.card = 2 := hsplit.2
  have haDegree : G.degree a = 10 := (Finset.mem_filter.mp ha).2
  have hNcard : (G.neighborFinset a).card = 10 := by
    simpa [G.card_neighborFinset_eq_degree] using haDegree
  have hdisj : Disjoint T S := by
    rw [Finset.disjoint_left]
    intro x hxT hxS
    have hx1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hxT).2).2
    have hx2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hxS).2).2
    omega
  have hunion : T ∪ S = G.neighborFinset a := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hxT | hxS
      · exact (Finset.mem_inter.mp hxT).1
      · exact (Finset.mem_inter.mp hxS).1
    · rw [Finset.card_union_of_disjoint hdisj, hTcard, hScard, hNcard]
  have hlocal : ∀ x ∈ T,
      (G.neighborFinset x ∩ T).card +
        (G.neighborFinset x ∩ S).card = 1 := by
    intro x hxT
    let H := G.induce (G.neighborSet a)
    have hxN : x ∈ G.neighborSet a :=
      (G.mem_neighborFinset a x).mp (Finset.mem_inter.mp hxT).1
    have hxDegree : H.degree ⟨x, hxN⟩ = 1 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree (by norm_num) hmin hcard haDegree).2.2 ⟨x, hxN⟩
    rw [degree_induce_neighborSet_eq_card_common] at hxDegree
    have hparts :
        (G.neighborFinset x ∩ T) ∪ (G.neighborFinset x ∩ S) =
          G.neighborFinset x ∩ G.neighborFinset a := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      rw [← hunion]
      simp only [Finset.mem_union]
      tauto
    have hpartsDisj : Disjoint (G.neighborFinset x ∩ T)
        (G.neighborFinset x ∩ S) := by
      rw [Finset.disjoint_left]
      intro y hyT hyS
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_inter.mp hyT).2 (Finset.mem_inter.mp hyS).2
    rw [← Finset.card_union_of_disjoint hpartsDisj, hparts]
    simpa [Finset.inter_comm] using hxDegree
  have hsumLocal :
      (∑ x ∈ T, (G.neighborFinset x ∩ T).card) +
        (∑ x ∈ T, (G.neighborFinset x ∩ S).card) = 8 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ T, ((G.neighborFinset x ∩ T).card +
          (G.neighborFinset x ∩ S).card)) = ∑ _x ∈ T, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hlocal x hx
      _ = T.card := by simp
      _ = 8 := hTcard
  have hinternal :
      (∑ x ∈ T, (G.neighborFinset x ∩ T).card) =
        2 * K.edgeFinset.card := by
    have hsum : (∑ x ∈ T, (G.neighborFinset x ∩ T).card) =
        ∑ x : ↥(↑T : Set V), K.degree x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [degree_induce_finset_eq_card_inter]
    rw [hsum, K.sum_degrees_eq_twice_card_edges]
  have hcrossSwap := sum_card_neighborFinset_inter_comm G T S
  have hcross :
      (∑ x ∈ T, (G.neighborFinset x ∩ S).card) =
        ∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card := by
    rw [hcrossSwap]
    apply Finset.sum_congr rfl
    intro x hxS
    congr 1
    ext y
    simp only [T, Finset.mem_inter]
    tauto
  change 2 * K.edgeFinset.card +
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card) = 8
  omega

/-- The complementary handshake on the two bin-two neighbors is
`2 * e(B₂,B₂) + crossMass = 2`. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_internal_twice_add_crossMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
    2 * (G.induce (↑S : Set V)).edgeFinset.card +
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card) = 2 := by
  classical
  dsimp only
  let S := G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2
  let K := G.induce (↑S : Set V)
  have hScard : S.card = 2 :=
    (squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc3 hc4 ha).2
  have hpoint : ∀ x ∈ S,
      (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card +
        (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card = 1 := by
    intro x hx
    exact squareOrderNine_threeHigh_firstProfile_binTwo_local_matching_dichotomy
      G hfree hmin hcard hp hc3 hc4
      (Finset.mem_inter.mp hx).2 ha (Finset.mem_inter.mp hx).1
  have htotal :
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card) +
        (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card) = 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ S,
          ((G.neighborFinset a ∩ G.neighborFinset x ∩
              squareOrderNineLowIncidenceBin G 1).card +
            (G.neighborFinset a ∩ G.neighborFinset x ∩
              squareOrderNineLowIncidenceBin G 2).card)) =
          ∑ _x ∈ S, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpoint x hx
      _ = S.card := by simp
      _ = 2 := hScard
  have hinternal :
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card) =
        2 * K.edgeFinset.card := by
    have hsum :
        (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 2).card) =
          ∑ x : ↥(↑S : Set V), K.degree x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [degree_induce_finset_eq_card_inter]
      congr 1
      ext y
      simp only [S, Finset.mem_inter]
      tauto
    rw [hsum, K.sum_degrees_eq_twice_card_edges]
  change 2 * K.edgeFinset.card +
      (∑ x ∈ S, (G.neighborFinset a ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card) = 2
  omega

/-- A bin-two vertex cannot be adjacent to three distinct high roots. -/
theorem squareOrderNine_binTwo_not_three_distinct_high_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x a b c : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hcx : G.Adj c x) : False := by
  let I := G.neighborFinset x ∩ squareOrderHighVertices G 9
  have hIcard : I.card = 2 := (Finset.mem_filter.mp hx).2
  have haI : a ∈ I := Finset.mem_inter.mpr ⟨
    (G.mem_neighborFinset x a).mpr hax.symm, ha⟩
  have hbI : b ∈ I := Finset.mem_inter.mpr ⟨
    (G.mem_neighborFinset x b).mpr hbx.symm, hb⟩
  have hcI : c ∈ I := Finset.mem_inter.mpr ⟨
    (G.mem_neighborFinset x c).mpr hcx.symm, hc⟩
  have hsub : ({a, b, c} : Finset V) ⊆ I := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact haI
    · exact hbI
    · exact hcI
  have hthree : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  have := Finset.card_le_card hsub
  omega

/-- The three pair-witnesses of the three high roots in the first profile are
distinct, and they cannot form a triangle.  Consequently it is impossible
for all three high-root matchings to pair their two bin-two vertices
internally. -/
theorem squareOrderNine_threeHigh_firstProfile_pairWitnesses_not_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x y z,
      x ∈ squareOrderNineLowIncidenceBin G 2 ∧
      y ∈ squareOrderNineLowIncidenceBin G 2 ∧
      z ∈ squareOrderNineLowIncidenceBin G 2 ∧
      G.Adj a x ∧ G.Adj b x ∧
      G.Adj a y ∧ G.Adj c y ∧
      G.Adj b z ∧ G.Adj c z ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
  rcases squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
      G hfree hmin hcard hp hc3 hc4 ha hb hab with ⟨x, hx, _⟩
  rcases squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
      G hfree hmin hcard hp hc3 hc4 ha hc hac with ⟨y, hy, _⟩
  rcases squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
      G hfree hmin hcard hp hc3 hc4 hb hc hbc with ⟨z, hz, _⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    exact squareOrderNine_binTwo_not_three_distinct_high_neighbors
      G hx.1 ha hb hc hab hac hbc hx.2.1 hx.2.2 hy.2.2
  have hxz : x ≠ z := by
    intro h
    subst z
    exact squareOrderNine_binTwo_not_three_distinct_high_neighbors
      G hx.1 ha hb hc hab hac hbc hx.2.1 hx.2.2 hz.2.2
  have hyz : y ≠ z := by
    intro h
    subst z
    exact squareOrderNine_binTwo_not_three_distinct_high_neighbors
      G hy.1 ha hb hc hab hac hbc hy.2.1 hz.2.1 hy.2.2
  refine ⟨x, y, z, hx.1, hy.1, hz.1, hx.2.1, hx.2.2,
    hy.2.1, hy.2.2, hz.2.1, hz.2.2, hxy, hxz, hyz, ?_⟩
  rintro ⟨_hxyAdj, hxzAdj, hyzAdj⟩
  have haz : a ≠ z := by
    intro h
    subst z
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz.1).1).2 ha
  have hle := common_le_one_of_not_containsC4 hfree x y hxy
  have haCommon : a ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x a).mpr hx.2.1.symm,
      (G.mem_neighborFinset y a).mpr hy.2.1.symm⟩
  have hzCommon : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x z).mpr hxzAdj,
      (G.mem_neighborFinset y z).mpr hyzAdj⟩
  have hazEq := Finset.card_le_one.mp hle a haCommon z hzCommon
  exact haz hazEq

/-- If two distinct vertices share a high root and one is defect-adjacent to
a third vertex which is originally adjacent to the other, then that defect
edge must be antipodal.  Were it also original, the shared high root and the
third vertex would be two common neighbors. -/
theorem antipodal_of_defectMate_crosses_shared_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x u y r : V}
    (hxu : x ≠ u) (hry : r ≠ y)
    (hrx : G.Adj r x) (hru : G.Adj r u)
    (hDxy : (secondOrderDefectGraph G).Adj x y)
    (hyu : G.Adj y u) :
    (antipodalGraph G).Adj x y := by
  have hnotGxy : ¬ G.Adj x y := by
    intro hxy
    have hle := common_le_one_of_not_containsC4 hfree x u hxu
    have hrCommon : r ∈ G.neighborFinset x ∩ G.neighborFinset u :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x r).mpr hrx.symm,
        (G.mem_neighborFinset u r).mpr hru.symm⟩
    have hyCommon : y ∈ G.neighborFinset x ∩ G.neighborFinset u :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x y).mpr hxy,
        (G.mem_neighborFinset u y).mpr hyu.symm⟩
    exact hry (Finset.card_le_one.mp hle r hrCommon y hyCommon)
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y at hDxy
  rcases hDxy with hanti | htf
  · exact hanti
  · exact (hnotGxy ((mem_triangleFreeNeighbors G x y).mp htf).1).elim

/-- Colored-core specialization: if a bin-two witness incident to highs
`a,b` crosses at `a` to a bin-one vertex `y`, then every defect edge from
`y` toward a bin-one vertex of color `b` is antipodal. -/
theorem squareOrderNine_binTwo_cross_forces_otherColor_defectEdge_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {a b x y p : V}
    (hb : b ∈ squareOrderHighVertices G 9)
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hp : p ∈ squareOrderNineLowIncidenceBin G 1)
    (_hax : G.Adj a x) (hbx : G.Adj b x)
    (_hay : G.Adj a y) (hby : G.Adj b p)
    (hyx : G.Adj y x)
    (hDyp : (secondOrderDefectGraph G).Adj y p) :
    (antipodalGraph G).Adj y p := by
  have hpx : p ≠ x := by
    intro h
    subst p
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hx).2
    omega
  have hbyNe : b ≠ y := by
    intro h
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 hb
  have hanti : (antipodalGraph G).Adj p y :=
    antipodal_of_defectMate_crosses_shared_high
      G hfree hpx hbyNe hby hbx hDyp.symm hyx
  exact hanti.symm

/-- Every bin-one vertex has even antipodal degree. -/
theorem squareOrderNine_binOne_antipodalNeighbors_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81) {y : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1) :
    Even (antipodalNeighbors G y).card := by
  rcases squareOrderNine_binOne_triangle_defect_profile
      G hfree hmin hcover hcard hy with h | h | h | h
  · rw [h.1]
    exact ⟨0, by omega⟩
  · rw [h.1]
    exact ⟨1, by omega⟩
  · rw [h.1]
    exact ⟨2, by omega⟩
  · rw [h.1]
    exact ⟨3, by omega⟩

/-- Once one antipodal neighbor of a bin-one vertex is known, parity forces
a second, distinct antipodal neighbor. -/
theorem squareOrderNine_binOne_exists_second_antipodalNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81) {y p : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hp : p ∈ antipodalNeighbors G y) :
    ∃ q ∈ antipodalNeighbors G y, q ≠ p := by
  classical
  have heven := squareOrderNine_binOne_antipodalNeighbors_card_even
    G hfree hmin hcover hcard hy
  have hpos : 0 < (antipodalNeighbors G y).card :=
    Finset.card_pos.mpr ⟨p, hp⟩
  rcases heven with ⟨k, hk⟩
  have hgt : 1 < (antipodalNeighbors G y).card := by omega
  have herase : ((antipodalNeighbors G y).erase p).card =
      (antipodalNeighbors G y).card - 1 :=
    Finset.card_erase_of_mem hp
  have herasePos : 0 < ((antipodalNeighbors G y).erase p).card := by
    rw [herase]
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp herasePos
  exact ⟨q, Finset.mem_of_mem_erase hq, (Finset.mem_erase.mp hq).1⟩

/-- A crossing endpoint in the colored core has a forced antipodal edge
toward the witness's other color, and hence a second antipodal neighbor. -/
theorem squareOrderNine_binTwo_cross_forces_second_antipodalNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    {a b x y p : V}
    (hb : b ∈ squareOrderHighVertices G 9)
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hp : p ∈ squareOrderNineLowIncidenceBin G 1)
    (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hby : G.Adj b p)
    (hyx : G.Adj y x)
    (hDyp : (secondOrderDefectGraph G).Adj y p) :
    ∃ q ∈ antipodalNeighbors G y, q ≠ p := by
  have hypAnti : (antipodalGraph G).Adj y p :=
    squareOrderNine_binTwo_cross_forces_otherColor_defectEdge_antipodal
      G hfree hb hx hy hp hax hbx hay hby hyx hDyp
  apply squareOrderNine_binOne_exists_second_antipodalNeighbor
    G hfree hmin hcover hcard hy
  simpa [antipodalGraph_adj] using hypAnti

/-- For the three pair-witnesses `x_ab,x_ac,x_bc`, an exceptional bin-one
mate opposite `a` is forced antipodal to `x_bc` whenever it is used as a
crossing partner at `a`. -/
theorem squareOrderNine_threeHigh_firstProfile_exceptional_cross_forces_antipodal_mate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {b c xab xac xbc e : V}
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (he : e ∈ squareOrderNineLowIncidenceBin G 1)
    (hxab_b : G.Adj b xab) (hxbc_b : G.Adj b xbc)
    (hxac_c : G.Adj c xac) (hxbc_c : G.Adj c xbc)
    (hxab_ne_xbc : xab ≠ xbc) (hxac_ne_xbc : xac ≠ xbc)
    (hDmate : (secondOrderDefectGraph G).Adj xbc e)
    (hcross : G.Adj e xab ∨ G.Adj e xac) :
    (antipodalGraph G).Adj xbc e := by
  have hbe : b ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).2 hb
  have hce : c ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).2 hc
  rcases hcross with heab | heac
  · exact antipodal_of_defectMate_crosses_shared_high
      G hfree hxab_ne_xbc.symm hbe hxbc_b hxab_b hDmate heab
  · exact antipodal_of_defectMate_crosses_shared_high
      G hfree hxac_ne_xbc.symm hce hxbc_c hxac_c hDmate heac

/-- In the first three-high profile, at least one high root uses the crossing
matching option: its two bin-two neighbors are both matched to bin one.
Indeed the three pair-witnesses cannot form a triangle, and a missing edge at
one pair's common high root forces cross-mass two there. -/
theorem squareOrderNine_threeHigh_firstProfile_some_highRoot_binTwo_crossMass_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let crossMass := fun r : V =>
      ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
        (G.neighborFinset r ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card
    crossMass a = 2 ∨ crossMass b = 2 ∨ crossMass c = 2 := by
  classical
  dsimp only
  obtain ⟨x, y, z, hx, hy, hz, hax, hbx, hay, hcy, hbz, hcz,
      hxy, hxz, hyz, hnotTriangle⟩ :=
    squareOrderNine_threeHigh_firstProfile_pairWitnesses_not_triangle
      G hfree hmin hcard hp hc3 hc4 ha hb hc hab hac hbc
  have hmissing : ¬ G.Adj x y ∨ ¬ G.Adj x z ∨ ¬ G.Adj y z := by
    tauto
  rcases hmissing with hnxy | hnxz | hnyz
  · exact Or.inl
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass_eq_two_of_not_adj
        G hfree hmin hcard hp hhigh hc3 hc4 ha hx hy hax hay hxy hnxy)
  · exact Or.inr (Or.inl
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass_eq_two_of_not_adj
        G hfree hmin hcard hp hhigh hc3 hc4 hb hx hz hbx hbz hxz hnxz))
  · exact Or.inr (Or.inr
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass_eq_two_of_not_adj
        G hfree hmin hcard hp hhigh hc3 hc4 hc hy hz hcy hcz hyz hnyz))

/-- The total number of oriented bin-two-to-bin-one matching incidences over
the three high roots is `2`, `4`, or `6`.  The value zero is excluded by the
three-witness obstruction. -/
theorem squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let crossMass := fun r : V =>
      ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
        (G.neighborFinset r ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card
    crossMass a + crossMass b + crossMass c = 2 ∨
      crossMass a + crossMass b + crossMass c = 4 ∨
      crossMass a + crossMass b + crossMass c = 6 := by
  classical
  dsimp only
  let crossMass := fun r : V =>
    ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
      (G.neighborFinset r ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card
  change crossMass a + crossMass b + crossMass c = 2 ∨
    crossMass a + crossMass b + crossMass c = 4 ∨
    crossMass a + crossMass b + crossMass c = 6
  have haCases : crossMass a = 0 ∨ crossMass a = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 ha)
  have hbCases : crossMass b = 0 ∨ crossMass b = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hb)
  have hcCases : crossMass c = 0 ∨ crossMass c = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hc)
  have hsome : crossMass a = 2 ∨ crossMass b = 2 ∨ crossMass c = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_some_highRoot_binTwo_crossMass_eq_two
        G hfree hmin hcard hp hhigh hc3 hc4 ha hb hc hab hac hbc)
  rcases haCases with ha0 | ha2 <;>
    rcases hbCases with hb0 | hb2 <;>
      rcases hcCases with hc0 | hc2 <;> omega

/-- C4-freeness rules out two internal pairings among the three bin-two
pair-witnesses.  Therefore at least two high roots use the crossing option,
and the total crossing mass sharpens from `2/4/6` to `4/6`. -/
theorem squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass_eq_four_or_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let crossMass := fun r : V =>
      ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
        (G.neighborFinset r ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card
    crossMass a + crossMass b + crossMass c = 4 ∨
      crossMass a + crossMass b + crossMass c = 6 := by
  classical
  dsimp only
  let crossMass := fun r : V =>
    ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
      (G.neighborFinset r ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card
  change crossMass a + crossMass b + crossMass c = 4 ∨
    crossMass a + crossMass b + crossMass c = 6
  obtain ⟨x, y, z, hx, hy, hz, hax, hbx, hay, hcy, hbz, hcz,
      hxy, hxz, hyz, _hnotTriangle⟩ :=
    squareOrderNine_threeHigh_firstProfile_pairWitnesses_not_triangle
      G hfree hmin hcard hp hc3 hc4 ha hb hc hab hac hbc
  have hxc : x ≠ c := by
    intro h
    subst x
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2 hc
  have hyb : y ≠ b := by
    intro h
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 hb
  have hza : z ≠ a := by
    intro h
    subst z
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2 ha
  have hn_xy_xz : ¬ (G.Adj x y ∧ G.Adj x z) := by
    rintro ⟨hxyAdj, hxzAdj⟩
    have hle := common_le_one_of_not_containsC4 hfree y z hyz
    have hcCommon : c ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y c).mpr hcy.symm,
        (G.mem_neighborFinset z c).mpr hcz.symm⟩
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr hxyAdj.symm,
        (G.mem_neighborFinset z x).mpr hxzAdj.symm⟩
    have hcx := Finset.card_le_one.mp hle c hcCommon x hxCommon
    exact hxc hcx.symm
  have hn_xy_yz : ¬ (G.Adj x y ∧ G.Adj y z) := by
    rintro ⟨hxyAdj, hyzAdj⟩
    have hle := common_le_one_of_not_containsC4 hfree x z hxz
    have hbCommon : b ∈ G.neighborFinset x ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x b).mpr hbx.symm,
        (G.mem_neighborFinset z b).mpr hbz.symm⟩
    have hyCommon : y ∈ G.neighborFinset x ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x y).mpr hxyAdj,
        (G.mem_neighborFinset z y).mpr hyzAdj.symm⟩
    have hby := Finset.card_le_one.mp hle b hbCommon y hyCommon
    exact hyb hby.symm
  have hn_xz_yz : ¬ (G.Adj x z ∧ G.Adj y z) := by
    rintro ⟨hxzAdj, hyzAdj⟩
    have hle := common_le_one_of_not_containsC4 hfree x y hxy
    have haCommon : a ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x a).mpr hax.symm,
        (G.mem_neighborFinset y a).mpr hay.symm⟩
    have hzCommon : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x z).mpr hxzAdj,
        (G.mem_neighborFinset y z).mpr hyzAdj⟩
    have haz := Finset.card_le_one.mp hle a haCommon z hzCommon
    exact hza haz.symm
  have haCases : crossMass a = 0 ∨ crossMass a = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 ha)
  have hbCases : crossMass b = 0 ∨ crossMass b = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hb)
  have hcCases : crossMass c = 0 ∨ crossMass c = 2 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hc)
  have hn_ab_zero : ¬ (crossMass a = 0 ∧ crossMass b = 0) := by
    rintro ⟨ha0, hb0⟩
    apply hn_xy_xz
    exact ⟨
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 ha hx hy hax hay hxy
          (by simpa [crossMass] using ha0),
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 hb hx hz hbx hbz hxz
          (by simpa [crossMass] using hb0)⟩
  have hn_ac_zero : ¬ (crossMass a = 0 ∧ crossMass c = 0) := by
    rintro ⟨ha0, hc0⟩
    apply hn_xy_yz
    exact ⟨
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 ha hx hy hax hay hxy
          (by simpa [crossMass] using ha0),
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 hc hy hz hcy hcz hyz
          (by simpa [crossMass] using hc0)⟩
  have hn_bc_zero : ¬ (crossMass b = 0 ∧ crossMass c = 0) := by
    rintro ⟨hb0, hc0⟩
    apply hn_xz_yz
    exact ⟨
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 hb hx hz hbx hbz hxz
          (by simpa [crossMass] using hb0),
      squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_adj_of_crossMass_eq_zero
        G hfree hmin hcard hp hhigh hc3 hc4 hc hy hz hcy hcz hyz
          (by simpa [crossMass] using hc0)⟩
  rcases haCases with ha0 | ha2 <;>
    rcases hbCases with hb0 | hb2 <;>
      rcases hcCases with hc0 | hc2 <;> omega

/-- Consequently, the three high roots support exactly nine or ten triangles
whose other two vertices both lie in bin one. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_edges_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let internal := fun r : V =>
      (G.induce (↑(G.neighborFinset r ∩
        squareOrderNineLowIncidenceBin G 1) : Set V)).edgeFinset.card
    internal a + internal b + internal c = 9 ∨
      internal a + internal b + internal c = 10 := by
  classical
  dsimp only
  let internal := fun r : V =>
    (G.induce (↑(G.neighborFinset r ∩
      squareOrderNineLowIncidenceBin G 1) : Set V)).edgeFinset.card
  let crossMass := fun r : V =>
    ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
      (G.neighborFinset r ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card
  change internal a + internal b + internal c = 9 ∨
    internal a + internal b + internal c = 10
  have haHandshake : 2 * internal a + crossMass a = 8 := by
    simpa [internal, crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_twice_add_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 ha)
  have hbHandshake : 2 * internal b + crossMass b = 8 := by
    simpa [internal, crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_twice_add_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hb)
  have hcHandshake : 2 * internal c + crossMass c = 8 := by
    simpa [internal, crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_twice_add_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hc)
  have hcross : crossMass a + crossMass b + crossMass c = 4 ∨
      crossMass a + crossMass b + crossMass c = 6 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass_eq_four_or_six
        G hfree hmin hcard hp hhigh hc3 hc4 ha hb hc hab hac hbc)
  omega

/-- Full high-root triangle-type ledger for the first profile.  Across the
three high roots, the only possibilities for
`(B₁-B₁ edges, B₂-B₁ edges, B₂-B₂ edges)` are `(10,4,1)` and `(9,6,0)`. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_triangle_type_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hc : c ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let internalOne := fun r : V =>
      (G.induce (↑(G.neighborFinset r ∩
        squareOrderNineLowIncidenceBin G 1) : Set V)).edgeFinset.card
    let crossMass := fun r : V =>
      ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
        (G.neighborFinset r ∩ G.neighborFinset x ∩
          squareOrderNineLowIncidenceBin G 1).card
    let internalTwo := fun r : V =>
      (G.induce (↑(G.neighborFinset r ∩
        squareOrderNineLowIncidenceBin G 2) : Set V)).edgeFinset.card
    (internalOne a + internalOne b + internalOne c = 10 ∧
        crossMass a + crossMass b + crossMass c = 4 ∧
        internalTwo a + internalTwo b + internalTwo c = 1) ∨
      (internalOne a + internalOne b + internalOne c = 9 ∧
        crossMass a + crossMass b + crossMass c = 6 ∧
        internalTwo a + internalTwo b + internalTwo c = 0) := by
  classical
  dsimp only
  let internalOne := fun r : V =>
    (G.induce (↑(G.neighborFinset r ∩
      squareOrderNineLowIncidenceBin G 1) : Set V)).edgeFinset.card
  let crossMass := fun r : V =>
    ∑ x ∈ G.neighborFinset r ∩ squareOrderNineLowIncidenceBin G 2,
      (G.neighborFinset r ∩ G.neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 1).card
  let internalTwo := fun r : V =>
    (G.induce (↑(G.neighborFinset r ∩
      squareOrderNineLowIncidenceBin G 2) : Set V)).edgeFinset.card
  change (internalOne a + internalOne b + internalOne c = 10 ∧
      crossMass a + crossMass b + crossMass c = 4 ∧
      internalTwo a + internalTwo b + internalTwo c = 1) ∨
    (internalOne a + internalOne b + internalOne c = 9 ∧
      crossMass a + crossMass b + crossMass c = 6 ∧
      internalTwo a + internalTwo b + internalTwo c = 0)
  have oneHandshake (r : V) (hr : r ∈ squareOrderHighVertices G 9) :
      2 * internalOne r + crossMass r = 8 := by
    simpa [internalOne, crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_twice_add_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hr)
  have twoHandshake (r : V) (hr : r ∈ squareOrderHighVertices G 9) :
      2 * internalTwo r + crossMass r = 2 := by
    simpa [internalTwo, crossMass] using
      (squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_internal_twice_add_crossMass
        G hfree hmin hcard hp hhigh hc3 hc4 hr)
  have hcross : crossMass a + crossMass b + crossMass c = 4 ∨
      crossMass a + crossMass b + crossMass c = 6 := by
    simpa [crossMass] using
      (squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass_eq_four_or_six
        G hfree hmin hcard hp hhigh hc3 hc4 ha hb hc hab hac hbc)
  have haOne := oneHandshake a ha
  have hbOne := oneHandshake b hb
  have hcOne := oneHandshake c hc
  have haTwo := twoHandshake a ha
  have hbTwo := twoHandshake b hb
  have hcTwo := twoHandshake c hc
  omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_highRoot_localEdges_card_eq_five
#print axioms Erdos85.squareOrderNine_threeHigh_localEdges_sum_eq_fifteen
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
#print axioms Erdos85.squareOrderNine_binTwo_not_three_distinct_high_neighbors
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_pairWitnesses_not_triangle
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_some_highRoot_binTwo_crossMass_eq_two
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_total_binTwo_crossMass_eq_four_or_six
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_highRoot_binOne_internal_edges_sum
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_highRoot_triangle_type_vector
#print axioms Erdos85.antipodal_of_defectMate_crosses_shared_high
#print axioms
  Erdos85.squareOrderNine_binTwo_cross_forces_otherColor_defectEdge_antipodal
#print axioms Erdos85.squareOrderNine_binOne_antipodalNeighbors_card_even
#print axioms Erdos85.squareOrderNine_binOne_exists_second_antipodalNeighbor
#print axioms Erdos85.squareOrderNine_binTwo_cross_forces_second_antipodalNeighbor
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_exceptional_cross_forces_antipodal_mate
