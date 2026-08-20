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

end

end Erdos85

#print axioms Erdos85.squareOrderNine_highRoot_localEdges_card_eq_five
#print axioms Erdos85.squareOrderNine_threeHigh_localEdges_sum_eq_fifteen
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_highRoot_binTwo_crossMass
