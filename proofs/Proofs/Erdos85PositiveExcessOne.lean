import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85SecondOrderColorTrace

/-!
# The excess-one local dichotomy

For a regular `C₄`-free graph of order `d(d-1)+4`, the combined defect graph
is cubic.  When `d` is odd, the triangle-free part of the defect at each
vertex consequently has size one or three.  If moreover `d ≡ 3 (mod 6)`,
the value three must occur: otherwise the graph of triangular edges would be
locally linear with an edge count not divisible by three.

This is the uniform first half of the excess-one obstruction of Boza, phrased
in the defect-graph vocabulary used by the rest of the Erdős 85 development.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At positive excess one and odd degree, exactly one or three incident
edges at every vertex lie in no triangle. -/
theorem excessOne_triangleFreeNeighbors_card_eq_one_or_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (triangleFreeNeighbors G x).card = 1 ∨
      (triangleFreeNeighbors G x).card = 3 := by
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  let H := G.induce (G.neighborSet x)
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
        2 * H.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hle : (triangleFreeNeighbors G x).card ≤ 3 := by
    have hsub : triangleFreeNeighbors G x ⊆
        (secondOrderDefectGraph G).neighborFinset x := by
      intro y hy
      rw [secondOrderDefectGraph_neighborFinset]
      exact Finset.mem_union_right _ hy
    calc
      (triangleFreeNeighbors G x).card ≤
          ((secondOrderDefectGraph G).neighborFinset x).card :=
        Finset.card_le_card hsub
      _ = (secondOrderDefectGraph G).degree x :=
        (secondOrderDefectGraph G).card_neighborFinset_eq_degree x
      _ = 3 := by
        simpa using secondOrderDefectGraph_degree_eq_excess_add_two
          G hfree hreg (e := 1) (by simpa using hcard) x
  have hdmod : d % 2 = 1 := Nat.odd_iff.mp hodd
  have htfmod : (triangleFreeNeighbors G x).card % 2 = 1 := by
    rw [hhand] at hsum
    omega
  omega

/-- In the `d ≡ 3 (mod 6)` excess-one regime, some vertex has three
triangle-free incident edges.  The alternative would make all triangular
edges a locally linear graph whose edge count is simultaneously and is not
divisible by three. -/
theorem exists_excessOne_triangleFreeNeighbors_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hmod : d % 6 = 3) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    ∃ x : V, (triangleFreeNeighbors G x).card = 3 := by
  classical
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  by_contra hnone
  push_neg at hnone
  have hone : ∀ x : V, (triangleFreeNeighbors G x).card = 1 := by
    intro x
    rcases excessOne_triangleFreeNeighbors_card_eq_one_or_three
        G hfree hodd hreg hcard x with hx | hx
    · exact hx
    · exact (hnone x hx).elim
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  have hsumG : ∑ x : V, G.degree x = Fintype.card V * d := by
    simp_rw [hreg]
    simp
  have hedgeG : 2 * G.edgeFinset.card = Fintype.card V * d := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
    exact hsumG
  have hTdeg : ∀ x : V, T.degree x = 1 := by
    intro x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact hone x
  have hsumT : ∑ x : V, T.degree x = Fintype.card V := by
    simp_rw [hTdeg]
    simp
  have hedgeT : 2 * T.edgeFinset.card = Fintype.card V := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges T]
    exact hsumT
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    have hlecard : T.edgeFinset.card ≤ G.edgeFinset.card :=
      Finset.card_le_card (edgeFinset_mono hTle)
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htri : H.edgeFinset.card = 3 * (H.cliqueFinset 3).card :=
    hlocal.card_edgeFinset
  have hdform : d = 6 * (d / 6) + 3 := by omega
  have hdmod3 : d % 3 = 0 := by omega
  have hdminus : (d - 1) % 3 = 2 := by omega
  have hnmod : Fintype.card V % 3 = 1 := by
    rw [hcard, Nat.add_mod, Nat.mul_mod, hdmod3, hdminus]
  have hd1 : 1 ≤ d := by omega
  have hprod : Fintype.card V * d =
      Fintype.card V * (d - 1) + Fintype.card V := by
    calc
      Fintype.card V * d = Fintype.card V * ((d - 1) + 1) := by
        rw [Nat.sub_add_cancel hd1]
      _ = Fintype.card V * (d - 1) + Fintype.card V := by ring
  have harith : 2 * H.edgeFinset.card = Fintype.card V * (d - 1) := by
    omega
  have hlmod : (2 * H.edgeFinset.card) % 3 = 0 := by
    rw [htri]
    omega
  have hrmod : (Fintype.card V * (d - 1)) % 3 = 2 := by
    rw [Nat.mul_mod, hnmod, hdminus]
  have := congrArg (· % 3) harith
  omega

end

end Erdos85
