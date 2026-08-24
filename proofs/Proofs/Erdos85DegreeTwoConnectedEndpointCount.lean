import Proofs.Erdos85ThreeSeparatorFirstSlicePathCycleDecomposition

/-!
# Endpoint count in a connected degree-one/two component

This supplies the open endpoint-containing half of B22 at the numerical
level.  A connected finite graph whose degrees are all one or two has at
most two degree-one vertices by the spanning-tree edge lower bound, and an
even positive number by handshaking; hence it has exactly two.
-/

open Finset SimpleGraph

namespace Erdos85

/-- A non-cycle connected component of a finite maximum-degree-two graph
has exactly two endpoints. -/
theorem connected_degree_one_or_two_endpoint_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 1 ∨ G.degree v = 2)
    (hendpoint : ∃ v, G.degree v = 1) :
    (Finset.univ.filter fun v ↦ G.degree v = 1).card = 2 := by
  let E := Finset.univ.filter fun v ↦ G.degree v = 1
  change E.card = 2
  have hdegreeSum : (∑ v, G.degree v) + E.card = 2 * Fintype.card V := by
    have hEcard : E.card = ∑ v, if v ∈ E then 1 else 0 := by
      simp
    rw [hEcard, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _v : V, 2 := by
        apply Finset.sum_congr rfl
        intro v _hv
        rcases hdeg v with h | h <;> simp [E, h]
      _ = 2 * Fintype.card V := by simp [mul_comm]
  obtain ⟨T, hTG, hTtree⟩ := hconn.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  have htreeCard := hTtree.card_edgeFinset
  have hedgeMono : T.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hTG)
  have hendpointLe : E.card ≤ 2 := by
    rw [G.sum_degrees_eq_twice_card_edges] at hdegreeSum
    omega
  have hoddEq : ({v | Odd (G.degree v)} : Finset V) = E := by
    ext v
    rcases hdeg v with h | h <;> simp [E, h]
  have heven : Even E.card := by
    rw [← hoddEq]
    exact G.even_card_odd_degree_vertices
  have hpos : 0 < E.card := by
    obtain ⟨v, hv⟩ := hendpoint
    rw [Finset.card_pos]
    exact ⟨v, by simp [E, hv]⟩
  have hne0 : E.card ≠ 0 := Nat.ne_of_gt hpos
  have hne1 : E.card ≠ 1 := by
    intro h
    rw [h] at heven
    simp at heven
  interval_cases h : E.card <;> simp_all

#print axioms connected_degree_one_or_two_endpoint_card_eq_two

end Erdos85
