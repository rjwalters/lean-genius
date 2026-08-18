import Proofs.Erdos85PositiveExcessLocalParity
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The antipodal cycle reservoir at positive odd excess

Vertices beyond distance two form the spanning `antipodalGraph`.  In the
surviving odd-degree, odd-excess band, its degree is the unused part of the
local defect budget.  It is therefore even and at least two at every vertex.
In particular it cannot be a forest: the external repair candidates always
contain a cyclic reservoir, even when they do not form the two-regular graph
available at excess one.
-/

open SimpleGraph

namespace Erdos85

/-- The degree in the antipodal graph is exactly the number of external
repair candidates.  This identity is purely definitional. -/
theorem antipodalGraph_degree_eq_card_externalRepairCandidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (x : V) :
    (antipodalGraph G).degree x =
      (externalRepairCandidates G x).card := by
  rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
    antipodalGraph_neighborFinset, antipodalNeighbors, Finset.card_map]

/-- Exact graph-facing degree formula for the antipodal reservoir. -/
theorem antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 1 ≤ d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) :
    (antipodalGraph G).degree x =
      e + 2 - (triangleFreeNeighbors G x).card := by
  rw [antipodalGraph_degree_eq_card_externalRepairCandidates,
    card_externalRepairCandidates_eq_excess_add_two_sub_triangleFree
      G hfree hd hreg hcard x]

/-- In the surviving odd-degree, odd-excess range, every antipodal degree is
both positive even and at least two. -/
theorem antipodalGraph_degree_even_and_two_le_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (hoddD : Odd d) (hoddE : Odd e) (he : e ≤ d - 4)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) :
    Even ((antipodalGraph G).degree x) ∧
      2 ≤ (antipodalGraph G).degree x := by
  have hdegree := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
    G hfree (by omega) hreg hcard x
  have hle := triangleFreeNeighbors_card_le_excess_of_odd
    G hfree hd hoddD hoddE he hreg hcard x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree
    G hfree hreg x
  obtain ⟨a, ha⟩ := hoddD
  obtain ⟨b, hb⟩ := hoddE
  constructor
  · rw [hdegree]
    use (e + 2 - (triangleFreeNeighbors G x).card) / 2
    omega
  · rw [hdegree]
    omega

/-- The degree of a vertex inside its connected-component graph agrees with
its degree in the ambient finite graph. -/
private theorem degree_connectedComponent_toSimpleGraph_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (C : H.ConnectedComponent) [Fintype C]
    [DecidableRel C.toSimpleGraph.Adj] (x : C) :
    C.toSimpleGraph.degree x = H.degree x.1 := by
  show (C.toSimpleGraph.neighborFinset x).card =
    (H.neighborFinset x.1).card
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact hy
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hy
    exact ⟨⟨y, hyC⟩, by
      rw [SimpleGraph.mem_neighborFinset]
      exact hy, rfl⟩

/-- A finite nonempty graph of minimum degree at least two is not acyclic. -/
private theorem not_isAcyclic_of_every_degree_two_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ x, 2 ≤ H.degree x) : ¬ H.IsAcyclic := by
  intro hac
  obtain ⟨v⟩ := ‹Nonempty V›
  have hvdegree := hdegree v
  have hvpos : 0 < H.degree v := by omega
  obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v).mp hvpos
  let C : H.ConnectedComponent := H.connectedComponentMk v
  have hvC : v ∈ C.supp := rfl
  have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hvw
  haveI : Fintype C := Fintype.ofFinite C
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  haveI : Nontrivial C :=
    ⟨⟨v, hvC⟩, ⟨w, hwC⟩,
      fun heq => hvw.ne (congrArg Subtype.val heq)⟩
  have htree : C.toSimpleGraph.IsTree := hac.isTree_connectedComponent C
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hxdeg : C.toSimpleGraph.degree x = H.degree x.1 :=
    degree_connectedComponent_toSimpleGraph_eq H C x
  have hxlower := hdegree x.1
  omega

/-- The external-candidate/antipodal graph contains a cycle throughout the
surviving odd band.  This is the closed reservoir needed by cyclic or
alternating repair programs. -/
theorem antipodalGraph_not_isAcyclic_of_odd
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (hoddD : Odd d) (hoddE : Odd e) (he : e ≤ d - 4)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) :
    ¬ (antipodalGraph G).IsAcyclic := by
  apply not_isAcyclic_of_every_degree_two_le
  intro x
  exact (antipodalGraph_degree_even_and_two_le_of_odd
    G hfree hd hoddD hoddE he hreg hcard x).2

end Erdos85
