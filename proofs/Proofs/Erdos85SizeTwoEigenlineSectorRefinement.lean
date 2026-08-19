import Proofs.Erdos85SizeTwoEigenlineGridInstantiation

/-!
# Triangle-free-sector refinement for size-two eigenline grids

The all-triangle classification assumes both internal cycle edges at every
coordinate have exterior grid witnesses.  In the general sector, failure of
such a witness is not arbitrary: on an internal edge it is exactly membership
in the ambient triangle-free edge graph.  This file records that q-generic
correction term.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (antipodalGraph G).Adj]
variable [DecidableRel (triangleFreeEdgeGraph G).Adj]
variable [Fintype (secondOrderDefectGraph G).ConnectedComponent]
variable [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]

/-- Abstract local form: if every common neighbour of an internal edge lies
outside the chosen support, then a missing grid cell is exactly a
triangle-free internal edge. -/
theorem gridHole_iff_triangleFreeEdge_of_common_not_mem
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {q : ℕ} (pval nval : ZMod q → V)
    (x y : ZMod q) (hxy : G.Adj (pval x) (nval y))
    (hout : ∀ z, G.Adj (pval x) z → G.Adj (nval y) z → z ∉ c.supp) :
    (¬ ∃ u, IsGridWitness G c pval nval u x y) ↔
      (triangleFreeEdgeGraph G).Adj (pval x) (nval y) := by
  classical
  rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
  constructor
  · intro hhole
    refine ⟨hxy, ?_⟩
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hz' := Finset.mem_inter.mp hz
    have hpz := (G.mem_neighborFinset (pval x) z).mp hz'.1
    have hnz := (G.mem_neighborFinset (nval y) z).mp hz'.2
    exact hhole ⟨z, hout z hpz hnz, hpz.symm, hnz.symm⟩
  · rintro ⟨-, hzero⟩ ⟨u, huout, hup, hun⟩
    have hu : u ∈ G.neighborFinset (pval x) ∩
        G.neighborFinset (nval y) := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hup.symm, hun.symm⟩
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hu
    simp at hu

/-- In an alternating size-two component, a common neighbour of an internal
positive-negative edge cannot lie in the component support. -/
theorem eigenline_internalEdge_commonNeighbor_not_mem
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    {p n z : V} (hp : p ∈ c.supp) (hn : n ∈ c.supp)
    (hps : s p = 1) (hns : s n = -1)
    (hpz : G.Adj p z) (hnz : G.Adj n z) : z ∉ c.supp := by
  intro hz
  have hpflip := (internal_alternation G hfree hq hreg hcard c hc s
    hs_in hs_out hA_in hp).2 z (by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset p z).mpr hpz,
        (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hz⟩)
  have hnflip := (internal_alternation G hfree hq hreg hcard c hc s
    hs_in hs_out hA_in hn).2 z (by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset n z).mpr hnz,
        (SimpleGraph.ConnectedComponent.mem_supp_iff c z).mp hz⟩)
  rw [hps] at hpflip
  rw [hns] at hnflip
  omega

/-- Graph-facing sector law.  Along every standard internal `H`-edge, the
two formerly assumed witness conditions are equivalent to saying that the
corresponding edge is not triangle-free. -/
theorem eigenline_gridHole_iff_triangleFreeEdge
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (pval nval : ZMod q → V)
    (hp : ∀ x, pval x ∈ c.supp ∧ s (pval x) = 1)
    (hn : ∀ y, nval y ∈ c.supp ∧ s (nval y) = -1)
    (x y : ZMod q) (hxy : G.Adj (pval x) (nval y)) :
    (¬ ∃ u, IsGridWitness G c pval nval u x y) ↔
      (triangleFreeEdgeGraph G).Adj (pval x) (nval y) := by
  apply gridHole_iff_triangleFreeEdge_of_common_not_mem
    G c pval nval x y hxy
  intro z hpz hnz
  exact eigenline_internalEdge_commonNeighbor_not_mem G hfree hq hreg hcard
    c hc s hs_in hs_out hA_in (hp x).1 (hn y).1 (hp x).2 (hn y).2 hpz hnz

end

end Erdos85

#print axioms Erdos85.gridHole_iff_triangleFreeEdge_of_common_not_mem
#print axioms Erdos85.eigenline_internalEdge_commonNeighbor_not_mem
#print axioms Erdos85.eigenline_gridHole_iff_triangleFreeEdge
