import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85MooreFriendship

/-!
# The canonical partial triangle-partner involution

For a fixed vertex `p`, every neighbor `x` whose edge lies in a triangle has
a unique common neighbor with `p` in a C4-free graph.  Sending `x` to that
common neighbor is the abstract form of the partial Baer involution.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Domain of the canonical partner at `p`: adjacent vertices for which a
common neighbor with `p` exists. -/
def trianglePartnerEligible {V : Type*} (G : SimpleGraph V) (p x : V) : Prop :=
  G.Adj p x ∧ ∃ y, G.Adj p y ∧ G.Adj x y

/-- The canonical common neighbor, extended by the identity off its domain. -/
def trianglePartner {V : Type*} (G : SimpleGraph V) (p x : V) : V :=
  by
    classical
    exact if h : ∃ y, G.Adj p y ∧ G.Adj x y then Classical.choose h else x

theorem trianglePartner_spec {V : Type*} {G : SimpleGraph V} {p x : V}
    (hx : trianglePartnerEligible G p x) :
    G.Adj p (trianglePartner G p x) ∧
      G.Adj x (trianglePartner G p x) := by
  rw [trianglePartner]
  simp only [dif_pos hx.2]
  exact Classical.choose_spec hx.2

/-- The canonical partner stays in the same eligible star fiber. -/
theorem trianglePartner_closed {V : Type*} {G : SimpleGraph V}
    {p x : V} (hx : trianglePartnerEligible G p x) :
    trianglePartnerEligible G p (trianglePartner G p x) := by
  have hs := trianglePartner_spec hx
  exact ⟨hs.1, x, hx.1, hs.2.symm⟩

/-- On its domain, the canonical triangle partner is an involution. -/
theorem trianglePartner_involutive {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) {p x : V}
    (hx : trianglePartnerEligible G p x) :
    trianglePartner G p (trianglePartner G p x) = x := by
  let y := trianglePartner G p x
  have hs : G.Adj p y ∧ G.Adj x y := trianglePartner_spec hx
  have hy : trianglePartnerEligible G p y := trianglePartner_closed hx
  have hys : G.Adj p (trianglePartner G p y) ∧
      G.Adj y (trianglePartner G p y) := trianglePartner_spec hy
  exact commonNeighbor_unique_of_c4Free hfree (G.ne_of_adj hs.1)
    hys.1 hys.2 hx.1 hs.2.symm

/-- The canonical triangle partner has no fixed point on its domain. -/
theorem trianglePartner_fixedPointFree {V : Type*} {G : SimpleGraph V}
    {p x : V} (hx : trianglePartnerEligible G p x) :
    trianglePartner G p x ≠ x := by
  intro h
  have hs := (trianglePartner_spec hx).2
  rw [h] at hs
  exact G.loopless.irrefl x hs

/-- The domain is exactly the complement, inside `N(p)`, of the edges lying
in no triangle. -/
theorem trianglePartnerEligible_iff_not_triangleFreeEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p x : V) :
    trianglePartnerEligible G p x ↔
      G.Adj p x ∧ ¬ (triangleFreeEdgeGraph G).Adj p x := by
  constructor
  · rintro ⟨hpx, y, hpy, hxy⟩
    refine ⟨hpx, ?_⟩
    intro hT
    have hzero := ((mem_triangleFreeNeighbors G p x).mp hT).2
    have hy : y ∈ G.neighborFinset p ∩ G.neighborFinset x := by
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset p y).mpr hpy,
        (G.mem_neighborFinset x y).mpr hxy⟩
    exact (Finset.card_ne_zero.mpr ⟨y, hy⟩) hzero
  · rintro ⟨hpx, hnotT⟩
    refine ⟨hpx, ?_⟩
    by_contra hnone
    apply hnotT
    rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
    refine ⟨hpx, Finset.card_eq_zero.mpr ?_⟩
    ext y
    constructor
    · intro hy
      have hy' := Finset.mem_inter.mp hy
      exact (hnone ⟨y, (G.mem_neighborFinset p y).mp hy'.1,
        (G.mem_neighborFinset x y).mp hy'.2⟩).elim
    · intro hy
      simp at hy

end

end Erdos85

#print axioms Erdos85.trianglePartner_closed
#print axioms Erdos85.trianglePartner_involutive
#print axioms Erdos85.trianglePartner_fixedPointFree
#print axioms Erdos85.trianglePartnerEligible_iff_not_triangleFreeEdge
