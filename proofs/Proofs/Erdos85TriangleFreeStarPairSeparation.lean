import Proofs.Erdos85C4FreeTrianglePartnerInvolution

/-!
# Geometry of the two Baer pairing fibers

Canonical triangle-partner pairs are ambient edges.  In contrast, two
broken (triangle-free-edge) endpoints at a common witness can never be
adjacent; under C4-freeness that witness is their unique common neighbor.
This is the geometric 00/11 separation used by the Baer relay price formula
(73rnz_cjibbf).
-/

open SimpleGraph

namespace Erdos85

/-- A canonical triangle-partner pair is an ambient edge. -/
theorem trianglePartner_pair_adj
    {V : Type*} {G : SimpleGraph V} {p x : V}
    (hx : trianglePartnerEligible G p x) :
    G.Adj x (trianglePartner G p x) :=
  (trianglePartner_spec hx).2

/-- Two endpoints carried by triangle-free edges at the same witness are
not adjacent to one another. -/
theorem triangleFreeStar_endpoints_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p x y : V}
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y) :
    ¬ G.Adj x y := by
  intro hxy
  have hx := (mem_triangleFreeNeighbors G p x).mp hpx
  have hy := (mem_triangleFreeNeighbors G p y).mp hpy
  have hymem : y ∈ G.neighborFinset p ∩ G.neighborFinset x := by
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset p y).mpr hy.1,
      (G.mem_neighborFinset x y).mpr hxy⟩
  rw [Finset.card_eq_zero.mp hx.2] at hymem
  simp at hymem

/-- In a C4-free graph, the common broken-edge witness is the unique common
neighbor of the two (necessarily distinct) endpoints. -/
theorem triangleFreeStar_commonWitness_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {p x y z : V}
    (hxy : x ≠ y)
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y)
    (hzx : G.Adj z x) (hzy : G.Adj z y) :
    p = z := by
  have hx := (mem_triangleFreeNeighbors G p x).mp hpx
  have hy := (mem_triangleFreeNeighbors G p y).mp hpy
  exact commonNeighbor_unique_of_c4Free hfree hxy
    hx.1.symm hy.1.symm hzx.symm hzy.symm

end Erdos85

#print axioms Erdos85.trianglePartner_pair_adj
#print axioms Erdos85.triangleFreeStar_endpoints_not_adj
#print axioms Erdos85.triangleFreeStar_commonWitness_unique
