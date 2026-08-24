import Proofs.Erdos85TriangleFreeStarPairSeparation
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# Matrix price of a broken Baer pair

The audit defines the Eulerian transport matrix by `H = A²(A+I)` over F₂.
A broken pair has exactly one common neighbor, so its `A²` entry is one.
Consequently its transport entry is `1 + A³`, the precise matrix content of
the K-price formula (73rnz_cjibbf).
-/

open SimpleGraph

namespace Erdos85

/-- Distinct broken-star endpoints have exactly their displayed witness as
common neighbor. -/
theorem triangleFreeStar_commonNeighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {p x y : V}
    (hxy : x ≠ y)
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hx := (mem_triangleFreeNeighbors G p x).mp hpx
  have hy := (mem_triangleFreeNeighbors G p y).mp hpy
  have hset : G.neighborFinset x ∩ G.neighborFinset y = {p} := by
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_inter.mp hz
      have hpz := triangleFreeStar_commonWitness_unique G hfree hxy hpx hpy
        ((G.mem_neighborFinset x z).mp hz'.1).symm
        ((G.mem_neighborFinset y z).mp hz'.2).symm
      exact Finset.mem_singleton.mpr hpz.symm
    · intro hz
      have hzp : z = p := Finset.mem_singleton.mp hz
      subst z
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x p).mpr hx.1.symm,
        (G.mem_neighborFinset y p).mpr hy.1.symm⟩
  rw [hset, Finset.card_singleton]

/-- **Broken-pair transport price.**  On a broken pair, the F₂ entry of
`A²(A+I)` is the constant unit plus the cubic entry `A³`. -/
theorem triangleFreeStar_transportMatrix_entry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {p x y : V}
    (hxy : x ≠ y)
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y) :
    let A := G.adjMatrix (ZMod 2)
    (A * A * (A + 1)) x y = 1 + (A * A * A) x y := by
  dsimp only
  let A := G.adjMatrix (ZMod 2)
  have hsquare : (A * A) x y = 1 := by
    rw [adjMatrix_sq_apply_eq_card_common_zmodTwo,
      triangleFreeStar_commonNeighbor_card_eq_one G hfree hxy hpx hpy]
    norm_num
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hsquare]
  exact add_comm _ _

end Erdos85

#print axioms Erdos85.triangleFreeStar_commonNeighbor_card_eq_one
#print axioms Erdos85.triangleFreeStar_transportMatrix_entry
