import Proofs.Erdos85BinarySquareConnectedOwnerComplement

/-!
# Triangle-free degree weighted-neighbor terminal

The remaining combinatorial target is a single weighted-neighbor identity.
This file proves that identity is incompatible with connected second-order
defect at binary square order.  It is a consumer, not a proof of the target.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If ambient adjacency sends the triangle-free degree vector to the
constant `(q^2-4)/3`, then its cleared affine translate is an adjacency
kernel vector. -/
theorem binarySquare_triangleFreeDegree_affine_mem_adj_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (htarget : (G.adjMatrix ℚ).mulVec
        (fun x => ((triangleFreeEdgeGraph G).degree x : ℚ)) =
      fun _ => ((q : ℚ) ^ 2 - 4) / 3) :
    (G.adjMatrix ℚ).mulVec (fun x =>
      3 * (q : ℚ) * ((triangleFreeEdgeGraph G).degree x : ℚ) -
        ((q : ℚ) ^ 2 - 4)) = 0 := by
  funext x
  have hrow := G.adjMatrix_mulVec_const_apply (α := ℚ)
    (v := x) (a := 1)
  rw [hreg x] at hrow
  have htargetx := congrFun htarget x
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at htargetx ⊢
  calc
    (∑ y, G.adjMatrix ℚ x y *
        (3 * (q : ℚ) * ((triangleFreeEdgeGraph G).degree y : ℚ) -
          ((q : ℚ) ^ 2 - 4))) =
        3 * (q : ℚ) *
          (∑ y, G.adjMatrix ℚ x y *
            ((triangleFreeEdgeGraph G).degree y : ℚ)) -
        ((q : ℚ) ^ 2 - 4) * (∑ y, G.adjMatrix ℚ x y) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = 0 := by
      rw [htargetx]
      have hrow' : ∑ y, G.adjMatrix ℚ x y = (q : ℚ) := by
        simpa [Matrix.mulVec, dotProduct] using hrow
      rw [hrow']
      ring

/-- **Conditional weighted-neighbor terminal.**  In the connected binary
square-order branch, the identity `A deg_K = ((q^2-4)/3) 1` is impossible.
Equivalently, some vertex has nonconstant triangle-free-degree mass across
its ambient neighborhood. -/
theorem false_of_binarySquare_connected_triangleFreeDegree_weightedNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 3 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (a : (secondOrderDefectGraph G).ConnectedComponent)
    (htarget : (G.adjMatrix ℚ).mulVec
        (fun x => ((triangleFreeEdgeGraph G).degree x : ℚ)) =
      fun _ => (((2 ^ k : ℕ) : ℚ) ^ 2 - 4) / 3) : False := by
  let q : ℕ := 2 ^ k
  let v : V → ℚ := fun x =>
    3 * (q : ℚ) * ((triangleFreeEdgeGraph G).degree x : ℚ) -
      ((q : ℚ) ^ 2 - 4)
  have hvker : (G.adjMatrix ℚ).mulVec v = 0 := by
    exact binarySquare_triangleFreeDegree_affine_mem_adj_kernel
      G hreg htarget
  have hq8 : 8 ≤ q := by
    change 8 ≤ 2 ^ k
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hfinrank :
      Module.finrank ℚ (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) = 0 :=
    binarySquare_regular_oneComponent_finrank_adj_kernel_eq_zero
      G hfree (by omega) hreg hcard hcount a
  have hkerbot : LinearMap.ker (G.adjMatrix ℚ).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hfinrank
  have hvmem : v ∈ LinearMap.ker (G.adjMatrix ℚ).mulVecLin := hvker
  have hvzero : v = 0 := by
    rw [hkerbot] at hvmem
    exact hvmem
  have hVpos : 0 < Fintype.card V := by
    rw [hcard]
    positivity
  let x : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
  have hx := congrFun hvzero x
  change 3 * (q : ℚ) * ((triangleFreeEdgeGraph G).degree x : ℚ) -
      ((q : ℚ) ^ 2 - 4) = 0 at hx
  have hxZ : 3 * (q : ℤ) * ((triangleFreeEdgeGraph G).degree x : ℤ) =
      (q : ℤ) ^ 2 - 4 := by
    exact_mod_cast (sub_eq_zero.mp hx)
  have hdivZ : (q : ℤ) ∣ 4 := by
    have hq2 : (q : ℤ) ∣ (q : ℤ) ^ 2 := by
      use q
      ring
    have hterm : (q : ℤ) ∣
        3 * (q : ℤ) * ((triangleFreeEdgeGraph G).degree x : ℤ) := by
      use 3 * ((triangleFreeEdgeGraph G).degree x : ℤ)
      ring
    have hsub := dvd_sub hq2 hterm
    have heq : (q : ℤ) ^ 2 -
        3 * (q : ℤ) * ((triangleFreeEdgeGraph G).degree x : ℤ) = 4 := by
      linarith
    rwa [heq] at hsub
  have hqle : q ≤ 4 := by
    have := Int.natAbs_le_of_dvd_ne_zero hdivZ (by norm_num : (4 : ℤ) ≠ 0)
    simpa using this
  omega

end

end Erdos85

#print axioms Erdos85.binarySquare_triangleFreeDegree_affine_mem_adj_kernel
#print axioms Erdos85.false_of_binarySquare_connected_triangleFreeDegree_weightedNeighbor
