import Proofs.Erdos85NearTwinPrivateRowPropagation
import Proofs.Erdos85DegreeTwoThreeEqualRowsImpossible

/-! # A two-step near-twin private cycle is impossible for an owner color -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A two-step segment of the private-pair cycle already closes the λ=6
owner-color terminal.  Starting from an equal owner row at `x,y`, the first
near-twin step transports it to `u,v`; if the private pair of `u,v` is `y,z`,
the second step gives three distinct equal rows in the two-regular owner
graph, which is impossible.

The hypotheses name the directed private neighbors explicitly.  Consequently
a component classification need only provide codegrees and the four stated
membership facts; all matrix propagation and the terminal contradiction are
contained here. -/
theorem sevenRegular_privateCycle_twoStep_ownerColor_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (D H : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel H.Adj]
    (hDreg : ∀ a, D.degree a = 7)
    (hHreg : ∀ a, H.degree a = 2)
    (hcomm : D.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * D.adjMatrix ℤ)
    {x y z u v : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyCommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (huXY : u ∈ D.neighborFinset x \ D.neighborFinset y)
    (hvYX : v ∈ D.neighborFinset y \ D.neighborFinset x)
    (huvCommon : (D.neighborFinset u ∩ D.neighborFinset v).card = 6)
    (hyUV : y ∈ D.neighborFinset u \ D.neighborFinset v)
    (hzVU : z ∈ D.neighborFinset v \ D.neighborFinset u)
    (hxyRows : H.neighborFinset x = H.neighborFinset y) : False := by
  classical
  have hxyMatrixRows : ∀ w, H.adjMatrix ℤ x w = H.adjMatrix ℤ y w := by
    intro w
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    have hiff : H.Adj x w ↔ H.Adj y w := by
      rw [← H.mem_neighborFinset, ← H.mem_neighborFinset, hxyRows]
    by_cases hxw : H.Adj x w <;> by_cases hyw : H.Adj y w <;>
      simp_all
  obtain ⟨p, q, hpq, hpXY, hqYX, hpqRows⟩ :=
    sevenRegular_nearTwin_equal_commutingRows_propagate_private
      D hDreg hxyCommon (H.adjMatrix ℤ) hcomm hxyMatrixRows
  obtain ⟨p₀, q₀, hpSet, hqSet, _hp₀q₀, _⟩ :=
    sevenRegular_nearTwin_privateNeighbor_normalization D hDreg hxyCommon
  have hpu : p = u := by
    have hp' := hpXY
    have hu' := huXY
    rw [hpSet] at hp' hu'
    exact (Finset.mem_singleton.mp hp').trans
      (Finset.mem_singleton.mp hu').symm
  have hqv : q = v := by
    have hq' := hqYX
    have hv' := hvYX
    rw [hqSet] at hq' hv'
    exact (Finset.mem_singleton.mp hq').trans
      (Finset.mem_singleton.mp hv').symm
  have huvMatrixRows : ∀ w, H.adjMatrix ℤ u w = H.adjMatrix ℤ v w := by
    simpa [hpu, hqv] using hpqRows
  obtain ⟨r, s, hrs, hrUV, hsVU, hrsRows⟩ :=
    sevenRegular_nearTwin_equal_commutingRows_propagate_private
      D hDreg huvCommon (H.adjMatrix ℤ) hcomm huvMatrixRows
  obtain ⟨r₀, s₀, hrSet, hsSet, _hr₀s₀, _⟩ :=
    sevenRegular_nearTwin_privateNeighbor_normalization D hDreg huvCommon
  have hry : r = y := by
    have hr' := hrUV
    have hy' := hyUV
    rw [hrSet] at hr' hy'
    exact (Finset.mem_singleton.mp hr').trans
      (Finset.mem_singleton.mp hy').symm
  have hsz : s = z := by
    have hs' := hsVU
    have hz' := hzVU
    rw [hsSet] at hs' hz'
    exact (Finset.mem_singleton.mp hs').trans
      (Finset.mem_singleton.mp hz').symm
  have hyzMatrixRows : ∀ w, H.adjMatrix ℤ y w = H.adjMatrix ℤ z w := by
    simpa [hry, hsz] using hrsRows
  have hyzRows : H.neighborFinset y = H.neighborFinset z := by
    apply Finset.ext
    intro w
    rw [H.mem_neighborFinset, H.mem_neighborFinset]
    have hrow := hyzMatrixRows w
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at hrow
    by_cases hyw : H.Adj y w <;> by_cases hzw : H.Adj z w <;>
      simp_all
  exact degreeTwo_no_three_distinct_equal_neighborFinsets
    H hHreg hxy hxz hyz hxyRows (hxyRows.trans hyzRows)

end

end Erdos85
