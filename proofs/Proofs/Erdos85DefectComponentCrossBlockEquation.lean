import Proofs.Erdos85ExcessDefectRegular

/-! # The exact adjacency equation across a defect-component cut

For a regular C4-free graph, distinct second-order defect components have
exactly one common ambient neighbor.  In block-matrix form, cutting at any
one defect component gives the exact equation `H B + B C = J`.  This is the
exterior coupling that is absent from purely local defect/owner calibrations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Defect-cut cross-block equation.**  If `H` and `C` are the ambient
adjacency blocks inside and outside a second-order defect component and `B`
is the cross-incidence block, then every cross pair has exactly one common
neighbor, equivalently `H B + B C` is the all-ones matrix. -/
theorem binarySquare_regular_defectComponent_crossBlock_eq_ones
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    H * B + B * C = fun _ _ ↦ (1 : ℤ) := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hblock := congrArg
    (fun X ↦ X.toBlock p (fun x ↦ ¬p x)) hsq
  rw [Matrix.toBlock_mul_eq_add p p (fun x ↦ ¬p x)] at hblock
  have hA11 : (G.adjMatrix ℤ).toBlock p p = H := by
    ext i j
    simp [H, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hA12 : (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x) = B := rfl
  have hA22 : (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x)
      (fun x ↦ ¬p x) = C := rfl
  have hright : (((q : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ).toBlock
          p (fun x ↦ ¬p x) = fun _ _ ↦ (1 : ℤ) := by
    ext i j
    have hij : i.1 ≠ j.1 := fun h ↦ j.2 (h ▸ i.2)
    have hD : ¬D.Adj i.1 j.1 := by
      intro hadj
      exact j.2 ((c.mem_supp_congr_adj hadj).mp i.2)
    change (((q : ℤ) - 1) * (if i.1 = j.1 then 1 else 0) + 1 -
      (if D.Adj i.1 j.1 then 1 else 0)) = 1
    simp [hij, hD]
  rw [hA11, hA12, hA22, hright] at hblock
  exact hblock

end

#print axioms Erdos85.binarySquare_regular_defectComponent_crossBlock_eq_ones

end Erdos85
