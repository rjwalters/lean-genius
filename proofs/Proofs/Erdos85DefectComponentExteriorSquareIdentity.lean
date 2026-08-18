import Proofs.Erdos85OrderSixtyFourComponentGramIdentity

/-!
# Exact exterior square identity at a defect-component cut

Restricting `A² = (q-1)I + J - D` to the exterior side of a defect component
splits the two-step paths into an exterior square and the Gram matrix of paths
through the component.  Removing the diagonal value two from that Gram matrix
isolates the row/column relation of a normalized size-two grid.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exterior diagonal block of the square identity, q-generically. -/
theorem binarySquare_regular_defectComponent_exterior_sq_add_internalGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : V → Prop := fun x => x ∉ c.supp
    let C := (G.adjMatrix ℤ).toBlock p p
    let Q := (G.adjMatrix ℤ).toBlock p (fun x => ¬p x) *
      (G.adjMatrix ℤ).toBlock (fun x => ¬p x) p
    let DO := ((secondOrderDefectGraph G).adjMatrix ℤ).toBlock p p
    C * C + Q =
      ((q : ℤ) - 1) • (1 : Matrix {x // p x} {x // p x} ℤ) +
        FriendshipTheoremOQ01.onesMatrix {x // p x} - DO := by
  classical
  let p : V → Prop := fun x => x ∉ c.supp
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hblock := toBlock_sq_add_cross_eq_of_sq_eq
    (G.adjMatrix ℤ) ((secondOrderDefectGraph G).adjMatrix ℤ)
    (FriendshipTheoremOQ01.onesMatrix V) ((q : ℤ) - 1) hsq p
  have hJ : (FriendshipTheoremOQ01.onesMatrix V).toBlock p p =
      FriendshipTheoremOQ01.onesMatrix {x // p x} := by
    ext i j
    simp [Matrix.toBlock_apply, FriendshipTheoremOQ01.onesMatrix]
  simpa only [hJ] using hblock

/-- Subtracting the two diagonal incidences through the component exposes the
off-diagonal shared-coordinate matrix `Rowcol = Q - 2I`:

`C² = (q-3)I + J - D_out - Rowcol`.

For a size-two signed grid, C4-freeness makes `Rowcol` the 0/1 relation "same
row or same column", so the other off-diagonal 1-entries of `C²` are exactly
the cross-cell agreements. -/
theorem binarySquare_regular_defectComponent_exterior_sq_eq_sub_rowcol
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : V → Prop := fun x => x ∉ c.supp
    let C := (G.adjMatrix ℤ).toBlock p p
    let Q := (G.adjMatrix ℤ).toBlock p (fun x => ¬p x) *
      (G.adjMatrix ℤ).toBlock (fun x => ¬p x) p
    let DO := ((secondOrderDefectGraph G).adjMatrix ℤ).toBlock p p
    let Rowcol := Q - (2 : ℤ) • (1 : Matrix {x // p x} {x // p x} ℤ)
    C * C =
      ((q : ℤ) - 3) • (1 : Matrix {x // p x} {x // p x} ℤ) +
        FriendshipTheoremOQ01.onesMatrix {x // p x} - DO - Rowcol := by
  classical
  dsimp only
  have h := binarySquare_regular_defectComponent_exterior_sq_add_internalGram
    G hfree hreg c
  dsimp only at h
  calc
    _ = (((q : ℤ) - 1) •
          (1 : Matrix {x // x ∉ c.supp} {x // x ∉ c.supp} ℤ) +
        FriendshipTheoremOQ01.onesMatrix {x // x ∉ c.supp} -
          ((secondOrderDefectGraph G).adjMatrix ℤ).toBlock
            (fun x => x ∉ c.supp) (fun x => x ∉ c.supp)) -
        ((G.adjMatrix ℤ).toBlock (fun x => x ∉ c.supp)
            (fun x => ¬x ∉ c.supp) *
          (G.adjMatrix ℤ).toBlock (fun x => ¬x ∉ c.supp)
            (fun x => x ∉ c.supp)) := eq_sub_of_add_eq h
    _ = _ := by module

end

end Erdos85

#print axioms
  Erdos85.binarySquare_regular_defectComponent_exterior_sq_add_internalGram
#print axioms
  Erdos85.binarySquare_regular_defectComponent_exterior_sq_eq_sub_rowcol
