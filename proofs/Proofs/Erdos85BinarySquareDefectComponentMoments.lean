import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85BinarySquareCenteredComponentLaplacian

/-!
# Exact moment ledgers for binary-square defect components

Each defect component of normalized size `m` is `(q-1)`-regular on `qm`
vertices.  This file records the resulting principal-removed first and second
adjacency moments.  These are the stable numerical inputs for the square-field
versus nonsquare-field orbit dichotomy.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Uniform graph-facing moment package for one defect component. -/
theorem binarySquare_regular_defectComponent_moment_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) :
    let H := (secondOrderDefectGraph G).induce c.supp
    (∀ x, H.degree x = q - 1) ∧
      Fintype.card c.supp = q * m ∧
      Matrix.trace (H.adjMatrix ℤ) = 0 ∧
      Matrix.trace (H.adjMatrix ℤ) - ((q - 1 : ℕ) : ℤ) =
        -((q - 1 : ℕ) : ℤ) ∧
      Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ) =
        ((q * m : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) ∧
      Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ) -
          ((q - 1 : ℕ) : ℤ) ^ 2 =
        ((q * m : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) -
          ((q - 1 : ℕ) : ℤ) ^ 2 := by
  let D := secondOrderDefectGraph G
  let H := D.induce c.supp
  have hHreg : ∀ x, H.degree x = q - 1 := by
    intro x
    exact binarySquare_regular_inducedDefectComponent_degree
      G hfree hq hreg hcard c x
  have hHcard : Fintype.card c.supp = q * m := by
    rw [Set.fintypeCard_eq_ncard, hc]
  have htrace : Matrix.trace (H.adjMatrix ℤ) = 0 :=
    FriendshipTheoremOQ01.adjMatrix_trace_zero H
  have htraceSq : Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ) =
      ((q * m : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) := by
    rw [FriendshipTheoremOQ01.trace_adjMatrix_sq H (q - 1) hHreg, hHcard]
  exact ⟨hHreg, hHcard, htrace, by rw [htrace]; ring,
    htraceSq, by rw [htraceSq]⟩

/-- At order 64 (`q=8`), every normalized-size-`m` defect component has
nonprincipal first moment `-7` and nonprincipal square moment `56m-49`. -/
theorem orderSixtyFour_regular_defectComponent_residual_moments
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = 8 * m) :
    let H := (secondOrderDefectGraph G).induce c.supp
    Matrix.trace (H.adjMatrix ℤ) - 7 = -7 ∧
      Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ) - 7 ^ 2 =
        56 * (m : ℤ) - 49 := by
  have hp := binarySquare_regular_defectComponent_moment_package
    G hfree (q := 8) (by norm_num) hreg (by norm_num) c hc
  dsimp only at hp ⊢
  refine ⟨?_, ?_⟩
  · simpa only [Nat.reduceSub, Nat.cast_ofNat] using hp.2.2.2.1
  calc
    Matrix.trace
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ) - 7 ^ 2 =
        (((8 * m : ℕ) : ℤ) * 7 - 7 ^ 2) := by
          simpa using hp.2.2.2.2.2
    _ = 56 * (m : ℤ) - 49 := by push_cast; ring

end

end Erdos85
