import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles
import Proofs.Erdos85OrderSixtyFourDefectSecondMoment

/-! # Exterior Gram mass on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The exterior incidence Gram matrix on the distinguished H16 block has
total trace `96`: sixteen vertices, each with six ambient neighbors outside
the internal two-factor. -/
theorem orderSixtyFour_seven_defect_components_sixteenBlock_exteriorGram_trace
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
      Matrix.trace (B * Matrix.conjTranspose B) = 96 := by
  classical
  obtain ⟨c, hc16, htwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let A := (G.induce c.supp).adjMatrix ℂ
  let D := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
  have hid :=
    orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
      G hfree hmin hcover c
  change A * A + B * Matrix.conjTranspose B =
      (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
        (FriendshipTheoremOQ01.onesMatrix c.supp).map
          (Int.castRingHom ℂ) - D at hid
  have hcard : Fintype.card c.supp = 16 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = 16 := hc16
  have hAtrace : Matrix.trace (A * A) = 32 := by
    dsimp [A]
    rw [trace_adjMatrix_sq_complex_eq_sum_degrees]
    simp [htwo, hcard]
    norm_num
  have hDtrace : Matrix.trace D = 0 := by
    simp [D, Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply]
  have hItrace : Matrix.trace (1 : Matrix c.supp c.supp ℂ) = 16 := by
    simp [Matrix.trace_one, hcard]
  have hJtrace : Matrix.trace
      ((FriendshipTheoremOQ01.onesMatrix c.supp).map
        (Int.castRingHom ℂ)) = 16 := by
    simp [Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix,
      hcard]
  have htrace := congrArg Matrix.trace hid
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, hAtrace, hDtrace, hItrace, hJtrace] at htrace
  change Matrix.trace (B * Matrix.conjTranspose B) = 96
  norm_num at htrace ⊢
  linear_combination htrace

end

end Erdos85
