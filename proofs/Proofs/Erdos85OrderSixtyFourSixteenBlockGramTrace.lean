import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles
import Proofs.Erdos85OrderSixtyFourDefectSecondMoment
import Proofs.Erdos85ComponentLocalObstruction

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

/-- The constant vector is the principal exterior-Gram eigenvector, with
eigenvalue `12`.  Combined with total trace `96`, this leaves Gram trace
`84` on the fifteen-dimensional mean-zero sector. -/
theorem orderSixtyFour_sixteenBlock_exteriorGram_mulVec_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16)
    (htwo : ∀ x : c.supp, (G.induce c.supp).degree x = 2) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    (B * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (12 : ℂ) • (fun _ ↦ 1) := by
  classical
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let A := (G.induce c.supp).adjMatrix ℂ
  let Dg := secondOrderDefectGraph G
  let D := (Dg.induce c.supp).adjMatrix ℂ
  let u : c.supp → ℂ := fun _ ↦ 1
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
  have hDreg : ∀ x : Fin 64, Dg.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hDlocal : ∀ x : c.supp, (Dg.induce c.supp).degree x = 7 := by
    intro x
    rw [degree_induce_connectedComponent_supp Dg c x]
    exact hDreg x
  have hAu : A.mulVec u = (2 : ℂ) • u := by
    funext x
    calc
      (A.mulVec u) x = ((G.induce c.supp).degree x : ℂ) := by
        simpa [A, u] using
          (SimpleGraph.adjMatrix_mulVec_const_apply
            (G := G.induce c.supp) (α := ℂ) (a := 1) (v := x))
      _ = 2 := by rw [htwo x]; norm_num
      _ = ((2 : ℂ) • u) x := by simp [u]
  have hDu : D.mulVec u = (7 : ℂ) • u := by
    funext x
    calc
      (D.mulVec u) x = ((Dg.induce c.supp).degree x : ℂ) := by
        simpa [D, u] using
          (SimpleGraph.adjMatrix_mulVec_const_apply
            (G := Dg.induce c.supp) (α := ℂ) (a := 1) (v := x))
      _ = 7 := by rw [hDlocal x]; norm_num
      _ = ((7 : ℂ) • u) x := by simp [u]
  have hJu :
      ((FriendshipTheoremOQ01.onesMatrix c.supp).map
        (Int.castRingHom ℂ)).mulVec u = (16 : ℂ) • u := by
    funext x
    simp [Matrix.mulVec, dotProduct, FriendshipTheoremOQ01.onesMatrix,
      u, hcard]
  have hA2u : A.mulVec (A.mulVec u) = (4 : ℂ) • u := by
    rw [hAu, Matrix.mulVec_smul, hAu]
    norm_num [smul_smul]
  have hmul := congrArg (fun M ↦ M.mulVec u) hid
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hA2u, hDu, hJu] at hmul
  change (B * Matrix.conjTranspose B).mulVec u = (12 : ℂ) • u
  rw [← Matrix.mulVec_mulVec]
  funext x
  have hx := congrFun hmul x
  simp [u] at hx ⊢
  linear_combination hx

end

end Erdos85
