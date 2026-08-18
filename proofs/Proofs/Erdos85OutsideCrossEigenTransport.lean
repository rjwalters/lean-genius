import Proofs.Erdos85OutsideCrossSquareTransport

/-!
# Spectral transport across the inside--outside incidence block

On the centered internal subspace the all-ones term in `A B + B C = J`
vanishes.  Consequently `Bᵀ` transports an internal eigenvector of `Aᵀ` to
an exterior eigenvector of `Cᵀ`, negating its eigenvalue.  This is the exact
linear-algebra interface needed by both the signed joint-eigenline and the
eigenline-free size-two branches.
-/

namespace Erdos85

noncomputable section

/-- Centered eigenvectors cross the rectangular block with their eigenvalue
negated.  Nonzeroness of the transported vector is deliberately separate: it
is the only additional condition needed to obtain a genuine exterior
eigenline. -/
theorem rectangular_cross_centered_eigenvector_transport
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (J : Matrix H O K) (v : H → K) (lambda : K)
    (hcross : A * B + B * C = J)
    (hAv : A.transpose.mulVec v = lambda • v)
    (hcenter : J.transpose.mulVec v = 0) :
    C.transpose.mulVec (B.transpose.mulVec v) =
      (-lambda) • B.transpose.mulVec v := by
  have ht := congrArg Matrix.transpose hcross
  have hCB : C.transpose * B.transpose =
      J.transpose - B.transpose * A.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul] at ht
    exact eq_sub_of_add_eq' ht
  calc
    C.transpose.mulVec (B.transpose.mulVec v) =
        (C.transpose * B.transpose).mulVec v := by
      rw [Matrix.mulVec_mulVec]
    _ = (J.transpose - B.transpose * A.transpose).mulVec v := by rw [hCB]
    _ = J.transpose.mulVec v -
        (B.transpose * A.transpose).mulVec v := by
      rw [Matrix.sub_mulVec]
    _ = 0 - B.transpose.mulVec (A.transpose.mulVec v) := by
      rw [hcenter, Matrix.mulVec_mulVec]
    _ = 0 - B.transpose.mulVec (lambda • v) := by rw [hAv]
    _ = 0 - lambda • B.transpose.mulVec v := by
      rw [Matrix.mulVec_smul]
    _ = (-lambda) • B.transpose.mulVec v := by module

/-- If the transported vector is nonzero, the preceding identity is a
literal exterior eigenpair. -/
theorem rectangular_cross_centered_eigenpair_transport
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (J : Matrix H O K) (v : H → K) (lambda : K)
    (hcross : A * B + B * C = J)
    (hAv : A.transpose.mulVec v = lambda • v)
    (hcenter : J.transpose.mulVec v = 0)
    (hnonzero : B.transpose.mulVec v ≠ 0) :
    B.transpose.mulVec v ≠ 0 ∧
      C.transpose.mulVec (B.transpose.mulVec v) =
        (-lambda) • B.transpose.mulVec v :=
  ⟨hnonzero, rectangular_cross_centered_eigenvector_transport
    A B C J v lambda hcross hAv hcenter⟩

/-- The only way incidence transport can vanish is through the negative
degree eigenspace of the residual Gram graph.  In the order-64 application
`r = 6` and `R` is the six-regular exterior-pair graph. -/
theorem rectangular_incidence_kernel_forces_negative_gram_residual
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (B : Matrix H O K) (E : Matrix O H K) (R : Matrix H H K)
    (r : K) (v : H → K)
    (hgram : B * E = r • (1 : Matrix H H K) + R)
    (hker : E.mulVec v = 0) :
    R.mulVec v = (-r) • v := by
  have hzero : (B * E).mulVec v = 0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  rw [hgram, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hzero
  have hneg := eq_neg_of_add_eq_zero_right hzero
  simpa using hneg

/-- Complete centered-mode dichotomy.  A mode either crosses to a genuine
exterior eigenpair, or its incidence image vanishes and the Gram residual
acts on it by the negative row degree. -/
theorem rectangular_cross_centered_eigenpair_or_negative_gram_residual
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (J : Matrix H O K) (R : Matrix H H K)
    (r lambda : K) (v : H → K)
    (hcross : A * B + B * C = J)
    (hAv : A.transpose.mulVec v = lambda • v)
    (hcenter : J.transpose.mulVec v = 0)
    (hgram : B * B.transpose = r • (1 : Matrix H H K) + R) :
    (B.transpose.mulVec v ≠ 0 ∧
      C.transpose.mulVec (B.transpose.mulVec v) =
        (-lambda) • B.transpose.mulVec v) ∨
      R.mulVec v = (-r) • v := by
  by_cases hker : B.transpose.mulVec v = 0
  · right
    exact rectangular_incidence_kernel_forces_negative_gram_residual
      B B.transpose R r v hgram hker
  · left
    exact rectangular_cross_centered_eigenpair_transport
      A B C J v lambda hcross hAv hcenter hker

/-- Graph-facing centered spectral transport for the actual order-64
`16+48` cut. -/
theorem orderSixtyFour_seven_components_outside_centered_eigenvector_transport
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
      let q : Set (Fin 64) := {x | ¬p x}
      let H := (G.induce c.supp).adjMatrix ℂ
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
      ∀ (v : c.supp → ℂ) (lambda : ℂ),
        H.mulVec v = lambda • v →
        J.transpose.mulVec v = 0 →
        C.mulVec (B.transpose.mulVec v) =
          (-lambda) • B.transpose.mulVec v := by
  classical
  obtain ⟨c, hc, _label, _hqcard, _htwo, _hinj, _himage,
      _hRreg, _hRedges, _hCreg, _hC4, hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  refine ⟨c, hc, ?_⟩
  dsimp only
  intro vec lambda hHv hcenter
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let q : Set (Fin 64) := {x | ¬p x}
  let Hg := G.induce c.supp
  let Cg := G.induce q
  let H := Hg.adjMatrix ℂ
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := Cg.adjMatrix ℂ
  let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
  have htransport := rectangular_cross_centered_eigenvector_transport
    H B C J vec lambda hcross (by
      rw [Hg.isSymm_adjMatrix.eq]
      exact hHv) hcenter
  rw [Cg.isSymm_adjMatrix.eq] at htransport
  exact htransport

end


end Erdos85

#print axioms Erdos85.rectangular_cross_centered_eigenvector_transport
#print axioms Erdos85.rectangular_cross_centered_eigenpair_transport
#print axioms Erdos85.rectangular_incidence_kernel_forces_negative_gram_residual
#print axioms Erdos85.rectangular_cross_centered_eigenpair_or_negative_gram_residual
#print axioms Erdos85.orderSixtyFour_seven_components_outside_centered_eigenvector_transport
