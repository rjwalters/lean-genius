import Proofs.Erdos85OrderFortyNineIntegralResidual

/-! # High-sector divisibility of the order-49 adjacency determinant -/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- With exactly three degree-eight vertices, the two high-row differences
contribute two copies of `X² - 7` to the integral characteristic polynomial.
Consequently the adjacency determinant is divisible by `7²`. -/
theorem orderFortyNine_fortyNine_dvd_det_adjMatrix_of_three_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7)
    (hhigh : (squareOrderHighVertices G 7).card = 3) :
    49 ∣ (G.adjMatrix ℤ).det := by
  obtain ⟨R, _hRmonic, hfactor, _hdegree, _hnext, _hc2, _hc4⟩ :=
    exists_monic_integral_orderFortyNineSeven_residualCharpoly
      G hfree hmin hcover hcard ha
  rw [hhigh] at hfactor
  have hcoeff := congrArg (fun p : ℤ[X] => p.coeff 0) hfactor
  simp only [coeff_zero_eq_eval_zero] at hcoeff
  norm_num at hcoeff
  rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero] at hcoeff
  have hdet := Matrix.det_eq_sign_charpoly_coeff (G.adjMatrix ℤ)
  rw [hcard] at hdet
  norm_num at hdet
  refine ⟨-R.coeff 0, ?_⟩
  omega

/-- Arithmetic consumer for a defect-side determinant formula of the shape
`det(A²) = 49 T`: the high-sector divisibility upgrades `T` from a square
to forty-nine times a square. -/
theorem eq_fortyNine_mul_sq_of_fortyNine_mul_eq_sq
    (z T : ℤ) (hz : 49 ∣ z) (hdet : 49 * T = z * z) :
    ∃ q : ℤ, T = 49 * (q * q) := by
  rcases hz with ⟨q, rfl⟩
  refine ⟨q, ?_⟩
  nlinarith

end

end Erdos85
