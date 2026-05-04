import Mathlib

/-
# De Moivre OQ-02 OQ-02: Product-to-Sum for Chebyshev Second Kind

## Open Question

Can the Chebyshev T product-to-sum formula
  2 T_m(cos θ) · T_n(cos θ) = T_{m+n}(cos θ) + T_{m-n}(cos θ)
be extended to Chebyshev polynomials of the second kind U_n?

## Answer: YES (cross-product formula)

We prove the mixed T·U product-to-sum identity for all integers m, n:

  2 · T_m(cos θ) · U_n(cos θ) = U_{m+n}(cos θ) + U_{n-m}(cos θ)

## Proof Strategy

Paired integer induction on m, carrying P(m) and P(m-1) simultaneously:
  P(m) := 2 · T R m · U R n = U R (m + n) + U R (n - m)

The key helper is 2·X·U_k = U_{k+1} + U_{k-1} (rearranged Chebyshev recurrence).
Each induction step uses this helper twice, via linear_combination.
-/

open Polynomial Polynomial.Chebyshev Real

namespace DeMoivreOQ02OQ02

section PolynomialIdentity

variable {R : Type*} [CommRing R] (n : ℤ)

/-- 2·X·U_k = U_{k+1} + U_{k-1}: rearrangement of the U recurrence -/
private lemma two_X_U (k : ℤ) :
    (2 : R[X]) * X * U R k = U R (k + 1) + U R (k - 1) := by
  have h := U_add_two (R := R) (k - 1)
  simp only [show k - 1 + 1 = k from by ring, show k - 1 + 2 = k + 1 from by ring] at h
  linear_combination -h

/-- P(m): the main product identity at index m -/
private def P (m : ℤ) : Prop :=
  (2 : R[X]) * T R m * U R n = U R (m + n) + U R (n - m)

/-- The paired conjunction used for induction -/
private def Q (m : ℤ) : Prop := P n m ∧ P n (m - 1)

private lemma Q_zero : Q n 0 := by
  constructor
  · -- P(0): 2 * 1 * U n = U n + U n = 2 * U n
    simp [P, T_zero]; ring
  · -- P(-1): 2 * T(-1) * U n = U(-1+n) + U(n+1)
    -- T(-1) = X (from T(-1+2) = 2X*T(0) - T(-1), so X = 2X - T(-1), T(-1) = X)
    simp only [P, show (0 : ℤ) - 1 = -1 from rfl, show (-1 : ℤ) + n = n - 1 from by ring,
               show n - (-1 : ℤ) = n + 1 from by ring]
    have hm1 : T R (-1 : ℤ) = X := by
      have h := T_add_two (R := R) (-1 : ℤ)
      simp only [show (-1 : ℤ) + 2 = 1 from rfl, show (-1 : ℤ) + 1 = 0 from rfl,
                 T_zero, T_one] at h
      linear_combination -h
    rw [hm1]
    exact two_X_U n

private lemma Q_succ (m : ℤ) (⟨hm, hm1⟩ : Q n m) : Q n (m + 1) := by
  refine ⟨?_, hm⟩
  -- P(m+1): T(m+1) appears, use T(m+1) via T(m) and T(m-1) via hT
  -- Actually: from Q(m), we have P(m) and P(m-1). Want P(m+1).
  -- From T(m+1) = 2X*T(m) - T(m-1): T_add_two at m-1:
  --   T(m+1) = 2X*T(m) - T(m-1)
  -- 2*T(m+1)*U n = 2*(2X*T(m) - T(m-1))*U n
  --   = 2X*(2*T(m)*U n) - (2*T(m-1)*U n)
  --   = 2X*(U(m+n) + U(n-m)) - (U(m-1+n) + U(n-m+1))   by hm, hm1
  --   = (U(m+n+1)+U(m+n-1)) + (U(n-m+1)+U(n-m-1)) - U(m-1+n) - U(n-m+1)  by two_X_U twice
  --   = U(m+1+n) + U(n-m-1)  ✓
  simp only [P, show (m + 1 : ℤ) + n = m + n + 1 from by ring,
             show n - (m + 1 : ℤ) = n - m - 1 from by ring]
  have hT := T_add_two (R := R) (m - 1)
  have hu1 := two_X_U (m + n)
  have hu2 := two_X_U (n - m)
  simp only [show m - 1 + 2 = m + 1 from by ring, show m - 1 + 1 = m from by ring] at hT
  simp only [show m + n + 1 = m + n + 1 from rfl, show m + n - 1 = m - 1 + n from by ring] at hu1
  simp only [show n - m + 1 = n - (m - 1) from by ring,
             show n - m - 1 = n - m - 1 from rfl] at hu2
  simp only [P] at hm hm1
  simp only [show (m - 1 : ℤ) + n = m - 1 + n from rfl, show n - (m - 1 : ℤ) = n - m + 1 from by ring] at hm1
  linear_combination 2 * U R n * hT + 2 * X * hm - hm1 - hu1 - hu2

private lemma Q_pred (m : ℤ) (⟨hm, hm1⟩ : Q n m) : Q n (m - 1) := by
  refine ⟨hm1, ?_⟩
  -- P(m-2): from P(m) and P(m-1), using T(m) = 2X*T(m-1) - T(m-2)
  --   T(m-2) = 2X*T(m-1) - T(m)
  --   2*T(m-2)*U n = 2*(2X*T(m-1) - T(m))*U n
  --     = 2X*(2*T(m-1)*U n) - (2*T(m)*U n)
  --     = 2X*(U(m-1+n) + U(n-m+1)) - (U(m+n) + U(n-m))  by hm1, hm
  --     = (U(m+n) + U(m-2+n)) + (U(n-m+2) + U(n-m)) - U(m+n) - U(n-m)  by two_X_U twice
  --     = U(m-2+n) + U(n-m+2) = U((m-1)-1+n) + U(n-((m-1)-1))  ✓
  simp only [P, show (m - 1 : ℤ) - 1 = m - 2 from by ring,
             show (m - 2 : ℤ) + n = m - 2 + n from rfl,
             show n - (m - 2 : ℤ) = n - m + 2 from by ring]
  have hT := T_add_two (R := R) (m - 2)
  have hu1 := two_X_U (m - 1 + n)
  have hu2 := two_X_U (n - m + 1)
  simp only [show m - 2 + 2 = m from by ring, show m - 2 + 1 = m - 1 from by ring] at hT
  simp only [show m - 1 + n + 1 = m + n from by ring,
             show m - 1 + n - 1 = m - 2 + n from by ring] at hu1
  simp only [show n - m + 1 + 1 = n - m + 2 from by ring,
             show n - m + 1 - 1 = n - m from by ring] at hu2
  simp only [P] at hm hm1
  simp only [show (m - 1 : ℤ) + n = m - 1 + n from rfl,
             show n - (m - 1 : ℤ) = n - m + 1 from by ring] at hm1
  linear_combination 2 * U R n * hT + 2 * X * hm1 - hm - hu1 - hu2

/-- **Main polynomial identity**: 2·T_m · U_n = U_{m+n} + U_{n-m} in R[X]

Proved by integer induction (paired), using only the Chebyshev polynomial recurrences. -/
theorem T_mul_U_product (m : ℤ) : (2 : R[X]) * T R m * U R n = U R (m + n) + U R (n - m) := by
  suffices h : Q n m from h.1
  induction m using Int.induction_on with
  | hz => exact Q_zero n
  | hp k ih => exact Q_succ n k ih
  | hn k ih =>
    -- ih : Q n (-↑k), goal : Q n (-↑k - 1) = Q n ((-↑k) - 1)
    exact Q_pred n (-(↑k : ℤ)) ih

end PolynomialIdentity

-- ============================================================
-- Real Evaluation Form
-- ============================================================

section RealEvaluation

/-- **Cross Product-to-Sum** (real form):
  2·T_m(cos θ)·U_n(cos θ) = U_{m+n}(cos θ) + U_{n-m}(cos θ)

Extends the T·T formula 2·T_m·T_n = T_{m+n} + T_{m-n} to the mixed T·U setting.
Proved algebraically from the polynomial identity — no sin θ = 0 case analysis needed. -/
theorem chebyshev_T_U_product_to_sum (m n : ℤ) (θ : ℝ) :
    2 * (T ℝ m).eval (Real.cos θ) * (U ℝ n).eval (Real.cos θ) =
    (U ℝ (m + n)).eval (Real.cos θ) + (U ℝ (n - m)).eval (Real.cos θ) := by
  have h := T_mul_U_product (R := ℝ) n m
  have key := congr_arg (Polynomial.eval (Real.cos θ)) h
  simp only [Polynomial.eval_mul, Polynomial.eval_add, map_ofNat] at key
  linarith

/-- Recurrence eval form: 2·cos θ·U_n(cos θ) = U_{n+1}(cos θ) + U_{n-1}(cos θ) -/
theorem chebyshev_cos_U (n : ℤ) (θ : ℝ) :
    2 * Real.cos θ * (U ℝ n).eval (Real.cos θ) =
    (U ℝ (n + 1)).eval (Real.cos θ) + (U ℝ (n - 1)).eval (Real.cos θ) := by
  have h := chebyshev_T_U_product_to_sum 1 n θ
  simp only [T_real_cos, Int.cast_one, one_mul] at h
  convert h using 2 <;> [ring; ring]

/-- Trig form: 2·cos θ·sin((n+1)θ) = sin((n+2)θ) + sin(nθ) -/
theorem two_cos_sin_spreading (n : ℤ) (θ : ℝ) :
    2 * Real.cos θ * Real.sin (((n : ℝ) + 1) * θ) =
    Real.sin (((n : ℝ) + 2) * θ) + Real.sin ((n : ℝ) * θ) := by
  have hcos := chebyshev_cos_U n θ
  rw [← U_real_cos θ n] at hcos
  rw [show (n : ℝ) + 1 = ((n : ℤ) : ℝ) + 1 from by norm_cast]
  have h1 := U_real_cos θ (n + 1)
  have h2 := U_real_cos θ (n - 1)
  have hn1 : (↑(n + 1 : ℤ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hn2 : (↑(n - 1 : ℤ) : ℝ) + 1 = (n : ℝ) := by push_cast; ring
  rw [hn1] at h1; rw [hn2] at h2
  nlinarith [hcos, h1, h2, Real.sin_sq_add_cos_sq θ,
             mul_comm ((U ℝ n).eval (Real.cos θ)) (Real.sin θ),
             mul_comm ((U ℝ (n + 1)).eval (Real.cos θ)) (Real.sin θ),
             mul_comm ((U ℝ (n - 1)).eval (Real.cos θ)) (Real.sin θ)]

end RealEvaluation

/-- **Summary**: cross product-to-sum formula and the recurrence corollary -/
theorem demoivre_oq02oq02_summary (m n : ℤ) (θ : ℝ) :
    (2 * (T ℝ m).eval (Real.cos θ) * (U ℝ n).eval (Real.cos θ) =
     (U ℝ (m + n)).eval (Real.cos θ) + (U ℝ (n - m)).eval (Real.cos θ)) ∧
    (2 * Real.cos θ * (U ℝ n).eval (Real.cos θ) =
     (U ℝ (n + 1)).eval (Real.cos θ) + (U ℝ (n - 1)).eval (Real.cos θ)) :=
  ⟨chebyshev_T_U_product_to_sum m n θ, chebyshev_cos_U n θ⟩

end DeMoivreOQ02OQ02
