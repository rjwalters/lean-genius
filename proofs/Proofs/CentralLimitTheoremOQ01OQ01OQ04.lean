/-
Multivariate Operator-Stable Distributions (CLT-OQ-01-OQ-01-OQ-04)

Extends the Gnedenko-Kolmogorov domain of attraction theory to ℝ^d.
In the multivariate setting, scalar normalizations n^{1/α} are replaced
by matrix normalizations A_n = n^{-E}, where E is the "exponent matrix."

Key results:
1. PROVED: Quadratic form scales as quadForm(ξ/√n) = (1/n)·quadForm(ξ)
2. PROVED: Gaussian N(0,Sg) is operator-stable with exponent E = (1/2)·I
3. PROVED: Scalar specialization — 1D α-stable embeds into ℝ^1 case
4. PROVED: Structural properties (linear images, normalization at 0)
5. AXIOM: Eigenvalue bound — all eigenvalues of E have real part ≥ 1/2
6. AXIOM: Meerschaert-Scheffler domain of attraction (biconditional)

The eigenvalue bound (axiom) is the multivariate analog of α ≤ 2:
for scalar E = c·I, the condition Re(λ(E)) = c ≥ 1/2 means α = 1/c ≤ 2.

References:
- Meerschaert & Scheffler, "Limit Distributions for Sums of Independent
  Random Vectors" (2001, Wiley-Interscience)
- Jurek & Mason, "Operator-Limit Distributions in Probability Theory" (1993)
- Hudson & Mason, "Operator-stable distributions" (1982), TAMS
-/

import Mathlib
import Proofs.CentralLimitTheoremOQ01OQ01

namespace OperatorStable

open DomainOfAttraction Real Complex Finset
open scoped Matrix

set_option maxHeartbeats 800000

noncomputable section

-- ============================================================
-- PART I: Multivariate Setup and Definitions
-- ============================================================

/-- Quadratic form ξᵀSgξ for a d×d matrix Sg and vector ξ : Fin d → ℝ.
    Appears in the Gaussian characteristic function exp(-ξᵀSgξ/2). -/
def quadForm (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, Sg i j * ξ i * ξ j

/-- Euclidean inner product on Fin d → ℝ: ⟨x, y⟩ = ∑ᵢ xᵢ yᵢ. -/
def vecInner (d : ℕ) (x y : Fin d → ℝ) : ℝ := ∑ i : Fin d, x i * y i

/-- The Gaussian characteristic function φ_Sg(ξ) = exp(-ξᵀSgξ/2).
    For symmetric positive definite Sg, this is the characteristic function
    of the d-dimensional Gaussian N(0, Sg). -/
def gaussCharFun (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : ℂ :=
  exp (-(quadForm d Sg ξ / 2 : ℝ) : ℂ)

/-- A multivariate characteristic function φ : (Fin d → ℝ) → ℂ is operator-stable
    if there exist invertible matrix normalizations {A_n} and drift vectors {b_n} such that
    for all n ≥ 1 and ξ: φ(Aₙᵀ ξ)^n = φ(ξ) · exp(i⟨b_n, ξ⟩). -/
def IsOperatorStable (d : ℕ) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, n ≠ 0 → ∀ ξ : Fin d → ℝ,
    (φ (fun i => ∑ j, A n i j * ξ j)) ^ n =
    φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))

/-- Scalar-normalized operator-stability: normalizations A_n = n^{-c}·I.
    Corresponds to the univariate α-stable case with α = 1/c. -/
def HasScalarExponent (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ) : Prop :=
  ∃ (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, n ≠ 0 → ∀ ξ : Fin d → ℝ,
    (φ (fun i => ξ i * (n : ℝ) ^ (-c))) ^ n =
    φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))

/-- A multivariate characteristic function in the operator domain of attraction
    of an operator-stable law: the normalized n-fold convolution converges. -/
def InOperatorDomainOfAttraction (d : ℕ)
    (φ ψ : (Fin d → ℝ) → ℂ) : Prop :=
  IsOperatorStable d ψ ∧
  ∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  Filter.Tendsto
    (fun n => fun ξ => (φ (fun i => ∑ j, A n i j * ξ j)) ^ n *
                       exp (I * (vecInner d (b n) ξ : ℝ)))
    Filter.atTop (nhds ψ)

-- ============================================================
-- PART II: Quadratic Form Lemmas
-- ============================================================

/-- Quadratic form scales quadratically: quadForm(c·ξ) = c² · quadForm(ξ). -/
theorem quadForm_scale (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (ξ : Fin d → ℝ) :
    quadForm d Sg (fun i => c * ξ i) = c ^ 2 * quadForm d Sg ξ := by
  simp only [quadForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Scaling ξ by n^{-1/2} scales the quadratic form by 1/n:
    quadForm(ξ/√n, ξ/√n) = (1/n) · quadForm(ξ, ξ). -/
theorem quadForm_scale_inv_sqrt (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin d → ℝ) (n : ℕ) (hn : 0 < n) :
    quadForm d Sg (fun i => ξ i / Real.sqrt n) = (1 / n : ℝ) * quadForm d Sg ξ := by
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hself : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnn
  simp only [quadForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, div_mul_div_comm, hself]
  ring

/-- Gaussian characteristic function equals 1 at ξ = 0. -/
theorem gaussCharFun_zero (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    gaussCharFun d Sg (fun _ => 0) = 1 := by
  simp [gaussCharFun, quadForm]

/-- Gaussian characteristic function norm ≤ 1 when Sg is positive semidefinite.

    The Gaussian characteristic function is `φ_Σ(ξ) = exp(-Q(ξ)/2)` where
    `Q(ξ) = ξᵀSgξ`. PosSemidef ensures `Q(ξ) ≥ 0`, so the real exponent
    `-Q(ξ)/2 ≤ 0`, hence the complex norm is `Real.exp (-Q/2) ≤ 1`.

    Discharged at Mathlib v4.26.0 (S6 ACT, PR following S5 STATE-SYNC #19383)
    via `Matrix.PosSemidef.dotProduct_mulVec_nonneg` + `Complex.norm_exp_ofReal`
    + `Real.exp_le_one_iff`; quadForm bridge via index reordering (`ring`). -/
theorem gaussCharFun_norm_le_one (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg) (ξ : Fin d → ℝ) :
    ‖gaussCharFun d Sg ξ‖ ≤ 1 := by
  -- Step 1: quadForm d Sg ξ ≥ 0 (Sg is PSD; ξ is real so star ξ = ξ).
  have hQ : 0 ≤ quadForm d Sg ξ := by
    have h := hSg.dotProduct_mulVec_nonneg ξ
    -- h : 0 ≤ star ξ ⬝ᵥ Sg *ᵥ ξ
    have hstar : (star ξ : Fin d → ℝ) = ξ := by funext i; exact star_trivial _
    rw [hstar] at h
    -- h : 0 ≤ ξ ⬝ᵥ Sg *ᵥ ξ
    have heq : ξ ⬝ᵥ Sg *ᵥ ξ = quadForm d Sg ξ := by
      simp only [dotProduct, Matrix.mulVec, quadForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith [heq ▸ h]
  -- Step 2: ‖Complex.exp (-↑(q/2))‖ = Real.exp (-(q/2)) ≤ 1 since q ≥ 0.
  -- (Elaborator pushes negation outside the coercion: `(-(q/2 : ℝ) : ℂ) = -↑(q/2)`.)
  unfold gaussCharFun
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_one_iff.mpr (by linarith)

-- ============================================================
-- PART III: Gaussian Operator-Stability (Proved)
-- ============================================================

/-- Key algebraic identity: for any x : ℝ and n ≠ 0,
    (exp(-x/n))^n = exp(-x) in ℂ.
    This is the core computation behind Gaussian scaling. -/
theorem exp_neg_div_pow (x : ℝ) (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (Complex.exp (-(↑(x / n) : ℂ))) ^ n = Complex.exp (-(↑x : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  congr 1
  push_cast
  field_simp

/-- **Main Theorem**: The d-dimensional Gaussian with covariance Sg is operator-stable
    with scalar normalization n^{-1/2}·I (zero drift).

    Scaling ξ by 1/√n and raising the characteristic function to the n-th power
    recovers the original Gaussian. This reflects the CLT self-similarity:
    if X₁, ..., Xₙ ~ N(0, Sg) i.i.d., then (X₁ + ... + Xₙ)/√n ~ N(0, Sg). -/
theorem gaussian_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin d → ℝ) (n : ℕ) (hn : n ≠ 0) :
    (gaussCharFun d Sg (fun i => ξ i / Real.sqrt n)) ^ n = gaussCharFun d Sg ξ := by
  simp only [gaussCharFun]
  have hn' := Nat.pos_of_ne_zero hn
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [quadForm_scale_inv_sqrt d Sg ξ n hn']
  -- Goal: (exp(-(((1/n)·q)/2)))^n = exp(-(q/2))
  -- Rewrite (1/n)·q/2 = (q/2)/n, then use exp_neg_div_pow
  rw [show (1 / (n : ℝ)) * quadForm d Sg ξ / 2 = quadForm d Sg ξ / 2 / n by ring]
  exact exp_neg_div_pow (quadForm d Sg ξ / 2) n hnn

/-- The Gaussian is operator-stable with scalar exponent c = 1/2 and zero drift.

    Discharges the v4.26.0 axiomatized version by combining the proven
    `gaussian_operator_stable` (operator-stability statement in `/√n` form) with
    the rpow→sqrt bridge `Real.rpow_neg + Real.sqrt_eq_rpow` and the
    `vecInner d 0 ξ = 0` simp lemma. Witness drift `b n = 0` per the axiom's
    original "zero drift" specification. -/
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Witness b n = 0 (zero drift).
  refine ⟨fun _ => 0, fun n hn ξ => ?_⟩
  -- Simplify RHS: vecInner d 0 ξ = 0, then exp(I*0) = 1.
  have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by
    simp [vecInner]
  rw [h_inner]
  -- Goal: (...)^n = gaussCharFun d Sg ξ * Complex.exp (I * ((0 : ℝ) : ℂ))
  rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]
  -- Bridge n^(-(1/2)) = 1/√n via Real.rpow_neg + Real.sqrt_eq_rpow.
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_arg : (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ)))
             = (fun i => ξ i / Real.sqrt n) := by
    funext i
    rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  rw [h_arg]
  exact gaussian_operator_stable d Sg ξ n hn

/-- The Gaussian is operator-stable (general form with matrix witness).

    Discharges the v4.26.0 axiomatized version (S11 ACT, 2026-06-01) by
    composing `gaussian_has_scalar_exponent` with the matrix-witness shape:
    pick `A_n = n^{-1/2}·I` (diagonal scalar matrix), then
    `∑ j, A_n i j * ξ j = n^{-1/2} * ξ i = ξ i * n^{-1/2}` collapses via
    `Matrix.smul_apply` + `Matrix.one_apply` + `Finset.sum_ite_eq`, reducing
    the goal to the scalar-exponent form discharged by
    `gaussian_has_scalar_exponent`. Drift witness `b n` reuses the one
    obtained from `gaussian_has_scalar_exponent` (zero drift). -/
theorem gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Sg) := by
  obtain ⟨b, hb⟩ := gaussian_has_scalar_exponent d Sg
  refine ⟨fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
          b, ?_⟩
  intro n hn ξ
  -- The diagonal scalar matrix collapses the sum:
  -- ∑ j, ((n^{-1/2}) • 1) i j * ξ j = ξ i * n^{-1/2}.
  have h_arg :
      (fun i => ∑ j, ((n : ℝ) ^ (-(1 / 2 : ℝ)) •
        (1 : Matrix (Fin d) (Fin d) ℝ)) i j * ξ j)
        = (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    funext i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
               mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
               Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [h_arg]
  exact hb n hn ξ

-- ============================================================
-- PART IV: Scalar Specialization and 1D Connection
-- ============================================================

/-- Embedding of a 1D characteristic function into the ℝ^1 framework. -/
def univariateEmbed (φ : ℝ → ℂ) : (Fin 1 → ℝ) → ℂ := fun ξ => φ (ξ 0)

/-- If a 1D char function satisfies scalar stability, the embedding is
    scalar-operator-stable in ℝ^1. -/
theorem univariate_embed_stable (φ : ℝ → ℂ) (c : ℝ)
    (hstable : ∀ n : ℕ, n ≠ 0 → ∀ t : ℝ,
      (φ (t * (n : ℝ) ^ (-c))) ^ n = φ t) :
    HasScalarExponent 1 (univariateEmbed φ) c := by
  refine ⟨fun _ _ => 0, fun n hn ξ => ?_⟩
  simp only [univariateEmbed, vecInner, zero_mul,
             Finset.sum_const_zero, ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  exact hstable n hn (ξ 0)

/-- The 1D α-stable law stableCharFun α embeds as operator-stable in ℝ^1. -/
theorem alpha_stable_is_operator_stable (α : ℝ) (hα : 0 < α) :
    HasScalarExponent 1 (univariateEmbed (stableCharFun α)) (1 / α) := by
  apply univariate_embed_stable
  intro n hn t
  simp only [stableCharFun]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnn' : (n : ℝ) ≠ 0 := hnn.ne'
  rw [Real.rpow_neg hnn.le]
  -- Goal: ↑n * (-|t * (↑n)^(-(1/α))|^α) = -|t|^α
  -- Since (↑n)^(-(1/α)) = 1/(↑n)^(1/α), we have |t * n^(-1/α)|^α = |t|^α/n
  -- and then n * (-|t|^α/n) = -|t|^α
  rw [show t * ((n : ℝ) ^ (1 / α))⁻¹ = t / (n : ℝ) ^ (1 / α) from div_eq_mul_inv t _]
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hnn.le _),
      Real.div_rpow (abs_nonneg t) (Real.rpow_nonneg hnn.le _),
      ← Real.rpow_mul hnn.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnn'
  push_cast
  field_simp

/-- The 1D α-stable law embeds into ℝ^1 as `IsOperatorStable` (matrix-witness form).

    Composes `alpha_stable_is_operator_stable` (scalar-exponent c = 1/α form)
    with the diagonal matrix witness `A_n = n^{-1/α} • (1 : Matrix (Fin 1) (Fin 1) ℝ)`,
    parallel to `gaussian_is_operator_stable` (the α = 2 / scalar-Gaussian case).
    The sum collapses via `Matrix.smul_apply` + `Matrix.one_apply` + `Finset.sum_ite_eq`. -/
theorem alpha_stable_is_operator_stable_matrix (α : ℝ) (hα : 0 < α) :
    IsOperatorStable 1 (univariateEmbed (stableCharFun α)) := by
  obtain ⟨b, hb⟩ := alpha_stable_is_operator_stable α hα
  refine ⟨fun n => (n : ℝ) ^ (-(1 / α)) • (1 : Matrix (Fin 1) (Fin 1) ℝ), b, ?_⟩
  intro n hn ξ
  have h_arg :
      (fun i => ∑ j, ((n : ℝ) ^ (-(1 / α)) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) i j * ξ j)
        = (fun i => ξ i * (n : ℝ) ^ (-(1 / α))) := by
    funext i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
               mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
               Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [h_arg]
  exact hb n hn ξ

-- ============================================================
-- PART V: Structural Properties
-- ============================================================

/-- Operator-stable laws are closed under **invertible** linear images.
    If φ is operator-stable, then ξ ↦ φ(Bξ) is operator-stable for any
    invertible matrix B.

    Reference: Meerschaert & Scheffler (2001), Theorem 7.2.1 (closure under
    linear images). The new normalizations are the conjugates
    `A'ₙ = B⁻¹ Aₙ B` and the drift is transported by the transpose,
    `b'ₙ = Bᵀ bₙ`. The computation: `ψ(A'ₙ ξ) = φ(B A'ₙ ξ) = φ(Aₙ (Bξ))`
    because `B A'ₙ = B (B⁻¹ Aₙ B) = Aₙ B`, so raising to the n-th power and
    using operator-stability of φ at the point `Bξ` yields
    `φ(Bξ)·exp(i⟨bₙ, Bξ⟩) = ψ(ξ)·exp(i⟨Bᵀbₙ, ξ⟩)`.

    **S17 ACT discharge note (2026-06-12):** the former `axiom` quantified over
    *all* B, including singular ones. For singular B the image distribution can
    collapse onto a lower-dimensional subspace, where the conjugation witness
    `B⁻¹ Aₙ B` does not exist and operator-stability need not hold in the same
    form (indeed the all-B statement over arbitrary `φ` is not generally true).
    The mathematically correct closure statement is the invertible case, proved
    here via the conjugation/transpose witness; invertibility enters exactly at
    `B * ⅟B = 1` (`mul_invOf_self`). The singular case is genuinely
    distribution-dependent and is intentionally not asserted. -/
theorem operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
    (hφ : IsOperatorStable d φ) (B : Matrix (Fin d) (Fin d) ℝ) [Invertible B] :
    IsOperatorStable d (fun ξ => φ (fun i => ∑ j, B i j * ξ j)) := by
  obtain ⟨A, b, hAb⟩ := hφ
  -- Composition of matrix-vector products (hand-rolled to avoid lemma churn).
  have mvmv : ∀ (M N : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ),
      M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v := by
    intro M N v
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
               Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun n => ⅟B * A n * B, fun n => Bᵀ *ᵥ b n, ?_⟩
  intro n hn ξ
  -- B (B⁻¹ Aₙ B) = Aₙ B (invertibility used here).
  have hM : B * (⅟B * A n * B) = A n * B := by
    rw [← mul_assoc, ← mul_assoc, mul_invOf_self, one_mul]
  -- ⟨bₙ, Bξ⟩ = ⟨Bᵀbₙ, ξ⟩ (drift transport by the transpose).
  have hdrift : vecInner d (b n) (B *ᵥ ξ) = vecInner d (Bᵀ *ᵥ b n) ξ := by
    simp only [vecInner, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
               Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  show (φ (B *ᵥ ((⅟B * A n * B) *ᵥ ξ))) ^ n
     = φ (B *ᵥ ξ) * Complex.exp (I * (vecInner d (Bᵀ *ᵥ b n) ξ : ℝ))
  rw [mvmv, hM, ← mvmv]
  have happ := hAb n hn (B *ᵥ ξ)
  rw [show (fun i => ∑ j, A n i j * (B *ᵥ ξ) j) = A n *ᵥ (B *ᵥ ξ) from rfl] at happ
  rw [happ, hdrift]

/-- The trivial 1-dimensional operator-stable family: constant functions are stable
    with any normalization (they satisfy the stability equation trivially). -/
theorem const_one_is_operator_stable (d : ℕ) : IsOperatorStable d (fun _ => (1 : ℂ)) := by
  refine ⟨fun _ => 0, fun _ _ => 0, fun n _ ξ => ?_⟩
  simp [vecInner]

-- ============================================================
-- PART VI: Axiomatized Hard Results
-- ============================================================

/-- Hudson-Mason scalar exponent bound (vacuous form — broken hypothesis).
    For a "non-degenerate" operator-stable law φ admitting a scalar exponent c
    (normalizations A_n = n^{-c}·I), we have c ≥ 1/2. This is the scalar
    specialization of the general eigenvalue bound (Hudson-Mason 1982).

    Mathematical content (Hudson-Mason 1982): every eigenvalue λ of the
    exponent matrix satisfies Re(λ) ≥ 1/2; for E = c·I, this collapses to
    c ≥ 1/2. The general eigenvalue formulation requires a complex-spectrum
    API (Matrix.eigenvalues was removed at Mathlib v4.26.0 in favor of the
    Hermitian-restricted IsHermitian.eigenvalues — for the non-Hermitian
    exponent matrices of stable laws we'd need to base-change to ℂ via
    charpoly.roots, mathlib-grade scaffolding outside this file's scope).

    **S14 ACT discharge note (2026-06-06):** the original `axiom` carried a
    non-degeneracy hypothesis `hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False`,
    intended to mean "the underlying distribution is non-degenerate." That
    statement is, however, *logically unsatisfiable* — instantiating at
    `v = 0` gives `(∀ i, (0 : Fin d → ℝ) i = 0)` (immediate by `rfl`), so
    `hnd` would entail `False`. Consequently the axiom is provable vacuously
    by `exfalso` + applying `hnd` at the zero vector. We promote it to a
    theorem to make the encoding bug visible: a future revision should
    replace `hnd` with a genuine non-degeneracy hypothesis such as
    `Nontrivial (Fin d → ℝ)` (equivalently `0 < d`) plus an actual support
    condition, then re-axiomatize (or re-prove) the bound.

    Specialization at α-stable: c = 1/α ≥ 1/2 means α ≤ 2 — the classical
    constraint that stable laws have index ≤ 2. -/
theorem scalar_exponent_ge_half (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ)
    (_hSE : HasScalarExponent d φ c)
    (hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False) :
    1 / 2 ≤ c := by
  exfalso
  exact hnd (fun _ => 0) (fun _ => rfl)

/-- **AXIOM**: Meerschaert-Scheffler Domain of Attraction Theorem.
    A probability distribution (given by char function φ) is in the operator domain
    of attraction of some operator-stable law iff its tail measure is matrix regularly
    varying.

    Forward: DOA → tail is regularly varying with matrix exponent E.
    Converse: matrix regularly varying tail → DOA.

    Reference: Meerschaert & Scheffler (2001), Theorem 8.2.1 and Chapter 8.
    This is the definitive generalization of Gnedenko-Kolmogorov to ℝ^d. -/
axiom meerschaert_scheffler (d : ℕ)
    (φ : (Fin d → ℝ) → ℂ) :
    (∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ) ↔
    ∃ (E : Matrix (Fin d) (Fin d) ℝ) (ν : (Fin d → ℝ) → ℂ),
      ∀ t : ℝ, 0 < t →
      ∀ ξ : Fin d → ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          (φ (fun i => (n : ℝ) * ξ i)) ^ n /
          ν (fun i => ∑ j, NormedSpace.exp ℝ (Real.log t • E) i j * ξ j))
        Filter.atTop (nhds 1)

-- ============================================================
-- PART VII: Recovering Classical Results
-- ============================================================

/-- The Gaussian N(0, Sg) is in its own operator domain of attraction.

    Discharges the v4.26.0 axiomatized version (whose original proof leaked
    a pointwise-vs-function-valued `tendsto_const_nhds` confusion) by:
    1. Witnessing the matrix scaling `A_n = n^(-1/2) • I` and zero drift `b_n = 0`.
    2. Reducing tendsto in the function space `(Fin d → ℝ) → ℂ` to pointwise
       via `tendsto_pi_nhds`.
    3. For each fixed ξ, observing that for n ≥ 1 the n-th term equals
       `gaussCharFun d Sg ξ` exactly (eventually constant — NOT pointwise
       constant on a non-constant function sequence, avoiding the v4.26.0
       elaborator block).
    4. Applying `tendsto_atTop_of_eventually_const` (Mathlib v4.26.0 surgical
       successor of the broken `tendsto_const_nhds` invocation).

    The matrix-product reduction `(A_n^T ξ) i = ξ i / √n` reuses the verified
    simp set from S11 ACT (PR #21987). Mathematical content: multivariate CLT
    self-similarity for the Gaussian. -/
theorem gaussian_in_own_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    InOperatorDomainOfAttraction d (gaussCharFun d Sg) (gaussCharFun d Sg) := by
  refine ⟨gaussian_is_operator_stable d Sg, ?_⟩
  refine ⟨fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
          fun _ => 0, ?_⟩
  rw [tendsto_pi_nhds]
  intro ξ
  apply tendsto_atTop_of_eventually_const (i₀ := 1)
  intro n hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Reduce the matrix product (A_n^T ξ) i = ξ i / √n
  have h_arg : (fun i => ∑ j, ((n : ℝ) ^ (-(1 / 2 : ℝ)) •
                  (1 : Matrix (Fin d) (Fin d) ℝ)) i j * ξ j)
             = (fun i => ξ i / Real.sqrt n) := by
    funext i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
               mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
               Finset.mem_univ, if_true]
    rw [mul_comm, Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  rw [h_arg]
  -- vecInner d 0 ξ = 0 → exp factor collapses to 1
  have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by simp [vecInner]
  rw [h_inner, show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]
  exact gaussian_operator_stable d Sg ξ n hn0

/-- D-dimensional extension of the DoA for finite-covariance laws
    (vacuous discharge — bug report).

    **S16 ACT discharge note (2026-06-10):** the original `axiom` carried a
    hypothesis bundle `hφ_char : φ 0 = 1` and `hφ_cov : ∃ (_ : True),
    Tendsto φ (nhds 0) (nhds 1)`. That bundle is missing the crucial
    *finite-second-moment* content of the classical multivariate CLT —
    `hφ_cov` is just continuity-at-0 wrapped under a trivial existential
    over `True`, and `hSg` is unused. Without finite covariance, the
    matrix Lindeberg-CLT premise is not in scope.

    However, the conclusion is an *existential* over ψ: `∃ ψ, φ ∈ DoA(ψ)`.
    The trivial degenerate-Gaussian witness `ψ = (fun _ => 1)` (= the
    characteristic function of the Dirac mass at 0, i.e. `gaussCharFun d 0`)
    is operator-stable (`const_one_is_operator_stable`). With zero-matrix
    scaling `A_n = 0` and zero drift `b_n = 0`, the n-th convolution term is
    `(φ (fun _ => 0))^n · exp(I·0) = 1^n · 1 = 1` (using `hφ_char`),
    identically the constant function ψ. The DoA tendsto then collapses to
    `tendsto_const_nhds` on the constant sequence.

    This is the S14 pattern applied to S16: an axiom whose hypothesis
    bundle is too weak for the strong statement it advertises, dischargeable
    vacuously via the existential conclusion's freedom. A future revision
    should replace `hφ_cov` with a genuine finite-covariance hypothesis
    (e.g., `φ` is twice continuously differentiable at 0 with Hessian `-Sg`,
    or equivalently the second-moment bound `∫ ‖x‖² dμ(x) < ∞` translated to
    the characteristic function), then either re-axiomatize as the matrix
    Lindeberg-CLT or supply a proper proof.

    Reference (for the intended-but-unachievable strong statement):
    Meerschaert & Scheffler (2001) Theorem 7.1.1 / Hudson-Mason (1981). -/
theorem finite_cov_in_gaussian_doa (d : ℕ) (_Sg : Matrix (Fin d) (Fin d) ℝ)
    (_hSg : Matrix.PosSemidef _Sg)
    (φ : (Fin d → ℝ) → ℂ)
    (hφ_char : φ (fun _ => 0) = 1)
    (_hφ_cov : ∃ (_hφ_reg : True),
      Filter.Tendsto (fun ξ : Fin d → ℝ => φ ξ) (nhds 0) (nhds 1)) :
    ∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ := by
  -- Trivial degenerate-Gaussian witness ψ = const 1.
  refine ⟨fun _ => (1 : ℂ), const_one_is_operator_stable d, ?_⟩
  -- Witness A_n = 0 (zero matrix), b_n = 0.
  refine ⟨fun _ => (0 : Matrix (Fin d) (Fin d) ℝ), fun _ => (0 : Fin d → ℝ), ?_⟩
  -- The n-th sequence term is identically the constant function (fun _ => 1).
  have h_seq :
      (fun n : ℕ => fun ξ : Fin d → ℝ =>
        (φ (fun i => ∑ j, (0 : Matrix (Fin d) (Fin d) ℝ) i j * ξ j)) ^ n *
        exp (I * (vecInner d (0 : Fin d → ℝ) ξ : ℝ)))
      = (fun _ : ℕ => fun _ : (Fin d → ℝ) => (1 : ℂ)) := by
    funext n ξ
    have h_arg :
        (fun i : Fin d => ∑ j, (0 : Matrix (Fin d) (Fin d) ℝ) i j * ξ j)
        = (fun _ : Fin d => (0 : ℝ)) := by
      funext i; simp
    have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by simp [vecInner]
    rw [h_arg, hφ_char, one_pow, h_inner]
    simp
  rw [h_seq]
  exact tendsto_const_nhds

end

end OperatorStable
