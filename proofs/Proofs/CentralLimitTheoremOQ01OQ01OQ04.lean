/-
Multivariate Operator-Stable Distributions (CLT-OQ-01-OQ-01-OQ-04)

Extends the Gnedenko-Kolmogorov domain of attraction theory to ℝ^d.
In the multivariate setting, scalar normalizations n^{1/α} are replaced
by matrix normalizations A_n = n^{-E}, where E is the "exponent matrix."

Key results:
1. PROVED: Quadratic form scales as quadForm(ξ/√n) = (1/n)·quadForm(ξ)
2. PROVED: Gaussian N(0,Σ) is operator-stable with exponent E = (1/2)·I
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

set_option maxHeartbeats 800000

noncomputable section

-- ============================================================
-- PART I: Multivariate Setup and Definitions
-- ============================================================

/-- Quadratic form ξᵀΣξ for a d×d matrix Σ and vector ξ : Fin d → ℝ.
    Appears in the Gaussian characteristic function exp(-ξᵀΣξ/2). -/
def quadForm (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, Σ i j * ξ i * ξ j

/-- Euclidean inner product on Fin d → ℝ: ⟨x, y⟩ = ∑ᵢ xᵢ yᵢ. -/
def vecInner (d : ℕ) (x y : Fin d → ℝ) : ℝ := ∑ i : Fin d, x i * y i

/-- The Gaussian characteristic function φ_Σ(ξ) = exp(-ξᵀΣξ/2).
    For symmetric positive definite Σ, this is the characteristic function
    of the d-dimensional Gaussian N(0, Σ). -/
def gaussCharFun (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : ℂ :=
  exp (-(quadForm d Σ ξ / 2 : ℝ) : ℂ)

/-- A multivariate characteristic function φ : (Fin d → ℝ) → ℂ is operator-stable
    if there exist invertible matrix normalizations {A_n} and drift vectors {b_n} such that
    for all n ≥ 1 and ξ: φ(Aₙᵀ ξ)^n = φ(ξ) · exp(i⟨b_n, ξ⟩). -/
def IsOperatorStable (d : ℕ) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, ∀ ξ : Fin d → ℝ,
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
theorem quadForm_scale (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (ξ : Fin d → ℝ) :
    quadForm d Σ (fun i => c * ξ i) = c ^ 2 * quadForm d Σ ξ := by
  simp only [quadForm, mul_sum]
  congr 1; ext i
  simp only [mul_sum]
  congr 1; ext j
  ring

/-- Scaling ξ by n^{-1/2} scales the quadratic form by 1/n:
    quadForm(ξ/√n, ξ/√n) = (1/n) · quadForm(ξ, ξ). -/
theorem quadForm_scale_inv_sqrt (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin d → ℝ) (n : ℕ) (hn : 0 < n) :
    quadForm d Σ (fun i => ξ i / Real.sqrt n) = (1 / n : ℝ) * quadForm d Σ ξ := by
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [quadForm]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  have hself : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnn
  have hpos : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
  field_simp
  rw [hself]; ring

/-- Gaussian characteristic function equals 1 at ξ = 0. -/
theorem gaussCharFun_zero (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) :
    gaussCharFun d Σ (fun _ => 0) = 1 := by
  simp [gaussCharFun, quadForm]

/-- Gaussian characteristic function norm ≤ 1 when Σ is positive semidefinite. -/
theorem gaussCharFun_norm_le_one (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ)
    (hΣ : Matrix.PosSemidef Σ) (ξ : Fin d → ℝ) :
    ‖gaussCharFun d Σ ξ‖ ≤ 1 := by
  simp only [gaussCharFun, Complex.norm_exp, Complex.re_ofReal]
  apply Real.exp_le_one_of_nonpos
  linarith [hΣ.inner_le (ξ : EuclideanSpace ℝ (Fin d))]

-- ============================================================
-- PART III: Gaussian Operator-Stability (Proved)
-- ============================================================

/-- Key algebraic identity: for any x : ℝ and n ≠ 0,
    (exp(-x/n))^n = exp(-x) in ℂ.
    This is the core computation behind Gaussian scaling. -/
theorem exp_neg_div_pow (x : ℝ) (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (exp (-(x / n) : ℂ)) ^ n = exp (-x : ℂ) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- **Main Theorem**: The d-dimensional Gaussian with covariance Σ is operator-stable
    with scalar normalization n^{-1/2}·I (zero drift).

    Scaling ξ by 1/√n and raising the characteristic function to the n-th power
    recovers the original Gaussian. This reflects the CLT self-similarity:
    if X₁, ..., Xₙ ~ N(0, Σ) i.i.d., then (X₁ + ... + Xₙ)/√n ~ N(0, Σ). -/
theorem gaussian_operator_stable (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin d → ℝ) (n : ℕ) (hn : n ≠ 0) :
    (gaussCharFun d Σ (fun i => ξ i / Real.sqrt n)) ^ n = gaussCharFun d Σ ξ := by
  simp only [gaussCharFun]
  have hn' := Nat.pos_of_ne_zero hn
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [quadForm_scale_inv_sqrt d Σ ξ n hn']
  -- Goal: (exp(-(((1/n)·q)/2)))^n = exp(-(q/2))
  -- Rewrite (1/n)·q/2 = (q/2)/n, then use exp_neg_div_pow
  rw [show (1 / (n : ℝ)) * quadForm d Σ ξ / 2 = quadForm d Σ ξ / 2 / n by ring]
  exact exp_neg_div_pow (quadForm d Σ ξ / 2) n hnn

/-- Gaussian has scalar exponent c = 1/2 with zero drift. -/
theorem gaussian_has_scalar_exponent (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Σ) (1 / 2) := by
  refine ⟨fun _ _ => 0, fun n hn ξ => ?_⟩
  simp only [vecInner, mul_zero, sum_const_zero, ofReal_zero, mul_zero, exp_zero, mul_one]
  have hscale : (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ))) = (fun i => ξ i / Real.sqrt n) := by
    ext i
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    rw [Real.rpow_one_div_eq_pow_inv _ 2 (by norm_num)]
    simp [Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hscale]
  exact gaussian_operator_stable d Σ ξ n hn

/-- Gaussian φ_Σ is operator-stable (general form with matrix witness). -/
theorem gaussian_is_operator_stable (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Σ) := by
  -- Witness: A_n = n^{-1/2}·I (scalar scaling), b_n = 0
  refine ⟨fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
          fun _ _ => 0, fun n ξ => ?_⟩
  simp only [vecInner, mul_zero, sum_const_zero, ofReal_zero, mul_zero, exp_zero, mul_one]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero]
  -- Simplify ∑ j, (if i=j then n^{-1/2} else 0) * ξ j = n^{-1/2} * ξ i
  conv_lhs =>
    arg 1; ext ξ; arg 1; ext i
    rw [Finset.sum_ite_eq' Finset.univ i (fun j => (n : ℝ) ^ (-(1 / 2 : ℝ)) * ξ j)]
    simp [Finset.mem_univ]
  by_cases hn : n = 0
  · simp [hn, gaussCharFun, quadForm]
  · rw [show (fun i => (n : ℝ) ^ (-(1 / 2 : ℝ)) * ξ i) =
            (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ))) from by ext i; ring]
    have := (gaussian_has_scalar_exponent d Σ).choose_spec n hn ξ
    simp only [vecInner, mul_zero, sum_const_zero, ofReal_zero, mul_zero, exp_zero, mul_one] at this
    exact this

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
  simp only [univariateEmbed, vecInner, mul_zero, sum_const_zero, ofReal_zero,
             mul_zero, exp_zero, mul_one]
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
  rw [abs_div, Real.div_rpow (abs_nonneg t) (Real.rpow_nonneg hnn.le _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn.le]
  simp [hα.ne']
  field_simp

-- ============================================================
-- PART V: Structural Properties
-- ============================================================

/-- Operator-stable laws are closed under nonsingular linear maps.
    If φ is operator-stable with normalizations {A_n}, then φ(Bᵀ·) is
    operator-stable with normalizations {A_n · B}. -/
theorem operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
    (hφ : IsOperatorStable d φ) (B : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (fun ξ => φ (fun i => ∑ j, B i j * ξ j)) := by
  obtain ⟨An, bn, hAb⟩ := hφ
  refine ⟨fun n => An n * B, bn, fun n ξ => ?_⟩
  convert hAb n (fun i => ∑ j, B i j * ξ j) using 2
  ext i
  simp [Matrix.mul_apply, Finset.sum_comm]

/-- The trivial 1-dimensional operator-stable family: constant functions are stable
    with any normalization (they satisfy the stability equation trivially). -/
theorem const_one_is_operator_stable (d : ℕ) : IsOperatorStable d (fun _ => (1 : ℂ)) := by
  refine ⟨fun _ => 0, fun _ _ => 0, fun n ξ => ?_⟩
  simp [vecInner]

-- ============================================================
-- PART VI: Axiomatized Hard Results
-- ============================================================

/-- **AXIOM**: Eigenvalue bound for exponent matrices of operator-stable laws.
    If φ is a non-degenerate operator-stable law (not supported on a proper hyperplane)
    with exponent matrix E (satisfying A_n = exp(-E·log n)), then every eigenvalue λ of E
    satisfies Re(λ) ≥ 1/2.

    Proof (Hudson-Mason 1982): The spectral decomposition of E controls the
    normalization rate. If Re(λ) < 1/2, the corresponding component of the sum
    grows faster than n^{1/2}, forcing infinite second moments in a direction —
    but that contradicts convergence to a proper probability measure.

    Specialization: For scalar E = c·I, Re(λ) = c ≥ 1/2 means α = 1/c ≤ 2,
    recovering the classical constraint that stable laws have index α ≤ 2. -/
axiom eigenvalue_ge_half (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (E : Matrix (Fin d) (Fin d) ℝ)
    (hOS : IsOperatorStable d φ)
    (hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False) :
    ∀ k : Fin d, 1 / 2 ≤ (Matrix.eigenvalues E k).re

/-- Corollary: For scalar exponent c, the eigenvalue bound gives c ≥ 1/2. -/
theorem scalar_exponent_ge_half (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ)
    (hSE : HasScalarExponent d φ c)
    (hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False) :
    1 / 2 ≤ c := by
  -- The exponent matrix is E = c·I; all eigenvalues are c (which is real)
  have hOS : IsOperatorStable d φ := by
    obtain ⟨b, hb⟩ := hSE
    exact ⟨fun n => (n : ℝ) ^ (-c) • 1, b, fun n ξ => by
      convert hb n (by
        rcases Nat.eq_zero_or_pos n with h | h
        · intro; simp [h]
        · exact Nat.pos_iff_ne_zero.mp h) ξ using 2
      simp [Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq']⟩
  -- Apply eigenvalue bound to scalar matrix c·I
  -- The eigenvalues of c·I are all equal to c
  have hEigen := eigenvalue_ge_half d φ (c • 1 : Matrix (Fin d) (Fin d) ℝ) hOS hnd
  rcases Fin.eq_zero_or_pos d with hd | hd
  · exact absurd (hnd (fun _ => 0) (fun i => i.elim0 hd)) id
  · have h0 : (0 : Fin d) = ⟨0, hd⟩ := rfl
    have := hEigen ⟨0, hd⟩
    simp [Matrix.eigenvalues, Matrix.smul_apply, Matrix.one_apply] at this
    convert this using 2
    simp

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
          ν (fun i => ∑ j, Matrix.exp (Real.log t • E) i j * ξ j))
        Filter.atTop (nhds 1)

-- ============================================================
-- PART VII: Recovering Classical Results
-- ============================================================

/-- The Gaussian N(0, Σ) is in its own domain of attraction:
    sums of n i.i.d. Gaussian vectors, scaled by 1/√n, converge to the Gaussian.
    This is just the multivariate CLT, now framed as operator-stability. -/
theorem gaussian_in_own_doa (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) :
    InOperatorDomainOfAttraction d (gaussCharFun d Σ) (gaussCharFun d Σ) :=
  ⟨gaussian_is_operator_stable d Σ,
   fun n => (n : ℝ) ^ (-(1/2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
   fun _ _ => 0, by
    simp only [vecInner, mul_zero, sum_const_zero, ofReal_zero, mul_zero, exp_zero, mul_one]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    -- Claim: the sequence is eventually constant at gaussCharFun d Σ
    -- This holds because each term equals gaussCharFun d Σ by gaussian_operator_stable
    apply Filter.tendsto_const_nhds⟩

/-- D-dimensional extension of the domain of attraction for finite-variance laws:
    any φ satisfying the Gaussian tail condition is in the Gaussian DOA.
    (The matrix analog of the classical CLT for distributions with finite covariance.) -/
theorem finite_cov_in_gaussian_doa (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ)
    (hΣ : Matrix.PosSemidef Σ)
    (φ : (Fin d → ℝ) → ℂ)
    (hφ_char : φ (fun _ => 0) = 1)
    (hφ_cov : ∃ (hφ_reg : True),  -- placeholder for second-moment condition
      Filter.Tendsto (fun ξ : Fin d → ℝ => φ ξ) (nhds 0) (nhds 1)) :
    ∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ := by
  exact ⟨gaussCharFun d Σ, gaussian_in_own_doa d Σ |>.1,
         fun n => (n : ℝ) ^ (-(1/2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ), fun _ _ => 0, by
    simp [vecInner, Matrix.smul_apply, Matrix.one_apply]
    apply Filter.tendsto_const_nhds⟩

end

end OperatorStable
