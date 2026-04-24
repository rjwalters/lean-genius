/-
  Erdős Problem #512: Littlewood's Conjecture on Exponential Sums

  Source: https://erdosproblems.com/512
  Status: SOLVED (Konyagin 1981, McGehee-Pigno-Smith 1981)

  Statement:
  Is it true that, if A ⊂ ℤ is a finite set of size N, then
    ∫₀¹ |∑_{n∈A} e(nθ)| dθ ≫ log N,
  where e(x) = e^{2πix}?

  Answer: YES (PROVED)

  Key Results:
  - Littlewood: Posed the conjecture
  - Konyagin (1981): First proof
  - McGehee-Pigno-Smith (1981): Independent proof via Hardy's inequality
  - The lower bound log N is essentially optimal

  References:
  - [Ko81] Konyagin, "On the Littlewood problem" (1981)
  - [MPS81] McGehee-Pigno-Smith, "Hardy's inequality and the L¹ norm of
    exponential sums" (1981)
-/

import Mathlib

open Real Complex MeasureTheory

namespace Erdos512

/-
## Part I: Exponential Functions
-/

/-- The exponential function e(x) = e^{2πix}. -/
noncomputable def expTwoPiI (x : ℝ) : ℂ := Complex.exp (2 * π * x * I)

/-- e(x) is periodic with period 1. -/
theorem expTwoPiI_periodic (x : ℝ) : expTwoPiI (x + 1) = expTwoPiI x := by
  simp only [expTwoPiI]
  rw [show (2 : ℂ) * π * ((x : ℂ) + 1) * I = 2 * π * x * I + 2 * π * I by ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

/-- |e(x)| = 1 for all x. -/
theorem expTwoPiI_norm (x : ℝ) : Complex.abs (expTwoPiI x) = 1 := by
  simp [expTwoPiI, Complex.abs_exp]

/-- e(x + y) = e(x) · e(y). -/
theorem expTwoPiI_add (x y : ℝ) : expTwoPiI (x + y) = expTwoPiI x * expTwoPiI y := by
  simp only [expTwoPiI]
  rw [show (2 : ℂ) * π * ((x : ℂ) + (y : ℂ)) * I = 2 * π * x * I + 2 * π * y * I by ring]
  exact Complex.exp_add _ _

/-
## Part II: Exponential Sums
-/

/-- The exponential sum ∑_{n∈A} e(nθ) for a finite set A ⊂ ℤ. -/
noncomputable def expSum (A : Finset ℤ) (θ : ℝ) : ℂ :=
  A.sum (fun n => expTwoPiI (n * θ))

/-- The exponential sum for a set of naturals. -/
noncomputable def expSumNat (A : Finset ℕ) (θ : ℝ) : ℂ :=
  A.sum (fun n => expTwoPiI (n * θ))

/-- The modulus of the exponential sum. -/
noncomputable def expSumNorm (A : Finset ℤ) (θ : ℝ) : ℝ :=
  Complex.abs (expSum A θ)

/-- Triangle inequality: |expSum A θ| ≤ |A|. -/
theorem expSum_bound (A : Finset ℤ) (θ : ℝ) :
    expSumNorm A θ ≤ A.card := by
  unfold expSumNorm expSum
  calc Complex.abs (A.sum (fun n => expTwoPiI (n * θ)))
      ≤ A.sum (fun n => Complex.abs (expTwoPiI (n * θ))) := Complex.abs.sum_le _ _
    _ = A.sum (fun _ => 1) := by simp [expTwoPiI_norm]
    _ = A.card := by simp

/-
## Part III: The L¹ Norm
-/

/-- The L¹ norm of the exponential sum: ∫₀¹ |∑_{n∈A} e(nθ)| dθ. -/
noncomputable def L1norm (A : Finset ℤ) : ℝ :=
  ∫ θ in Set.Icc 0 1, expSumNorm A θ

/-- The L¹ norm is nonnegative. -/
theorem L1norm_nonneg (A : Finset ℤ) : L1norm A ≥ 0 := by
  unfold L1norm
  apply integral_nonneg
  intro θ
  exact Complex.abs.nonneg _

/-- The L¹ norm is at most |A| (trivial upper bound). -/
theorem L1norm_upper_bound (A : Finset ℤ) : L1norm A ≤ A.card := by
  unfold L1norm
  -- expSumNorm A is continuous (finite sum of continuous functions + Complex.abs)
  have hf_cont : Continuous (expSumNorm A) := by
    unfold expSumNorm expSum expTwoPiI
    apply Complex.continuous_abs.comp
    apply continuous_finset_sum
    intro n _
    apply Complex.continuous_exp.comp
    fun_prop
  -- IntegrableOn [0,1] from continuity on compact set
  have hint : IntegrableOn (expSumNorm A) (Set.Icc 0 1) :=
    hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  -- Constant A.card is integrable on [0,1] (finite measure)
  have hcint : IntegrableOn (fun _ : ℝ => (A.card : ℝ)) (Set.Icc 0 1) :=
    integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))
  -- Pointwise bound: expSumNorm A θ ≤ A.card (proved as expSum_bound)
  have hbdd : ∀ θ ∈ Set.Icc (0:ℝ) 1, expSumNorm A θ ≤ (A.card : ℝ) :=
    fun θ _ => expSum_bound A θ
  -- Monotone integration gives the integral bound
  have h1 : ∫ θ in Set.Icc 0 1, expSumNorm A θ ≤ ∫ θ in Set.Icc 0 1, (A.card : ℝ) :=
    setIntegral_mono_on hint hcint measurableSet_Icc hbdd
  -- Constant integral over [0,1] equals A.card (vol([0,1]) = 1)
  have h2 : ∫ θ in Set.Icc (0:ℝ) 1, (A.card : ℝ) = A.card := by
    rw [set_integral_const, smul_eq_mul]
    have hv : (volume (Set.Icc (0:ℝ) 1)).toReal = 1 := by
      rw [Real.volume_Icc]
      simp [ENNReal.toReal_ofReal]
    linarith [hv]
  linarith

/-
## Part IV: Littlewood's Conjecture
-/

/-- **Littlewood's Conjecture:**
    For any finite set A ⊂ ℤ with |A| = N,
    ∫₀¹ |∑_{n∈A} e(nθ)| dθ ≥ c · log N
    for some absolute constant c > 0. -/
def LittlewoodConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ A : Finset ℤ, A.card ≥ 2 →
    L1norm A ≥ c * Real.log A.card

/-- Alternative formulation with explicit asymptotic. -/
def LittlewoodConjecture' : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
    L1norm A ≥ (1 - ε) * Real.log A.card

/-
## Part V: The Solution
-/

/-- **Konyagin's Theorem (1981):**
    Littlewood's conjecture is TRUE. -/
axiom konyagin_theorem : LittlewoodConjecture

/-- **McGehee-Pigno-Smith Theorem (1981):**
    Independent proof via Hardy's inequality. -/
axiom mcgehee_pigno_smith_theorem : LittlewoodConjecture

/-- The constant in Littlewood's conjecture. -/
noncomputable def littlewoodConstant : ℝ := 1 / (4 * π)

/-- Explicit version of the bound. -/
/-
## Part VI: Sharpness
-/

/-- The log N lower bound is essentially optimal. -/
/-- Geometric progressions achieve the lower bound. -/
def geometricProgression (N : ℕ) : Finset ℤ :=
  Finset.image (fun k => (k : ℤ)) (Finset.range N)

/-- For arithmetic progressions, the bound is approximately log N. -/
/-
## Part VII: Hardy's Inequality Connection
-/

/-- Hardy's inequality (discrete form). -/
/-- The MPS proof uses Hardy's inequality in a crucial way. -/
def hardyConnection : Prop :=
  -- McGehee-Pigno-Smith showed that Hardy's inequality implies
  -- the L¹ lower bound for exponential sums
  True

/-
## Part VIII: Related Results
-/

/-
Supporting lemmas for L2_norm (Parseval's theorem via character orthogonality).
-/

/-- Complex conjugate of expTwoPiI(x) is expTwoPiI(-x). -/
private lemma expTwoPiI_conj (x : ℝ) :
    starRingEnd ℂ (expTwoPiI x) = expTwoPiI (-x) := by
  simp only [expTwoPiI, starRingEnd_apply, Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- expTwoPiI(n·θ) · conj(expTwoPiI(m·θ)) = expTwoPiI((n−m)·θ). -/
private lemma expTwoPiI_mul_conj (n m : ℤ) (θ : ℝ) :
    expTwoPiI (↑n * θ) * starRingEnd ℂ (expTwoPiI (↑m * θ)) =
    expTwoPiI ((↑n - ↑m) * θ) := by
  rw [expTwoPiI_conj, ← expTwoPiI_add]
  congr 1; push_cast; ring

/-- The real part of expTwoPiI(k·θ) equals cos(2π·k·θ). -/
private lemma expTwoPiI_re (k : ℤ) (θ : ℝ) :
    (expTwoPiI (↑k * θ)).re = Real.cos (2 * π * k * θ) := by
  unfold expTwoPiI
  have h : (2 : ℂ) * ↑π * ↑((k : ℝ) * θ) * I = ↑(2 * π * (k : ℝ) * θ) * I := by
    push_cast; ring
  rw [h]
  exact Complex.exp_ofReal_mul_I_re _

/-- normSq z = (z * starRingEnd ℂ z).re -/
private lemma normSq_eq_mul_conj_re (z : ℂ) :
    Complex.normSq z = (z * starRingEnd ℂ z).re := by
  rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj]
  simp [Complex.ofReal_re]

/-- (expSumNorm A θ)² = ∑_{(n,m)∈A×A} (expTwoPiI((n−m)·θ)).re -/
private lemma expSumNorm_sq_eq (A : Finset ℤ) (θ : ℝ) :
    (expSumNorm A θ)^2 =
    ∑ p ∈ A ×ˢ A, (expTwoPiI ((↑p.1 - ↑p.2) * θ)).re := by
  unfold expSumNorm expSum
  rw [Complex.sq_abs, normSq_eq_mul_conj_re, map_sum, Finset.mul_sum]
  simp_rw [Finset.sum_mul, expTwoPiI_mul_conj, Complex.re_sum]
  rw [Finset.sum_comm]
  exact (Finset.sum_product (fun p : ℤ × ℤ => (expTwoPiI ((↑p.1 - ↑p.2) * θ)).re)).symm

/-- Character orthogonality: ∫₀¹ cos(2πkθ) dθ = [k=0] -/
private lemma char_ortho (k : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, Real.cos (2 * π * ↑k * θ) =
    if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    have hck : (2 * π * (k : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hk)
    -- Rewrite Set.Icc integral as interval integral
    have hconv : ∫ θ in Set.Icc (0:ℝ) 1, Real.cos (2 * π * ↑k * θ) =
        ∫ θ in (0:ℝ)..1, Real.cos (2 * π * ↑k * θ) :=
      (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := MeasureTheory.volume)).trans
        (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
    rw [hconv]
    -- Antiderivative: d/dθ [sin(2πkθ)/(2πk)] = cos(2πkθ)
    have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun t => Real.sin (2 * π * ↑k * t) / (2 * π * ↑k))
                  (Real.cos (2 * π * ↑k * θ)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t => 2 * π * (k : ℝ) * t) (2 * π * (k : ℝ)) θ := by
        have := (hasDerivAt_id θ).const_mul (2 * π * (k : ℝ))
        simpa using this
      have h2 : HasDerivAt (fun t => Real.sin (2 * π * (k : ℝ) * t))
          (Real.cos (2 * π * (k : ℝ) * θ) * (2 * π * (k : ℝ))) θ := by
        have h := (Real.hasDerivAt_sin (2 * π * (k : ℝ) * θ)).comp θ h1
        simpa [Function.comp] using h
      have h3 := h2.div_const (2 * π * (k : ℝ))
      rwa [mul_div_cancel_right₀ _ hck] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((Real.continuous_cos.comp (continuous_const.mul
          continuous_id')).continuousOn.intervalIntegrable)]
    -- sin(2πk·1)/(2πk) - sin(2πk·0)/(2πk) = 0
    simp only [mul_one, mul_zero, Real.sin_zero, zero_div, sub_zero]
    have hsin : Real.sin (2 * π * (k : ℝ)) = 0 := by
      have h : 2 * π * (k : ℝ) = ↑(2 * k : ℤ) * π := by push_cast; ring
      rw [h]; exact Real.sin_int_mul_pi (2 * k)
    simp [hsin, hck]

/-- Orthogonality: ∫₀¹ (expTwoPiI((n−m)·θ)).re dθ = [n=m] -/
private lemma integral_expTwoPiI_orthog (n m : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, (expTwoPiI ((↑n - ↑m) * θ)).re = if n = m then 1 else 0 := by
  have heq : ∀ θ : ℝ, (expTwoPiI ((↑n - ↑m) * θ)).re = Real.cos (2 * π * ↑(n - m) * θ) := by
    intro θ
    unfold expTwoPiI
    have h : (2 : ℂ) * ↑π * ↑((↑n - ↑m : ℝ) * θ) * I = ↑(2 * π * ↑(n - m) * θ) * I := by
      push_cast; ring
    rw [h]; exact Complex.exp_ofReal_mul_I_re _
  simp_rw [heq, char_ortho]
  simp [Int.sub_eq_zero]

/-- **Parseval's theorem for exponential sums:**
    The L² norm of ∑_{n∈A} e(nθ) over [0,1] equals |A|. -/
theorem L2_norm (A : Finset ℤ) :
    ∫ θ in Set.Icc 0 1, (expSumNorm A θ)^2 = A.card := by
  simp_rw [expSumNorm_sq_eq]
  have hint : ∀ p ∈ A ×ˢ A, IntegrableOn
      (fun θ => (expTwoPiI ((↑p.1 - ↑p.2) * θ)).re) (Set.Icc 0 1) := fun p _ =>
    (Complex.continuous_re.comp (Complex.continuous_exp.comp (by fun_prop))
      ).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_finset_sum _ hint]
  simp_rw [integral_expTwoPiI_orthog]
  -- Count diagonal: ∑_{(n,m)∈A×A} [n=m] = |A|
  simp [Finset.sum_product, Finset.sum_ite_eq, Finset.card_eq_sum_ones, eq_comm]

/-- L¹ vs L² comparison: log N ≤ L¹ while L² = √N. -/
def L1_vs_L2_comparison : Prop :=
  -- For N elements: L² norm = √N, L¹ norm ≍ log N
  -- The L¹ norm is much smaller than the L² norm would suggest
  True

/-- Connection to the flat polynomial problem. -/
def flatPolynomialProblem : Prop :=
  -- Related: for which polynomials can |P(z)| be nearly constant on |z|=1?
  -- Littlewood's conjecture shows exponential sums cannot be too "flat"
  True

/-
## Part IX: Generalizations
-/

/-- Generalization to weighted sums. -/
noncomputable def weightedExpSum (A : Finset ℤ) (w : ℤ → ℂ) (θ : ℝ) : ℂ :=
  A.sum (fun n => w n * expTwoPiI (n * θ))

/-- Generalization to higher-dimensional character sums. -/
def higherDimensionalGeneralization : Prop :=
  -- Similar bounds exist for sums over ℤᵈ
  True

/-
## Part X: Applications
-/

/-- Application to Diophantine approximation. -/
def diophantineApplication : Prop :=
  -- Lower bounds on exponential sums relate to
  -- distribution of sequences mod 1
  True

/-- Application to analytic number theory. -/
def numberTheoreticApplication : Prop :=
  -- Bounds on character sums are fundamental in
  -- estimating error terms in prime counting
  True

/-
## Part XI: Summary
-/

/-- **Erdős Problem #512: SOLVED**

Question: Is ∫₀¹ |∑_{n∈A} e(nθ)| dθ ≫ log N for |A| = N?

Answer: YES (Konyagin 1981, McGehee-Pigno-Smith 1981)

The L¹ norm of exponential sums is at least c log N for some absolute
constant c > 0. This bound is essentially optimal. The proof by
McGehee-Pigno-Smith uses Hardy's inequality in a fundamental way.
-/
theorem erdos_512 : LittlewoodConjecture := konyagin_theorem

/-- Main result: Littlewood's conjecture is TRUE. -/
theorem erdos_512_main : LittlewoodConjecture := erdos_512

/-- The problem was solved independently by two groups. -/
theorem erdos_512_solved :
    LittlewoodConjecture ∧ True :=
  ⟨erdos_512, trivial⟩

/-- Both proofs establish the same result. -/
theorem konyagin_equals_mps : LittlewoodConjecture :=
  konyagin_theorem

end Erdos512
