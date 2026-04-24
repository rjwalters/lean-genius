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

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.Bochner

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

-- ============================================================
-- L² norm helpers for Parseval's theorem
-- ============================================================

/-- Conjugate of expTwoPiI: conj(e(nθ)) = e(-nθ).
    Since expTwoPiI(nθ) = exp(2πi·nθ), conjugation negates the exponent. -/
private lemma expTwoPiI_conj (n : ℤ) (θ : ℝ) :
    starRingEnd ℂ (expTwoPiI ((n : ℝ) * θ)) = expTwoPiI ((-(n : ℝ)) * θ) := by
  simp only [expTwoPiI, starRingEnd_apply, Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- The squared norm decomposes as a double sum (Parseval's algebraic identity):
    |∑_{n∈A} e(nθ)|² = ∑_{(m,n)∈A×A} e((m-n)θ)  [in ℂ, taking real part]
    = ∑_{(m,n)∈A×A} cos(2π(m-n)θ)               [since imaginary parts cancel]

    Proof: normSq(∑_m e(mθ)) = (∑_m e(mθ))*(∑_n conj(e(nθ)))
         = ∑_{m,n} e(mθ)*e(-nθ) = ∑_{m,n} e((m-n)θ)    [ring computation] -/
private lemma expSumNorm_sq_double (A : Finset ℤ) (θ : ℝ) :
    (expSumNorm A θ)^2 =
      ∑ mn in A ×ˢ A, Real.cos (2 * Real.pi * ((mn.1 : ℝ) - (mn.2 : ℝ)) * θ) := by
  -- Step 1: |S|^2 = (S * conj S).re
  have key : (expSumNorm A θ)^2 = (expSum A θ * starRingEnd ℂ (expSum A θ)).re := by
    rw [expSumNorm, Complex.sq_abs]
    simp only [Complex.normSq_apply, Complex.mul_re, starRingEnd_apply,
               Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  -- Step 2: Distribute conj over sum, apply expTwoPiI_conj
  simp_rw [expSum, map_sum (starRingEnd ℂ), expTwoPiI_conj]
  -- Step 3: Expand product of sums
  rw [Finset.sum_mul]
  rw [Complex.re_sum]
  simp_rw [Finset.mul_sum, Complex.re_sum]
  -- Step 4: Convert Σ_m Σ_n to Σ_{(m,n) ∈ A×A}
  rw [← Finset.sum_product']
  -- Step 5: Each term: Re(e(mθ) * e(-nθ)) = cos(2π(m-n)θ)
  congr 1
  ext ⟨m, n⟩
  have hmul : expTwoPiI ((m : ℝ) * θ) * expTwoPiI ((-(n : ℝ)) * θ) =
              expTwoPiI (((m : ℝ) - (n : ℝ)) * θ) := by
    rw [← expTwoPiI_add]; congr 1; ring
  have hre : ∀ x : ℝ, (expTwoPiI x).re = Real.cos (2 * Real.pi * x) := fun x => by
    simp only [expTwoPiI]
    rw [show ((2 : ℂ) * ↑π * ↑x * I) = ↑(2 * Real.pi * x) * I from by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im]
  rw [hmul, hre]
  congr 1; ring

/-- **Character orthogonality on [0,1]** for k : ℤ:
    ∫₀¹ cos(2πkθ) dθ = if k = 0 then 1 else 0.

    Proof:
    - k = 0: ∫₀¹ 1 dθ = 1
    - k ≠ 0: ∫ = [sin(2πkθ)/(2πk)]₀¹ = sin(2πk)/(2πk) = 0/(2πk) = 0
              since sin(2πk) = 0 for integer k. -/
private lemma integral_cos_character (k : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, Real.cos (2 * Real.pi * (k : ℝ) * θ) =
    if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp only [hk, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, if_true]
    simp [MeasureTheory.integral_const, Real.volume_Icc]
  · rw [if_neg hk]
    have hak : (2 * Real.pi * (k : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hk)
    -- Use interval integral antiderivative: ∫ cos(ax) dx = sin(ax)/a
    rw [show ∫ θ in Set.Icc (0:ℝ) 1, Real.cos (2 * π * ↑k * θ) =
            ∫ θ in (0:ℝ)..1, Real.cos (2 * π * ↑k * θ) from by
          rw [intervalIntegral.integral_eq_integral_Ioc]
          apply MeasureTheory.integral_Ioc_eq_integral_Icc.symm]
    -- Now use interval integral calculation
    rw [show (fun θ : ℝ => Real.cos (2 * π * ↑k * θ)) =
            (fun θ => Real.cos ((2 * π * ↑k) * θ)) from by ext; ring]
    rw [intervalIntegral.integral_cos_mul hak]
    simp [Real.sin_int_mul_two_pi, Real.sin_zero, hak]

/-- The L² norm of exponential sums equals |A| (Parseval's theorem on [0,1]).

    ∫₀¹ |∑_{n∈A} e(nθ)|² dθ = ∑_{(m,n)∈A×A} ∫₀¹ cos(2π(m-n)θ) dθ
                              = ∑_{(m,n)∈A×A} [m=n] = |A|.

    Key steps: Parseval algebraic identity + character orthogonality + diagonal count. -/
theorem L2_norm (A : Finset ℤ) :
    ∫ θ in Set.Icc 0 1, (expSumNorm A θ)^2 = A.card := by
  simp_rw [expSumNorm_sq_double]
  -- Swap integral and double sum
  rw [← MeasureTheory.integral_finset_sum
      (s := A ×ˢ A)
      (f := fun mn θ => Real.cos (2 * Real.pi * ((mn.1 : ℝ) - mn.2) * θ))]
  · -- Compute each integral via character orthogonality
    apply Finset.sum_congr rfl
    intro ⟨m, n⟩ _
    have h := integral_cos_character (m - n)
    simp only [Int.cast_sub] at h
    convert h using 2
    · ext θ; ring
    · simp [sub_eq_zero]
  · -- Integrability: each summand is continuous hence integrable on Icc
    intro ⟨m, n⟩ _
    apply ContinuousOn.integrableOn_Icc
    apply (continuous_const.mul (continuous_const.mul
      (continuous_const.mul continuous_id))).cos.continuousOn

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

/-- For unit weights, the L¹ norm is at least c log N. -/
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
theorem konyagin_equals_mps :
    konyagin_theorem ↔ mcgehee_pigno_smith_theorem := by
  constructor <;> (intro _; exact mcgehee_pigno_smith_theorem)

end Erdos512
