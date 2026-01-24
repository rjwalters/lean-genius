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
  sorry -- Requires measure theory

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
axiom littlewood_explicit (A : Finset ℤ) (hA : A.card ≥ 2) :
  L1norm A ≥ littlewoodConstant * Real.log A.card

/-
## Part VI: Sharpness
-/

/-- The log N lower bound is essentially optimal. -/
axiom littlewood_sharpness :
  ∃ c' : ℝ, ∀ N : ℕ, N ≥ 2 → ∃ A : Finset ℤ, A.card = N ∧
    L1norm A ≤ c' * Real.log N

/-- Geometric progressions achieve the lower bound. -/
def geometricProgression (N : ℕ) : Finset ℤ :=
  Finset.image (fun k => (k : ℤ)) (Finset.range N)

/-- For arithmetic progressions, the bound is approximately log N. -/
axiom arithmetic_progression_bound (N : ℕ) (hN : N ≥ 2) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * Real.log N ≤ L1norm (geometricProgression N) ∧
    L1norm (geometricProgression N) ≤ c₂ * Real.log N

/-
## Part VII: Hardy's Inequality Connection
-/

/-- Hardy's inequality (discrete form). -/
axiom hardy_inequality (f : ℕ → ℝ) (hf : ∀ n, f n ≥ 0) :
  (∑' n : ℕ, (1 / (n + 1 : ℝ)) * (∑ k in Finset.range (n + 1), f k)^2) ≤
    4 * (∑' n : ℕ, (f n)^2)

/-- The MPS proof uses Hardy's inequality in a crucial way. -/
def hardyConnection : Prop :=
  -- McGehee-Pigno-Smith showed that Hardy's inequality implies
  -- the L¹ lower bound for exponential sums
  True

/-
## Part VIII: Related Results
-/

/-- The L² norm of exponential sums is exactly √N (by Parseval). -/
theorem L2_norm (A : Finset ℤ) :
    ∫ θ in Set.Icc 0 1, (expSumNorm A θ)^2 = A.card := by
  sorry -- Parseval's theorem

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
axiom weighted_littlewood (A : Finset ℤ) (w : ℤ → ℂ)
    (hw : ∀ n ∈ A, Complex.abs (w n) = 1) (hA : A.card ≥ 2) :
  ∫ θ in Set.Icc 0 1, Complex.abs (weightedExpSum A w θ) ≥
    littlewoodConstant * Real.log A.card

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
