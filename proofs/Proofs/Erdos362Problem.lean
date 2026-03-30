/-
Erdős Problem #362: Subset Sum Concentration

Source: https://erdosproblems.com/362
Status: SOLVED (Sárközy-Szemerédi 1965, Halász 1977, Stanley 1980)

Statement:
Let A ⊆ ℕ be a finite set of size N. For any fixed target t:
Q1: Are there ≪ 2^N / N^(3/2) subsets S ⊆ A with sum(S) = t?
Q2: If we also fix |S| = l, are there ≪ 2^N / N² such subsets?

Answers: YES to both!

Key Results:
- Erdős-Moser (1965): First bound with extra (log N)^(3/2) factor
- Sárközy-Szemerédi (1965): Proved Q1 affirmatively (removed log factor)
- Halász (1977): Proved Q2 affirmatively via multi-dimensional result
- Stanley (1980): Maximizing set is {-⌊(N-1)/2⌋, ..., ⌊N/2⌋}

Tags: additive-combinatorics, subset-sum, concentration, counting
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot

namespace Erdos362

open Finset Nat Real Filter BigOperators

/-
## Part 1: Subset Sum Definitions

Define the number of subsets summing to a target value.
-/

variable {α : Type*} [DecidableEq α]

/-- The sum of elements in a finite set -/
def setSum (A : Finset ℤ) : ℤ := ∑ x ∈ A, x

/-- Subsets of A that sum to target t -/
def subsetsWithSum (A : Finset ℤ) (t : ℤ) : Finset (Finset ℤ) :=
  A.powerset.filter (fun S => setSum S = t)

/-- Count of subsets summing to t -/
def countSubsetsWithSum (A : Finset ℤ) (t : ℤ) : ℕ :=
  (subsetsWithSum A t).card

/-- The concentration function: max over all targets -/
noncomputable def concentrationFunction (A : Finset ℤ) : ℕ :=
  Finset.sup (Finset.Icc (∑ x ∈ A.filter (· < 0), x) (∑ x ∈ A.filter (· ≥ 0), x))
    (fun t => countSubsetsWithSum A t)

/-
## Part 2: Question 1 - General Subset Sum Bound

For any A of size N and any target t:
  #{S ⊆ A : sum(S) = t} ≪ 2^N / N^(3/2)
-/

/-- Sárközy-Szemerédi (1965): Sharp bound answering Q1.
    Removed the log factor from the Erdős-Moser bound. -/
axiom sarkozy_szemeredi_1965 :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤ C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ)

/-- For N ≥ 3, log N ≥ 1 (since e < 3).
    Follows the pattern from Erdos442Problem.logPlus_eq_log. -/
lemma log_ge_one_of_ge_three {n : ℕ} (hn : n ≥ 3) : Real.log (n : ℝ) ≥ 1 := by
  rw [ge_iff_le, ← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9,
    show (3 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn])

/-- For x ≥ 1 and p ≥ 0, x^p ≥ 1. -/
lemma rpow_ge_one_of_ge_one {x : ℝ} {p : ℝ} (hx : x ≥ 1) (hp : p ≥ 0) :
    x ^ p ≥ 1 := by
  rw [ge_iff_le, ← Real.one_rpow p]
  exact Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx hp

/-- Erdős-Moser (1965): Weaker bound with log factor.
    First proved the concentration bound with an extra (log N)^(3/2) factor.
    This follows from the stronger Sárközy-Szemerédi bound (which removes the log factor).
    Note: requires N ≥ 3 since log(1) = 0 and log(2) < 1 make the bound degenerate.
    (The original axiom incorrectly required only N > 0, but the bound is 0 at N = 1.) -/
theorem erdos_moser_1965_bound :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card ≥ 3 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ) * (Real.log ↑A.card)^(3/2 : ℝ) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := sarkozy_szemeredi_1965
  refine ⟨C, hC_pos, fun A hA t => ?_⟩
  have h_ss := hC_bound A (by omega) t
  -- The sharp Sárközy-Szemerédi bound gives: count ≤ C * 2^N / N^(3/2)
  -- Multiplying the RHS by (log N)^(3/2) ≥ 1 (for N ≥ 3) only weakens it.
  apply le_trans h_ss
  apply le_mul_of_one_le_right
  · -- C * 2^N / N^(3/2) ≥ 0
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hC_pos) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · -- (log N)^(3/2) ≥ 1 for N ≥ 3
    exact rpow_ge_one_of_ge_one (log_ge_one_of_ge_three hA) (by norm_num)

/-- The bound 2^N / N^(3/2) is tight up to constants. -/
/-
## Part 3: Question 2 - Fixed Cardinality Bound

For any A of size N, any target t, and any fixed cardinality l:
  #{S ⊆ A : sum(S) = t, |S| = l} ≪ 2^N / N²
-/

/-- Subsets of fixed cardinality summing to t -/
def subsetsWithSumAndCard (A : Finset ℤ) (t : ℤ) (l : ℕ) : Finset (Finset ℤ) :=
  A.powerset.filter (fun S => setSum S = t ∧ S.card = l)

/-- Count of subsets with fixed sum and cardinality -/
def countSubsetsWithSumAndCard (A : Finset ℤ) (t : ℤ) (l : ℕ) : ℕ :=
  (subsetsWithSumAndCard A t l).card

/-- Halász (1977): Sharp bound answering Q2.
    With fixed cardinality constraint, the bound improves to 2^N / N². -/
axiom halasz_1977 :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, ∀ l : ℕ,
        (countSubsetsWithSumAndCard A t l : ℝ) ≤ C * 2^(A.card) / (A.card : ℝ)^2

/-
## Part 4: Stanley's Extremal Result

The symmetric set {-⌊(N-1)/2⌋, ..., ⌊N/2⌋} maximizes concentration.
Stanley's proof uses the hard Lefschetz theorem from algebraic geometry
to establish the Sperner property for certain posets.
-/

/-- The symmetric set centered at 0 -/
def symmetricSet (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N - 1 : ℕ) / 2 : ℤ) ((N : ℕ) / 2 : ℤ)

/-- Stanley (1980): Symmetric set maximizes concentration.
    Uses the hard Lefschetz theorem from algebraic geometry. -/
/-- For the symmetric set, t = 0 achieves maximum concentration. -/
/-
## Part 5: Multi-dimensional Generalization

Halász's theorem generalizes to vector sums in d dimensions,
giving a bound of 2^N / N^((d+1)/2).
-/

/-- Vector-valued subset sum -/
def vectorSetSum {d : ℕ} (A : Finset (Fin d → ℤ)) : Fin d → ℤ :=
  fun i => ∑ v ∈ A, v i

/-- Count of subsets with fixed vector sum -/
def countVectorSubsetsWithSum {d : ℕ} (A : Finset (Fin d → ℤ))
    (t : Fin d → ℤ) : ℕ :=
  (A.powerset.filter (fun S => vectorSetSum S = t)).card

/-- Halász multi-dimensional bound: generalizes to d dimensions.
    The exponent (d+1)/2 specializes to 3/2 for d=2 and 2 for d=3. -/
/-
## Part 6: Generating Function Approach

The Sárközy-Szemerédi proof uses Fourier analysis / generating functions.
The generating function for subset sums factors as a product, and
the concentration bound follows from saddle point analysis.
-/

/-- The generating function for subset sums.
    For z ≠ 0, the coefficient of z^t in this product equals countSubsetsWithSum A t.
    Uses zpow (integer exponentiation) since elements of A may be negative. -/
noncomputable def subsetSumGF (A : Finset ℤ) (z : ℂ) : ℂ :=
  ∏ a ∈ A, (1 + z ^ a)

/-- zpow distributes over finset sum (for nonzero base).
    Proved via induction on the finset using zpow_add₀. -/
theorem zpow_finset_sum (S : Finset ℤ) (z : ℂ) (hz : z ≠ 0) :
    ∏ a ∈ S, z ^ a = z ^ (∑ a ∈ S, a) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [prod_cons, sum_cons, zpow_add₀ hz, ih]

/-- GF at z=1 equals 2^|A| (counts all subsets). -/
theorem gf_at_one (A : Finset ℤ) :
    subsetSumGF A 1 = (2 : ℂ) ^ A.card := by
  unfold subsetSumGF
  have h : ∀ a ∈ A, (1 : ℂ) + (1 : ℂ) ^ a = 2 := by
    intros a _; simp [one_zpow]; norm_num
  rw [prod_congr rfl h, prod_const]

/-- Product expansion of GF as sum over powerset.
    Key identity: ∏ (1 + z^a) = ∑_{S ⊆ A} z^{setSum S}.
    Uses Finset.prod_one_add to expand the product, then zpow_finset_sum
    to convert ∏ z^a to z^(∑ a). -/
theorem gf_expansion (A : Finset ℤ) (z : ℂ) (hz : z ≠ 0) :
    subsetSumGF A z = ∑ S ∈ A.powerset, z ^ (setSum S) := by
  simp only [subsetSumGF, setSum]
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun S _ => zpow_finset_sum S z hz

/-- GF factors over disjoint union. -/
theorem gf_disjoint_union (B C : Finset ℤ) (z : ℂ) (h : Disjoint B C) :
    subsetSumGF (B ∪ C) z = subsetSumGF B z * subsetSumGF C z := by
  unfold subsetSumGF
  exact prod_union h

/-
## Proof roadmap for fourier_extraction (below)

Using gf_expansion (proved above), the proof reduces to:
1. subsetSumGF A (e^{iθ}) = ∑ S ∈ A.powerset, e^{i·setSum(S)·θ} (by gf_expansion, since e^{iθ} ≠ 0)
2. Multiply by e^{-itθ} and integrate: each term gives (1/2π)∫₀²π e^{i(setSum S-t)θ} dθ
3. Orthogonality: this integral equals 1 if setSum S = t, 0 otherwise
4. Sum collapses to #{S ⊆ A : setSum S = t} = countSubsetsWithSum A t

Step 3 needs: for n : ℤ, (1/2π)∫₀²π e^{inθ} dθ = if n = 0 then 1 else 0
- n = 0: ∫₀²π 1 dθ = 2π, so (1/2π)·2π = 1
- n ≠ 0: FTC with antiderivative e^{inθ}/(in), giving (e^{2πin}-1)/(in) = 0

Alternatively, use Mathlib's AddCircle/fourierCoeff infrastructure:
- Express f(θ) = subsetSumGF A (e^{iθ}) as ∑_{S} fourier(setSum S)(θ) on AddCircle(2π)
- Apply fourierCoeff linearity + orthonormal_fourier
- Bridge set_integral on Icc to intervalIntegral / Haar measure
-/

/-- Fourier coefficient extraction: countSubsetsWithSum equals
    the integral of the generating function against an exponential. -/
axiom fourier_extraction (A : Finset ℤ) (t : ℤ) :
    (countSubsetsWithSum A t : ℂ) =
      (1 : ℂ) / (2 * Real.pi) * ∫ θ in Set.Icc 0 (2 * Real.pi),
        subsetSumGF A (Complex.exp (Complex.I * θ)) * Complex.exp (-Complex.I * t * θ)

/-
## Part 7: Summary

Erdős Problem #362 asks about concentration of subset sums.
Both questions were answered affirmatively.
-/

/-- Main summary of Erdős Problem #362.
    Q1: #{S ⊆ A : sum(S) = t} ≪ 2^N / N^(3/2) (Sárközy-Szemerédi 1965)
    Q2: #{S ⊆ A : sum(S) = t, |S| = l} ≪ 2^N / N² (Halász 1977) -/
theorem erdos_362_summary :
    (∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ)) ∧
    (∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, ∀ l : ℕ, (countSubsetsWithSumAndCard A t l : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^2) := by
  exact ⟨sarkozy_szemeredi_1965, halasz_1977⟩

/-- The number of subsets summing to any fixed target is at most 2^|A|. -/
theorem subset_count_le_pow (A : Finset ℤ) (t : ℤ) :
    countSubsetsWithSum A t ≤ 2 ^ A.card := by
  unfold countSubsetsWithSum subsetsWithSum
  calc (A.powerset.filter fun S => setSum S = t).card
      ≤ A.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ A.card := Finset.card_powerset A

end Erdos362
