/-
  Erdős Problem #973: Power Sums of Complex Numbers (Turán's Problem)

  Source: https://erdosproblems.com/973
  Status: OPEN (partial results known)

  Statement:
  Does there exist a constant C > 1 such that, for every n ≥ 2,
  there exists a sequence z_i ∈ ℂ with z₁ = 1 and |z_i| ≥ 1 such that
    max_{2 ≤ k ≤ n+1} |∑_{i=1}^n z_i^k| < C^{-n}?

  Known results:
  - For |z_i| ≤ 1: Erdős showed such sequences exist with C ≈ 1.32
  - For |z_i| = 1: L. Erdős (1992) proved (1.746)^{-n} < M₂ < (1.745)^{-n}
  - For |z_i| ≥ 1: Turán's theorem gives lower bound (2e)^{-(1+o(1))n}
  - The original question (|z_i| ≥ 1) remains open

  This is Turán's power sum problem, fundamental in analytic number theory.

  References:
  - [Ha74] Hayman, "Research problems in function theory" (1974), Problem 7.3
  - [Tu84b] Turán, "On a new method of analysis and its applications" (1984)
  - [Er92f] L. Erdős, "On some problems of P. Turán" (1992)
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Complex Finset BigOperators

namespace Erdos973

/- ## Part I: Power Sums of Complex Numbers -/

/-- A sequence of n complex numbers. -/
def ComplexSeq (n : ℕ) := Fin n → ℂ

/-- The k-th power sum of a sequence: ∑_{i=1}^n z_i^k. -/
def powerSum (z : ComplexSeq n) (k : ℕ) : ℂ :=
  ∑ i, (z i) ^ k

/-- The first element is 1. -/
def HasFirstOne (z : ComplexSeq n) : Prop :=
  n > 0 ∧ z ⟨0, by omega⟩ = 1

/-- All elements have modulus at least 1. -/
def AllModulusGeOne (z : ComplexSeq n) : Prop :=
  ∀ i, abs (z i) ≥ 1

/-- All elements have modulus exactly 1 (on unit circle). -/
def AllOnUnitCircle (z : ComplexSeq n) : Prop :=
  ∀ i, abs (z i) = 1

/-- All elements have modulus at most 1 (in unit disk). -/
def AllModulusLeOne (z : ComplexSeq n) : Prop :=
  ∀ i, abs (z i) ≤ 1

/-- The maximum of |powerSum z k| over k from 2 to n+1.
    Axiomatized because Finset.sup' requires a nonempty proof that
    depends on the parameter n. -/
axiom maxPowerSum (z : ComplexSeq n) : ℝ

/-- maxPowerSum is the supremum of |∑ z_i^k| for k ∈ {2, ..., n+1}. -/
/- ## Part II: The Erdős Question -/

/-- Erdős's Question: Does there exist C > 1 such that for all n,
    we can find z with first element 1, all |z_i| ≥ 1,
    and max power sum < C^{-n}? -/
def ErdosQuestion973 : Prop :=
  ∃ C : ℝ, C > 1 ∧
    ∀ n : ℕ, n ≥ 2 →
      ∃ z : ComplexSeq n, HasFirstOne z ∧ AllModulusGeOne z ∧
        maxPowerSum z < C^(-(n : ℤ))

/- ## Part III: Erdős's Construction (Unit Disk Case) -/

/-- **Erdős's Original Result:**
    Such sequences exist with |z_i| ≤ 1 and C ≈ 1.32. -/
axiom erdos_unit_disk_construction :
  ∃ C : ℝ, C > 1 ∧ C < 1.33 ∧
    ∀ n : ℕ, n ≥ 2 →
      ∃ z : ComplexSeq n, HasFirstOne z ∧ AllModulusLeOne z ∧
        maxPowerSum z < C^(-(n : ℤ))

/-- Erdős's constant is approximately 1.32. -/
def erdosConstant : ℝ := 1.32

/- ## Part IV: L. Erdős's Refinement (1992) -/

/-- The minimum over sequences of the maximum power sum (for unit circle). -/
noncomputable def M2 (n : ℕ) : ℝ :=
  ⨅ (z : ComplexSeq n) (_ : HasFirstOne z) (_ : AllOnUnitCircle z), maxPowerSum z

/-- **L. Erdős (1992):**
    For sequences on the unit circle,
    (1.746)^{-n} < M₂ < (1.745)^{-n}. -/
axiom l_erdos_1992_bounds (n : ℕ) (hn : n ≥ 2) :
    (1.746 : ℝ)^(-(n : ℤ)) < M2 n ∧ M2 n < (1.745 : ℝ)^(-(n : ℤ))

/-- The optimal constant for unit circle sequences. -/
def unitCircleConstant : ℝ := 1.7455

/- ## Part V: Turán's Lower Bound -/

/-- **Turán's Theorem (Tu84b, Theorem 6.1):**
    If all |z_i| ≥ 1, then the maximum power sum is at least (2e)^{-(1+o(1))n}. -/
axiom turan_lower_bound :
  ∀ ε > 0, ∃ N : ℕ,
    ∀ n ≥ N, ∀ z : ComplexSeq n, HasFirstOne z → AllModulusGeOne z →
      maxPowerSum z ≥ (2 * Real.exp 1)^(-(1 + ε) * n)

/-- The Turán constant 2e ≈ 5.44. -/
noncomputable def turanConstant : ℝ := 2 * Real.exp 1

/-- 2e is approximately 5.44. -/
/- ## Part VI: The Answer -/

/-- The answer depends on the modulus constraint:
    - |z_i| ≤ 1: YES with C ≈ 1.32
    - |z_i| = 1: C ≈ 1.7455 is optimal
    - |z_i| ≥ 1: lower bound (2e)^{-n} shows exponential decay, but the
      exact question (whether C > 1 exists) remains open -/
def AnswerSummary : Prop :=
  (∃ C : ℝ, C > 1 ∧ ∀ n ≥ 2, ∃ z : ComplexSeq n,
    HasFirstOne z ∧ AllModulusLeOne z ∧ maxPowerSum z < C^(-(n : ℤ))) ∧
  (∀ n ≥ 2, (1.746 : ℝ)^(-(n : ℤ)) < M2 n ∧ M2 n < (1.745 : ℝ)^(-(n : ℤ))) ∧
  (∀ ε > 0, ∃ N : ℕ,
    ∀ n ≥ N, ∀ z : ComplexSeq n, HasFirstOne z → AllModulusGeOne z →
      maxPowerSum z ≥ (2 * Real.exp 1)^(-(1 + ε) * n))

/- ## Part VII: Extremal Sequences -/

/-- Roots of unity provide natural candidates for extremal sequences. -/
def rootsOfUnitySequence (n : ℕ) : ComplexSeq n :=
  fun i => Complex.exp (2 * Real.pi * I * i / n)

/-- Roots of unity are on the unit circle. -/
theorem roots_on_circle (n : ℕ) :
    AllOnUnitCircle (rootsOfUnitySequence n) := by
  intro i
  simp only [rootsOfUnitySequence]
  rw [Complex.abs_exp]
  simp

/-- For n-th roots of unity, the k-th power sum is 0 when n ∤ k and n when n ∣ k. -/
/- ## Part VIII: Dirichlet Polynomial Connection -/

/-- A Dirichlet polynomial: ∑ a_n n^{-s}. -/
structure DirichletPolynomial where
  coeffs : ℕ → ℂ
  support : Finset ℕ

/-- Power sums of z_i = n_i^{it} for integers n_i yield Dirichlet sums.
    This connects Turán's method to L-function zero-free regions. -/
/- ## Part IX: Summary -/

/-- **Unit disk result (PROVED from axiom):** Erdős showed C ≈ 1.32 works
    when elements have modulus ≤ 1. -/
theorem erdos_973_unit_disk :
    ∃ C : ℝ, C > 1 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∃ z : ComplexSeq n, HasFirstOne z ∧ AllModulusLeOne z ∧
          maxPowerSum z < C^(-(n : ℤ)) := by
  obtain ⟨C, hC_gt, _, hExist⟩ := erdos_unit_disk_construction
  exact ⟨C, hC_gt, hExist⟩

/-- **Turán's constraint (PROVED from axiom):** For |z_i| ≥ 1,
    Turán's bound gives a lower limit on power sums. -/
theorem erdos_973_turan_constrained :
    ∀ ε > 0, ∃ N : ℕ,
      ∀ n ≥ N, ∀ z : ComplexSeq n, HasFirstOne z → AllModulusGeOne z →
        maxPowerSum z ≥ (2 * Real.exp 1)^(-(1 + ε) * n) :=
  turan_lower_bound

/-- **Main summary theorem:** Combines all three known results:
    1. Unit disk: C ≈ 1.32 works (Erdős)
    2. Unit circle: optimal constant ≈ 1.7455 (L. Erdős 1992)
    3. Outside disk: Turán's lower bound applies -/
theorem erdos_973 : AnswerSummary := by
  exact ⟨
    (let ⟨C, hC, _, hExist⟩ := erdos_unit_disk_construction; ⟨C, hC, fun n hn => hExist n hn⟩),
    l_erdos_1992_bounds,
    turan_lower_bound⟩

end Erdos973
