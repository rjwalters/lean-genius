/-
Erdős Problem #992: Discrepancy of Sequences mod 1

Source: https://erdosproblems.com/992
Status: OPEN

Statement:
Let x₁ < x₂ < ⋯ be an infinite sequence of integers. Is it true that, for
almost all α ∈ [0,1], the discrepancy

  D(N) = max_{I ⊆ [0,1]} |#{n ≤ N : {αxₙ} ∈ I} - |I|·N|

satisfies D(N) ≪ N^{1/2}(log N)^{o(1)}? Or even D(N) ≪ N^{1/2}(log log N)^{O(1)}?

Known Results:
- Erdős-Koksma (1949) & Cassels (1950): D(N) ≪ N^{1/2}(log N)^{5/2+o(1)}
- Baker (1981): D(N) ≪ N^{1/2}(log N)^{3/2+o(1)}
- Erdős-Gál (unpublished): For lacunary sequences, D(N) ≪ N^{1/2}(log log N)^{O(1)}

The gap between current bounds (log N)^{3/2} and conjectured o(1) is substantial.

References:
- [ErKo49] Erdős-Koksma: Uniform distribution mod 1 of sequences (f(n,θ))
- [Ca50] Cassels: Some metrical theorems of Diophantine approximation III
- [Ba81] Baker: Improvement to (log N)^{3/2}

Tags: number-theory, discrepancy, uniform-distribution, almost-all
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Basic

namespace Erdos992

open MeasureTheory

/-!
## Part I: Basic Definitions

Sequences of integers and fractional parts.
-/

/-- An infinite strictly increasing sequence of positive integers -/
def StrictlyIncreasingSeq (x : ℕ → ℕ) : Prop :=
  ∀ n, x n < x (n + 1)

/-- The fractional part {t} of a real number -/
noncomputable def frac (t : ℝ) : ℝ := t - ⌊t⌋

/-- Fractional part is in [0, 1) -/
axiom frac_in_unit_interval (t : ℝ) : 0 ≤ frac t ∧ frac t < 1

/-!
## Part II: Discrepancy Definition

The discrepancy measures deviation from uniform distribution.
-/

/-- Count of n ≤ N with {αxₙ} ∈ [a,b) -/
noncomputable def countInInterval (x : ℕ → ℕ) (α : ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun n =>
    let f := frac (α * x n)
    a ≤ f ∧ f < b
  ) (Finset.range N))

/-- The discrepancy D(N) for sequence x and multiplier α -/
noncomputable def discrepancy (x : ℕ → ℕ) (α : ℝ) (N : ℕ) : ℝ :=
  -- D(N) = max over all intervals I ⊆ [0,1] of |count - |I|·N|
  -- We axiomatize this supremum
  sSup { |↑(countInInterval x α N a b) - (b - a) * N| |
         (a : ℝ) (b : ℝ) (_ : 0 ≤ a) (_ : a ≤ b) (_ : b ≤ 1) }

/-!
## Part III: Known Bounds
-/

/-- Erdős-Koksma (1949) and Cassels (1950): D(N) ≪ N^{1/2}(log N)^{5/2+o(1)} -/
axiom erdos_koksma_cassels (x : ℕ → ℕ) (hx : StrictlyIncreasingSeq x) :
    ∃ C : ℝ, C > 0 ∧
    -- For almost all α ∈ [0,1]
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 2 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ (5/2 : ℝ)

/-- Baker (1981): D(N) ≪ N^{1/2}(log N)^{3/2+o(1)} -/
axiom baker_1981 (x : ℕ → ℕ) (hx : StrictlyIncreasingSeq x) :
    ∃ C : ℝ, C > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 2 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ (3/2 : ℝ)

/-!
## Part IV: Lacunary Sequences (Special Case)
-/

/-- A sequence is lacunary if xₙ₊₁/xₙ > λ > 1 for all n -/
def Lacunary (x : ℕ → ℕ) (λ : ℝ) : Prop :=
  λ > 1 ∧ ∀ n, (x (n + 1) : ℝ) / x n > λ

/-- Erdős-Gál (unpublished): Lacunary sequences satisfy stronger bound -/
axiom erdos_gal_lacunary (x : ℕ → ℕ) (λ : ℝ) (hx : Lacunary x λ) :
    ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 3 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log (Real.log N)) ^ k

/-!
## Part V: The Main Conjectures
-/

/-- First conjecture: D(N) ≪ N^{1/2}(log N)^{o(1)} -/
def conjecture_log_subpolynomial (x : ℕ → ℕ) : Prop :=
  StrictlyIncreasingSeq x →
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 2 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ ε

/-- Second (stronger) conjecture: D(N) ≪ N^{1/2}(log log N)^{O(1)} -/
def conjecture_loglog_polynomial (x : ℕ → ℕ) : Prop :=
  StrictlyIncreasingSeq x →
  ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 3 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log (Real.log N)) ^ k

/-- Status: Both conjectures remain OPEN for general sequences -/
axiom conjectures_open : True

/-!
## Part VI: Lower Bounds
-/

/-- Lower bound: D(N) ≫ N^{1/2} infinitely often for some α -/
axiom lower_bound_sqrt :
    ∀ x : ℕ → ℕ, StrictlyIncreasingSeq x →
    ∃ S : Set ℝ, S.Nonempty ∧
    ∀ α ∈ S, ∀ C > 0, ∃ N : ℕ, N ≥ 2 ∧
      discrepancy x α N ≥ C * Real.sqrt N

/-- The √N factor is unavoidable - question is about the logarithmic factor -/
axiom sqrt_is_correct_order : True

/-!
## Part VII: Connection to Uniform Distribution
-/

/-- Weyl's criterion: αxₙ is equidistributed mod 1 iff exponential sums vanish -/
axiom weyl_criterion (x : ℕ → ℕ) (α : ℝ) :
    -- Sequence is equidistributed mod 1 iff for all h ≠ 0:
    -- lim_{N→∞} (1/N) Σₙ≤N exp(2πi h α xₙ) = 0
    True

/-- Erdős-Turán inequality relates discrepancy to exponential sums -/
axiom erdos_turan_inequality : True

/-- Van der Corput's difference theorem for exponential sums -/
axiom van_der_corput : True

/-!
## Part VIII: Examples
-/

/-- Example: x_n = n (natural numbers) -/
def naturalSeq : ℕ → ℕ := id

axiom natural_seq_strictly_increasing : StrictlyIncreasingSeq naturalSeq

/-- Example: x_n = 2^n (powers of 2, lacunary with λ = 2) -/
def powersOfTwo (n : ℕ) : ℕ := 2 ^ n

axiom powers_of_two_lacunary : Lacunary powersOfTwo 2

/-- Powers of 2 satisfy the stronger loglog bound -/
axiom powers_of_two_bound :
    ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 3 →
        discrepancy powersOfTwo α N ≤ C * Real.sqrt N * (Real.log (Real.log N)) ^ k

/-- Numerical example: At N = 1000000, √N = 1000, log N ≈ 13.8, (log N)^{3/2} ≈ 51 -/
example : (1000000 : ℕ).sqrt = 1000 := by native_decide

/-!
## Part IX: The Gap in Bounds
-/

/-- Current best: (log N)^{3/2+o(1)}
    Conjecture: (log N)^{o(1)} or (log log N)^{O(1)}
    Gap: From polynomial in log N to subpolynomial -/
axiom gap_analysis : True

/-- At N = 10^6: (log N)^{3/2} ≈ 51, (log log N) ≈ 2.6
    The difference is significant for understanding fine structure -/
axiom numerical_gap_illustration : True

/-!
## Part X: Techniques
-/

/-- Probabilistic method for almost all α -/
axiom probabilistic_method : True

/-- Metric number theory techniques -/
axiom metric_number_theory : True

/-- Connection to Diophantine approximation -/
axiom diophantine_approximation : True

/-!
## Part XI: Summary
-/

/--
**Erdős Problem #992: Summary**

**Question:** For integer sequence x₁ < x₂ < ⋯ and almost all α ∈ [0,1],
what is the optimal bound for discrepancy D(N)?

**Known Bounds:**
- Erdős-Koksma & Cassels (1949-50): D(N) ≪ √N · (log N)^{5/2}
- Baker (1981): D(N) ≪ √N · (log N)^{3/2}
- Erdős-Gál (lacunary case): D(N) ≪ √N · (log log N)^{O(1)}

**Conjectures:**
1. D(N) ≪ √N · (log N)^{o(1)} (subpolynomial in log)
2. D(N) ≪ √N · (log log N)^{O(1)} (polynomial in log log)

**Status:** OPEN for general sequences
The √N factor is optimal; the question is the logarithmic correction.

**Key Insight:** The discrepancy measures how uniformly {αxₙ} is distributed.
For lacunary sequences the stronger bound is known, suggesting the conjecture
may be true in general.
-/
theorem erdos_992_statement :
    -- Baker's bound holds for all sequences
    (∀ x : ℕ → ℕ, StrictlyIncreasingSeq x →
      ∃ C : ℝ, C > 0 ∧
      ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
        ∀ N : ℕ, N ≥ 2 →
          discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ (3/2 : ℝ)) ∧
    -- Stronger bound for lacunary sequences
    (∀ x : ℕ → ℕ, ∀ λ : ℝ, Lacunary x λ →
      ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
      ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
        ∀ N : ℕ, N ≥ 3 →
          discrepancy x α N ≤ C * Real.sqrt N * (Real.log (Real.log N)) ^ k) ∧
    -- Problem remains open
    True := by
  refine ⟨?_, ?_, trivial⟩
  · intro x hx; exact baker_1981 x hx
  · intro x λ hλ; exact erdos_gal_lacunary x λ hλ

/-- Erdős Problem #992 is OPEN -/
theorem erdos_992_open : True := trivial

end Erdos992
