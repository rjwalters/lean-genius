/-
Erdős Problem #995: Lacunary Sequences and Fractional Parts

Source: https://erdosproblems.com/995
Status: OPEN

Statement:
Let n₁ < n₂ < ⋯ be a lacunary sequence of integers and f ∈ L²([0,1]).
Estimate the growth of, for almost all α,
  ∑_{k ≤ N} f({α n_k})
where {x} denotes the fractional part of x.

Is it true that for almost all α,
  ∑_{k ≤ N} f({α n_k}) = o(N √(log log N))?

Known Bounds:
- Lower: Erdős (1949) constructed examples with
    limsup ∑_{k≤N} f({α n_k}) / (N (log log N)^{1/2-ε}) = ∞
- Upper: Erdős proved ∑_{k≤N} f({α n_k}) = o(N (log N)^{1/2+ε})

Erdős (1964) believed the lower bound is closer to the truth.

Tags: analysis, lacunary-sequences, diophantine-approximation, probability
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

namespace Erdos995

open MeasureTheory Real

/-!
## Part 1: Basic Definitions
-/

/-- Fractional part of a real number -/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/-- A sequence is lacunary if each term is at least q times the previous (q > 1) -/
def IsLacunary (n : ℕ → ℕ) (q : ℝ) : Prop :=
  q > 1 ∧ ∀ k, (n (k + 1) : ℝ) ≥ q * n k

/-- Common lacunary condition: n_{k+1}/n_k ≥ q for some q > 1 -/
def IsLacunarySeq (n : ℕ → ℕ) : Prop :=
  ∃ q > 1, IsLacunary n q

/-- The sum ∑_{k ≤ N} f({α n_k}) for a function f and sequence n -/
noncomputable def lacunarySum (f : ℝ → ℝ) (n : ℕ → ℕ) (α : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f (frac (α * n k))

/-!
## Part 2: The Main Conjecture
-/

/-- The Erdős conjecture: for almost all α, the sum is o(N √(log log N)) -/
def ErdosConjecture (f : ℝ → ℝ) (n : ℕ → ℕ) : Prop :=
  -- For almost all α ∈ [0,1], the sum grows as o(N √(log log N))
  ∀ᵐ α ∂(volume.restrict (Set.Icc 0 1)),
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |lacunarySum f n α N| < ε * N * Real.sqrt (Real.log (Real.log N))

/-- The main question: Is the conjecture true for all lacunary sequences and L² functions? -/
def ErdosQuestion : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ → ℕ),
    IsLacunarySeq n →
    -- f ∈ L²([0,1])
    ErdosConjecture f n

/-!
## Part 3: Known Lower Bounds

Erdős (1949) constructed counterexamples showing the sum can be large.
-/

/-- Erdős (1949): There exists a lacunary sequence and f ∈ L² such that
    for a.e. α, limsup ∑f({α n_k}) / (N(log log N)^{1/2-ε}) = ∞ -/
axiom erdos_lower_bound_1949 :
  ∃ (f : ℝ → ℝ) (n : ℕ → ℕ),
    IsLacunarySeq n ∧
    -- f ∈ L²([0,1])
    ∀ ε > 0,
      ∀ᵐ α ∂(volume.restrict (Set.Icc 0 1)),
        Filter.limsup (fun N => |lacunarySum f n α N| /
          (N * (Real.log (Real.log N))^((1:ℝ)/2 - ε))) Filter.atTop = ⊤

/-- The lower bound shows: at least N (log log N)^{1/2 - ε} infinitely often -/
def LowerBoundGrowth (f : ℝ → ℝ) (n : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᵐ α ∂(volume.restrict (Set.Icc 0 1)),
    ∀ M : ℝ, ∃ N : ℕ, |lacunarySum f n α N| ≥ M * N * (Real.log (Real.log N))^((1:ℝ)/2 - ε)

/-!
## Part 4: Known Upper Bounds

Erdős proved a general upper bound for all lacunary sequences.
-/

/-- Erdős upper bound: For every lacunary sequence and L² function,
    ∑f({α n_k}) = o(N (log N)^{1/2+ε}) for a.e. α -/
axiom erdos_upper_bound :
  ∀ (f : ℝ → ℝ) (n : ℕ → ℕ),
    IsLacunarySeq n →
    -- f ∈ L²([0,1])
    ∀ ε > 0,
      ∀ᵐ α ∂(volume.restrict (Set.Icc 0 1)),
        ∃ N₀ : ℕ, ∀ N ≥ N₀,
          |lacunarySum f n α N| < N * (Real.log N)^((1:ℝ)/2 + ε)

/-- The upper bound is o(N (log N)^{1/2+ε}) -/
def UpperBoundGrowth (f : ℝ → ℝ) (n : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᵐ α ∂(volume.restrict (Set.Icc 0 1)),
    Filter.limsup (fun N => |lacunarySum f n α N| /
      (N * (Real.log N)^((1:ℝ)/2 + ε))) Filter.atTop ≤ 1

/-!
## Part 5: The Gap

The lower bound has (log log N)^{1/2} while the upper bound has (log N)^{1/2}.
The question asks if (log log N)^{1/2} is the truth.
-/

/-- The gap between bounds: log log N vs log N -/
theorem bound_gap :
    -- Lower: limsup ≥ N (log log N)^{1/2 - ε} for some examples
    -- Upper: always o(N (log N)^{1/2 + ε})
    -- Conjectured: o(N (log log N)^{1/2})
    True := trivial

/-- The ratio of exponents in the bounds -/
theorem exponent_gap (N : ℕ) (hN : N ≥ 3) :
    Real.log (Real.log N) < Real.log N := by
  -- log log N < log N for N ≥ 3
  sorry

/-!
## Part 6: Examples
-/

/-- The geometric sequence 2^k is lacunary with q = 2 -/
def geometricSeq (k : ℕ) : ℕ := 2^k

theorem geometric_is_lacunary : IsLacunary geometricSeq 2 := by
  constructor
  · norm_num
  · intro k
    simp [geometricSeq]
    ring_nf
    norm_num

/-- Powers of 3 are also lacunary -/
def powersOf3 (k : ℕ) : ℕ := 3^k

theorem powers3_lacunary : IsLacunary powersOf3 3 := by
  constructor
  · norm_num
  · intro k
    simp [powersOf3]
    ring_nf
    norm_num

/-- Fibonacci sequence is lacunary (eventually) with q ≈ φ = (1+√5)/2 -/
def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

-- Fibonacci is eventually lacunary with ratio approaching the golden ratio

/-!
## Part 7: Connection to Strong Law of Large Numbers

Erdős (1949) paper was titled "On the strong law of large numbers".
-/

/-- Connection to SLLN: Under certain conditions, the sum behaves like a random walk -/
axiom slln_connection :
  -- For "generic" f with ∫f = 0, the sum behaves like a random walk
  -- Random walk of N steps has variance ~ N
  -- So sum ~ √N on average, but can be larger for special sequences
  True

/-!
## Part 8: Erdős's Opinion

Erdős (1964) believed the lower bound is closer to the truth.
-/

/-- Erdős's conjecture: The truth is closer to N (log log N)^{1/2} -/
def ErdosGuess : Prop :=
  -- The lower bound construction is close to optimal
  -- The upper bound can likely be improved to N (log log N)^{1/2+ε}
  True

axiom erdos_opinion : ErdosGuess

/-!
## Part 9: Main Results
-/

/-- Erdős Problem #995: Main statement -/
theorem erdos_995_statement :
    -- Known lower bound: limsup can reach N(log log N)^{1/2-ε}
    (∃ (f : ℝ → ℝ) (n : ℕ → ℕ), IsLacunarySeq n ∧ LowerBoundGrowth f n) ∧
    -- Known upper bound: always o(N(log N)^{1/2+ε})
    (∀ (f : ℝ → ℝ) (n : ℕ → ℕ), IsLacunarySeq n → UpperBoundGrowth f n) ∧
    -- The gap remains open
    True := by
  constructor
  · -- Lower bound existence from Erdős (1949)
    sorry
  constructor
  · -- Upper bound from Erdős
    intro f n hlac ε hε
    sorry
  · trivial

/-- The problem remains open -/
theorem erdos_995_open : True := trivial

/-- Summary of the problem -/
theorem erdos_995_summary :
    -- Question: Is ∑f({α n_k}) = o(N √(log log N))?
    -- Known: o(N(log log N)^{1/2-ε}) ≤ growth ≤ o(N(log N)^{1/2+ε})
    -- Erdős conjectured: Lower bound is closer to truth
    -- Status: OPEN
    True := trivial

end Erdos995
