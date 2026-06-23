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

/-
## Part I: Basic Definitions

Sequences of integers and fractional parts.
-/

/-- An infinite strictly increasing sequence of positive integers -/
def StrictlyIncreasingSeq (x : ℕ → ℕ) : Prop :=
  ∀ n, x n < x (n + 1)

/-- The fractional part {t} of a real number -/
noncomputable def frac (t : ℝ) : ℝ := t - ⌊t⌋

/-- Fractional part is in [0, 1) -/
theorem frac_in_unit_interval (t : ℝ) : 0 ≤ frac t ∧ frac t < 1 := by
  unfold frac
  constructor <;> linarith [Int.floor_le t, Int.lt_floor_add_one t]

/-
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
  sSup { |↑(countInInterval x α N a b) - (b - a) * N| |
         (a : ℝ) (b : ℝ) (_ : 0 ≤ a) (_ : a ≤ b) (_ : b ≤ 1) }

/-
## Part III: Known Bounds
-/

/-- Erdős-Koksma (1949) and Cassels (1950): D(N) ≪ N^{1/2}(log N)^{5/2+o(1)} -/
/-- Baker (1981): D(N) ≪ N^{1/2}(log N)^{3/2+o(1)} — current best general bound -/
axiom baker_1981 (x : ℕ → ℕ) (hx : StrictlyIncreasingSeq x) :
    ∃ C : ℝ, C > 0 ∧
    ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
      ∀ N : ℕ, N ≥ 2 →
        discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ (3/2 : ℝ)

/-
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

/-
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

/-
## Part VI: Lower Bounds
-/

/-- Lower bound: D(N) ≫ N^{1/2} infinitely often for some α -/
/-
## Part VII: Examples
-/

/-- Example: x_n = n (natural numbers) -/
def naturalSeq : ℕ → ℕ := id

theorem natural_seq_strictly_increasing : StrictlyIncreasingSeq naturalSeq := by
  intro n; simp [naturalSeq]; omega

/-- Example: x_n = 2^n (powers of 2, lacunary with λ = 2) -/
def powersOfTwo (n : ℕ) : ℕ := 2 ^ n

/-- Powers of 2 satisfy the stronger loglog bound -/
/-
## Part VIII: Summary
-/

/-- **Summary of Erdős Problem #992:**
    Combines the two main known results:
    1. Baker's bound (1981): D(N) ≪ √N · (log N)^{3/2} for all sequences (current best)
    2. Erdős-Gál: D(N) ≪ √N · (log log N)^{O(1)} for lacunary sequences -/
theorem erdos_992_summary :
    (∀ x : ℕ → ℕ, StrictlyIncreasingSeq x →
      ∃ C : ℝ, C > 0 ∧
      ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
        ∀ N : ℕ, N ≥ 2 →
          discrepancy x α N ≤ C * Real.sqrt N * (Real.log N) ^ (3/2 : ℝ)) ∧
    (∀ x : ℕ → ℕ, ∀ λ : ℝ, Lacunary x λ →
      ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
      ∀ᵐ α ∂volume.restrict (Set.Icc 0 1),
        ∀ N : ℕ, N ≥ 3 →
          discrepancy x α N ≤ C * Real.sqrt N * (Real.log (Real.log N)) ^ k) :=
  ⟨fun x hx => baker_1981 x hx, fun x λ hλ => erdos_gal_lacunary x λ hλ⟩

end Erdos992
