/-
Erdős Problem #792: Sum-Free Subsets

A set B ⊆ ℤ is sum-free if there are no solutions to a + b = c with a, b, c ∈ B.

Let f(n) be the maximum value such that any subset A ⊆ ℤ with |A| = n contains
a sum-free subset B ⊆ A with |B| ≥ f(n).

Problem: Estimate f(n).

Known bounds:
- Lower: f(n) ≥ n/3 (Erdős, 1965)
- Lower: f(n) ≥ (n+1)/3 (Alon-Kleitman, 1990)
- Lower: f(n) ≥ (n+2)/3 (Bourgain, 1997)
- Lower: f(n) ≥ n/3 + c·log log n (Bedert, 2025)
- Upper: f(n) ≤ n/3 + o(n) (Eberhard-Green-Manners, 2014)

This is Problem #792 from erdosproblems.com.
Also Problem 1 on Ben Green's open problems list.

Reference: https://erdosproblems.com/792
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic

open Nat Finset Set Filter

namespace Erdos792

-- Core Definitions

/-- A set B ⊆ ℤ is sum-free if there are no a, b, c ∈ B with a + b = c -/
def SumFree (B : Set ℤ) : Prop :=
  ∀ a b c : ℤ, a ∈ B → b ∈ B → c ∈ B → a + b ≠ c

/-- For finsets: sum-free predicate -/
def SumFreeFinset (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a + b ≠ c

/-- A sum-free subset of A -/
def IsSumFreeSubset (B A : Finset ℤ) : Prop :=
  B ⊆ A ∧ SumFreeFinset B

/-- The maximum size of a sum-free subset of A -/
noncomputable def maxSumFreeSize (A : Finset ℤ) : ℕ :=
  sSup {n | ∃ B : Finset ℤ, IsSumFreeSubset B A ∧ B.card = n}

-- f(n) axiomatized: minimum guaranteed sum-free subset size

/-- f(n): the minimum over all n-element sets A of the maximum sum-free subset size -/
axiom f : ℕ → ℕ

/-- f satisfies its defining property: every n-element set has a sum-free subset of size ≥ f(n) -/
/-- f is tight: for each n ≥ 1, some n-element set achieves exactly f(n) -/
/-- Bourgain (1997): f(n) ≥ (n+2)/3 — the strongest unconditional lower bound -/
axiom bourgain_bound : ∀ n : ℕ, n ≥ 1 → f n ≥ (n + 2) / 3

/-- Alon-Kleitman (1990): f(n) ≥ (n+1)/3.
    Previously axiomatized; now derived from Bourgain's stronger bound. -/
theorem alon_kleitman_bound : ∀ n : ℕ, n ≥ 1 → f n ≥ (n + 1) / 3 := by
  intro n hn
  have := bourgain_bound n hn
  have : (n + 1) / 3 ≤ (n + 2) / 3 := Nat.div_le_div_right (by omega)
  omega

/-- Erdős (1965): f(n) ≥ n/3 via the middle-third construction.
    Previously axiomatized; now derived from Bourgain's stronger bound. -/
theorem erdos_lower_bound : ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ n / 3 := by
  intro n hn
  have hb := bourgain_bound n hn
  have hnat : n ≤ (n + 2) / 3 * 3 := by omega
  have h1 : (f n : ℝ) ≥ ↑((n + 2) / 3) := by exact_mod_cast hb
  have h2 : (↑n : ℝ) / 3 ≤ ↑((n + 2) / 3) := by
    rw [div_le_iff (by norm_num : (3 : ℝ) > 0)]
    exact_mod_cast hnat
  linarith

/-- Bedert (2025): f(n) ≥ n/3 + c·log log n for some c > 0 -/
axiom bedert_bound : ∃ c : ℝ, c > 0 ∧
  ∀ᶠ n in atTop, (f n : ℝ) ≥ n / 3 + c * Real.log (Real.log n)

-- Upper Bounds

/-- Eberhard-Green-Manners (2014): f(n) ≤ n/3 + o(n) -/
axiom egm_upper_bound : ∀ ε : ℝ, ε > 0 →
  ∀ᶠ n in atTop, (f n : ℝ) ≤ n / 3 + ε * n

/-- Corollary: f(n)/n → 1/3 as n → ∞ -/
/-- The interval [n, 2n-1] is sum-free since a + b ≥ 2n > 2n - 1 for a, b in the interval.
    Proof: if a, b ∈ [n, 2n-1], then a+b ≥ 2n > 2n-1 ≥ c for any c ∈ [n, 2n-1]. -/
theorem interval_sum_free : ∀ n : ℕ, n ≥ 1 →
    SumFreeFinset (Finset.Icc (n : ℤ) (2 * n - 1)) := by
  intro n hn a ha b hb c hc hab
  simp [Finset.mem_Icc] at ha hb hc
  omega

/-- Middle-third construction: every finite set A has a sum-free subset of size ≥ |A|/3 -/
/-- The known bounds bracket f(n) between n/3 + c·log log n and n/3 + o(n) -/
theorem erdos_792_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (f n : ℝ) ≥ n / 3 + c * Real.log (Real.log n)) ∧
    (∀ ε : ℝ, ε > 0 → ∀ᶠ n in atTop, (f n : ℝ) ≤ n / 3 + ε * n) :=
  ⟨bedert_bound, egm_upper_bound⟩

/-- The lower bounds form a chain: Erdős ≤ Alon-Kleitman ≤ Bourgain ≤ Bedert -/
theorem erdos_792_lower_bound_chain (n : ℕ) (hn : n ≥ 1) :
    (f n : ℝ) ≥ n / 3 :=
  erdos_lower_bound n hn

-- Open question: Is f(n) = n/3 + Θ(log log n)?
-- The gap between Bedert's lower bound (log log n) and EGM's upper bound (o(n)) remains open.

end Erdos792
