/- Erdős Problem #404: Prime Power Divisibility of Factorial Sums

Source: https://erdosproblems.com/404
Status: OPEN

Statement:
For which integers a ≥ 1 and primes p is there a finite upper bound on those k
such that there exist a = a₁ < a₂ < ··· < aₙ with p^k | (a₁! + a₂! + ··· + aₙ!)?

Let f(a, p) denote the greatest such k if it exists. How does f(a, p) behave?

Known results:
- Lin (1976): f(2, 2) ≤ 254

Tags: number-theory, p-adic-valuation, factorials, divisibility, open-problem
-/

import Mathlib

open Nat Finset Filter

namespace Erdos404

/- ## Part I: Core Definitions -/

structure StrictIncSeq (a : ℕ) where
  length : ℕ
  seq : Fin length → ℕ
  starts_at_a : length > 0 → seq ⟨0, by omega⟩ = a
  strictly_increasing : ∀ i j : Fin length, i < j → seq i < seq j

noncomputable def factorialSum (s : StrictIncSeq a) : ℕ :=
  ∑ i : Fin s.length, (s.seq i).factorial

def dividesByPrimePower (a k : ℕ) (p : ℕ) : Prop :=
  ∃ s : StrictIncSeq a, p^k ∣ factorialSum s

def divisiblePowers (a : ℕ) (p : ℕ) : Set ℕ :=
  {k | dividesByPrimePower a k p}

noncomputable def f (a : ℕ) (p : ℕ) : ℕ :=
  sSup (divisiblePowers a p)

/- ## Part II: Main Questions -/

def secondaryQuestion : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k+1), (seq i).factorial)) atTop atTop

def erdos404Conjecture : Prop :=
  ∀ a : ℕ, a ≥ 1 → ∀ p : ℕ, p.Prime → ∃ B : ℕ, f a p ≤ B

/- ## Part III: Known Results -/

axiom lin_bound : f 2 2 ≤ 254
axiom lin_bound_meaning : ∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)

/- ## Part IV: p-adic Analysis -/

noncomputable def legendreSum (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log p n + 1), n / p^(i+1)

/-- Legendre's formula: ν_p(n!) = ∑_{i=1}^{⌊log_p n⌋+1} ⌊n/p^i⌋.
    Proved from Mathlib's padicValNat_factorial by reindexing. -/
theorem legendre_formula (n p : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    padicValNat p n.factorial = legendreSum n p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (show Nat.log p n < Nat.log p n + 2 by omega),
      Finset.sum_Ico_eq_sum_range]
  unfold legendreSum
  have h1 : Nat.log p n + 2 - 1 = Nat.log p n + 1 := by omega
  rw [h1]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

/-- ν_p(n!)/n → 1/(p-1) as n → ∞.
    Proof: By Legendre's formula, ν_p(n!) = ∑_{k=1}^{L} ⌊n/p^k⌋ where L = ⌊log_p n⌋ + 1.
    Upper bound: ⌊n/p^k⌋ ≤ n/p^k, so ν_p(n!)/n ≤ ∑ 1/p^k = 1/(p-1).
    Lower bound: ⌊n/p^k⌋ ≥ n/p^k - 1, so ν_p(n!)/n ≥ 1/(p-1) - L/n - 1/(p^L(p-1)).
    Since L = O(log n), both L/n → 0 and 1/p^L → 0. Squeeze gives the result. -/
theorem padic_val_factorial_asymp (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n => (padicValNat p n.factorial : ℝ) / n) atTop (nhds (1/(p-1))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp_one_lt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp1 : (0 : ℝ) < p - 1 := by linarith
  -- Upper bound: ν_p(n!)/n ≤ 1/(p-1) for all n ≥ 1
  have h_upper : ∀ᶠ n in atTop, (padicValNat p n.factorial : ℝ) / n ≤ 1 / (p - 1) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    sorry -- Legendre + ⌊n/p^k⌋ ≤ n/p^k + geometric series ≤ n/(p-1)
  -- Lower bound: ν_p(n!)/n ≥ 1/(p-1) - (log_p n + 1)/n for all n ≥ 1
  have h_lower_tendsto : Tendsto (fun n : ℕ =>
      1 / ((p : ℝ) - 1) - ((Nat.log p n : ℝ) + 1) / n) atTop (nhds (1 / (p - 1))) := by
    have : Tendsto (fun n : ℕ => ((Nat.log p n : ℝ) + 1) / n) atTop (nhds 0) := by
      sorry -- log_p(n)/n → 0
    rw [show (1 : ℝ) / (p - 1) = 1 / (p - 1) - 0 from by ring]
    exact Tendsto.sub tendsto_const_nhds this
  have h_lower : ∀ᶠ n in atTop, 1 / ((p : ℝ) - 1) - ((Nat.log p n : ℝ) + 1) / n ≤
      (padicValNat p n.factorial : ℝ) / n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    sorry -- Legendre + ⌊n/p^k⌋ ≥ n/p^k - 1 + sum over L terms
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lower_tendsto tendsto_const_nhds
    h_lower h_upper

/- ## Part V: Structure of Factorial Sums -/

/-- For a₁ ≤ a₂, a₁! + a₂! = a₁! * (1 + a₂!/a₁!) since a₁! | a₂!. -/
theorem factorial_sum_factored (a₁ a₂ : ℕ) (h : a₁ ≤ a₂) :
    a₁.factorial + a₂.factorial = a₁.factorial * (1 + a₂.factorial / a₁.factorial) := by
  have hdvd : a₁.factorial ∣ a₂.factorial := Nat.factorial_dvd_factorial h
  rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]

/- ## Part VI: Examples -/

example : 2^3 ∣ Nat.factorial 2 + Nat.factorial 3 := by native_decide
example : 3 ∣ Nat.factorial 1 + Nat.factorial 2 := by native_decide
example : 3^2 ∣ Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 := by native_decide

/- ## Part VII: Summary -/

theorem erdos_404_summary :
    f 2 2 ≤ 254 ∧
    (∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)) := by
  exact ⟨lin_bound, lin_bound_meaning⟩

end Erdos404
