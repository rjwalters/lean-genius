/-
Erdős Problem #404: Prime Power Divisibility of Factorial Sums

Source: https://erdosproblems.com/404
Status: OPEN

Statement:
For which integers a ≥ 1 and primes p is there a finite upper bound on those k
such that there exist a = a₁ < a₂ < ··· < aₙ with p^k | (a₁! + a₂! + ··· + aₙ!)?

Let f(a, p) denote the greatest such k if it exists. How does f(a, p) behave?

Secondary question: Is there a prime p and an infinite sequence a₁ < a₂ < ···
such that if p^{mₖ} is the highest power of p dividing ∑_{i≤k} aᵢ!, then mₖ → ∞?

Known results:
- Lin (1976): f(2, 2) ≤ 254

References:
- Erdős-Graham [ErGr80]
- Related to Problem #403

Tags: number-theory, p-adic-valuation, factorials, divisibility, open-problem
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat Finset Filter

namespace Erdos404

/- ## Part I: Core Definitions -/

/-- A strictly increasing sequence starting at a. -/
structure StrictIncSeq (a : ℕ) where
  length : ℕ
  seq : Fin length → ℕ
  starts_at_a : length > 0 → seq ⟨0, by omega⟩ = a
  strictly_increasing : ∀ i j : Fin length, i < j → seq i < seq j

/-- The sum of factorials over a sequence. -/
noncomputable def factorialSum (s : StrictIncSeq a) : ℕ :=
  ∑ i : Fin s.length, (s.seq i).factorial

/-- p^k divides the factorial sum of some sequence starting at a. -/
def dividesByPrimePower (a k : ℕ) (p : ℕ) : Prop :=
  ∃ s : StrictIncSeq a, p^k ∣ factorialSum s

/-- The set of k such that some sequence starting at a has p^k | sum of factorials. -/
def divisiblePowers (a : ℕ) (p : ℕ) : Set ℕ :=
  {k | dividesByPrimePower a k p}

/-- f(a, p) = sup {k : p^k divides some factorial sum starting at a}. -/
noncomputable def f (a : ℕ) (p : ℕ) : ℕ∞ :=
  sSup (divisiblePowers a p : Set ℕ)

/- ## Part II: Main Questions -/

/-- The secondary question: does there exist p and a sequence with mₖ → ∞? -/
def secondaryQuestion : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k+1), (seq i).factorial)) atTop atTop

/-- Erdős Problem #404 (OPEN):
    For which (a, p) is f(a, p) finite? -/
def erdos404Conjecture : Prop :=
  ∀ a : ℕ, a ≥ 1 → ∀ p : ℕ, p.Prime → f a p < ⊤

/- ## Part III: Known Results -/

/-- Lin's bound (1976): f(2, 2) ≤ 254. -/
axiom lin_bound : f 2 2 ≤ 254

/-- Lin's bound means: for any strictly increasing sequence starting at 2,
    2^255 does not divide the sum of factorials. -/
axiom lin_bound_meaning : ∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)

/- ## Part IV: p-adic Analysis of Factorials -/

/-- Legendre's formula: v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋. -/
noncomputable def legendreSum (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log p n + 1), n / p^(i+1)

/-- Legendre's formula for p-adic valuation of factorials. -/
axiom legendre_formula (n p : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    padicValNat p n.factorial = legendreSum n p

/-- For large n, v_p(n!) ≈ n/(p-1). -/
axiom padic_val_factorial_asymp (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n => (padicValNat p n.factorial : ℝ) / n) atTop (nhds (1/(p-1)))

/- ## Part V: Structure of Factorial Sums -/

/-- If a₁ < a₂, then a₁! + a₂! ≡ a₁! (mod a₂!),
    because a₂! | a₂! and a₁! is the remainder. -/
axiom factorial_sum_mod (a₁ a₂ : ℕ) (h : a₁ < a₂) :
    a₁.factorial + a₂.factorial ≡ a₁.factorial [MOD a₂.factorial]

/-- Key observation: a₁! + a₂! = a₁!(1 + a₂!/a₁!) for a₁ ≤ a₂.
    The ratio a₂!/a₁! determines the p-adic cancellation behavior. -/
axiom factorial_sum_factored (a₁ a₂ : ℕ) (h : a₁ ≤ a₂) :
    a₁.factorial + a₂.factorial = a₁.factorial * (1 + a₂.factorial / a₁.factorial)

/- ## Part VI: Examples -/

/-- Example: 2! + 3! = 2 + 6 = 8 = 2³, so f(2, 2) ≥ 3. -/
example : 2^3 ∣ Nat.factorial 2 + Nat.factorial 3 := by
  native_decide

/-- Example: 1! + 2! = 1 + 2 = 3, so 3 | 1! + 2!. -/
example : 3 ∣ Nat.factorial 1 + Nat.factorial 2 := by
  native_decide

/- ## Part VII: Summary -/

/-- Erdős Problem #404: OPEN.
    Known: Lin (1976) proved f(2, 2) ≤ 254 — the only concrete upper bound.
    Key tools: Legendre's formula for v_p(n!), factorial sum factorization.
    The secondary question about mₖ → ∞ is also open. -/
theorem erdos_404_summary :
    -- Lin's bound is the main known result
    f 2 2 ≤ 254 ∧
    -- Lin's bound unpacked
    (∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)) := by
  exact ⟨lin_bound, lin_bound_meaning⟩

end Erdos404
