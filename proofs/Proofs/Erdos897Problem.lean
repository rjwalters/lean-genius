/-
  Erdős Problem #897: Additive Functions and Consecutive Differences

  Let f(n) be an additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1)
  such that limsup_{p,k} f(p^k) log(p^k) = ∞.

  **Questions**:
  1. Is it true that limsup_n (f(n+1) - f(n)) / log(n) = ∞?
  2. Is it true that limsup_n f(n+1) / f(n) = ∞?

  **Status**: OPEN — Both questions remain unresolved.

  **Known Result** (Wirsing 1970):
  If |f(n+1) - f(n)| ≤ C for all n, then f(n) = c·log(n) + O(1).

  References:
  - https://erdosproblems.com/897
  - Wirsing, E., "A characterization of log n as an additive arithmetic
    function." Symposia Math. (1970), 45-47.
-/

import Mathlib

open Filter Asymptotics

namespace Erdos897

/-!
## Core Definitions

An additive arithmetic function satisfies f(ab) = f(a) + f(b) whenever
gcd(a, b) = 1. This is weaker than completely additive (which requires
the relation for all a, b).
-/

/-- A function f : ℕ → ℝ is **additive** if f(ab) = f(a) + f(b) whenever
gcd(a, b) = 1. Classic examples include:
- ω(n): number of distinct prime divisors
- Ω(n): total number of prime factors (with multiplicity)
- log(n): the natural logarithm -/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b

/-- The condition that f grows unboundedly on prime powers, faster than
log(p^k). Specifically: limsup_{p prime, k ≥ 1} f(p^k) / log(p^k) = ∞. -/
def UnboundedOnPrimePowers (f : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ f (p ^ k) > M * Real.log (p ^ k)

/-!
## The Main Conjectures (OPEN)

Erdős asked whether unbounded growth on prime powers implies
unbounded growth of consecutive differences.
-/

/-- **Erdős Problem #897, Part I (OPEN)**: If f is additive and
f(p^k) / log(p^k) is unbounded over prime powers, then is
(f(n+1) - f(n)) / log(n) also unbounded?

This asks whether rapid growth on prime powers propagates to
consecutive differences. -/
axiom erdos_897_part_i :
    ∀ f : ℕ → ℝ, IsAdditive f → UnboundedOnPrimePowers f →
      ∀ M : ℝ, ∃ᶠ n in atTop, (f (n + 1) - f n) / Real.log n > M

/-- **Erdős Problem #897, Part II (OPEN)**: If f is additive and
f(p^k) / log(p^k) is unbounded over prime powers, then is
f(n+1) / f(n) also unbounded?

This asks whether the ratio of consecutive values can be arbitrarily large. -/
axiom erdos_897_part_ii :
    ∀ f : ℕ → ℝ, IsAdditive f → UnboundedOnPrimePowers f →
      ∀ M : ℝ, ∃ᶠ n in atTop, f (n + 1) / f n > M

/-!
## Wirsing's Theorem (SOLVED)

The converse direction is known: if consecutive differences are
BOUNDED, then f must behave like log.
-/

/-- **Wirsing's Theorem (1970)**: If f is additive and the consecutive
differences |f(n+1) - f(n)| are bounded by some constant C, then
f(n) = c·log(n) + O(1) for some constant c.

This characterizes log as the essentially unique additive function with
bounded consecutive differences. -/
axiom wirsing_theorem :
    ∀ f : ℕ → ℝ, IsAdditive f →
      (∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| ≤ C) →
        ∃ c : ℝ, (fun n => f n - c * Real.log n) =O[atTop] (1 : ℕ → ℝ)

/-!
## Restricted Variants (OPEN)

The same questions restricted to functions where f(p^k) has a
simple relationship with f(p).
-/

/-- The function f is **strongly additive** if f(p^k) = f(p) for all
primes p and k ≥ 1. Example: ω(n), the number of distinct prime factors. -/
def IsStronglyAdditive (f : ℕ → ℝ) : Prop :=
  IsAdditive f ∧ ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) = f p

/-- The function f is **completely additive** if f(p^k) = k·f(p) for all
primes p and k ≥ 1. Example: Ω(n), the total prime factor count;
or log(n). -/
def IsCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  IsAdditive f ∧ ∀ p k : ℕ, p.Prime → f (p ^ k) = k * f p

/-- **Restricted Variant, Part I (OPEN)**: Same as Part I, but restricted
to functions that are either strongly additive or completely additive. -/
axiom erdos_897_restricted_part_i :
    ∀ f : ℕ → ℝ, (IsStronglyAdditive f ∨ IsCompletelyAdditive f) →
      UnboundedOnPrimePowers f →
        ∀ M : ℝ, ∃ᶠ n in atTop, (f (n + 1) - f n) / Real.log n > M

/-- **Restricted Variant, Part II (OPEN)**: Same as Part II, but restricted
to functions that are either strongly additive or completely additive. -/
axiom erdos_897_restricted_part_ii :
    ∀ f : ℕ → ℝ, (IsStronglyAdditive f ∨ IsCompletelyAdditive f) →
      UnboundedOnPrimePowers f →
        ∀ M : ℝ, ∃ᶠ n in atTop, f (n + 1) / f n > M

/-!
## Classical Examples of Additive Functions
-/

/-- The number of distinct prime divisors function ω(n). -/
noncomputable def omega (n : ℕ) : ℝ := (n.primeFactors.card : ℝ)

/-- The total number of prime factors Ω(n) (with multiplicity). -/
noncomputable def bigOmega (n : ℕ) : ℝ := (n.primeFactorsList.length : ℝ)

/-- The natural logarithm function (restricted to ℕ). -/
noncomputable def logN (n : ℕ) : ℝ := Real.log n

/-- omega is strongly additive. -/
axiom omega_strongly_additive : IsStronglyAdditive omega

/-- bigOmega is completely additive. -/
axiom bigOmega_completely_additive : IsCompletelyAdditive bigOmega

/-- log is completely additive (up to the convention that log(1) = 0). -/
axiom log_completely_additive : IsCompletelyAdditive logN

/-!
## Basic Properties
-/

/-- Additive functions satisfy f(1) = 0.
Proof: f(1) = f(1·1) = f(1) + f(1), so f(1) = 0. -/
theorem additive_at_one (f : ℕ → ℝ) (hf : IsAdditive f) : f 1 = 0 := by
  have h := hf 1 1 (by norm_num) (by norm_num) ((Nat.coprime_self 1).mpr rfl)
  simp at h
  linarith

/-- For completely additive f, f(p^k) = k·f(p).
This follows directly from the definition. -/
theorem completely_additive_prime_power (f : ℕ → ℝ) (hf : IsCompletelyAdditive f)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : f (p ^ k) = k * f p := hf.2 p k hp

/-- For strongly additive f, f(p^k) = f(p) when k ≥ 1.
The prime power contributes only once. -/
theorem strongly_additive_prime_power (f : ℕ → ℝ) (hf : IsStronglyAdditive f)
    (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) : f (p ^ k) = f p := hf.2 p k hp hk

end Erdos897
