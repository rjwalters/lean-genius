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

/-
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

/-
## The Main Conjectures (OPEN)

Erdős asked whether unbounded growth on prime powers implies
unbounded growth of consecutive differences.
-/

/- **Erdős Problem #897, Part I (OPEN)**: If f is additive and
f(p^k) / log(p^k) is unbounded over prime powers, then is
(f(n+1) - f(n)) / log(n) also unbounded?

This asks whether rapid growth on prime powers propagates to
consecutive differences. -/

/- **Erdős Problem #897, Part II (OPEN)**: If f is additive and
f(p^k) / log(p^k) is unbounded over prime powers, then is
f(n+1) / f(n) also unbounded?

This asks whether the ratio of consecutive values can be arbitrarily large. -/

/-
## Wirsing's Theorem (SOLVED)

The converse direction is known: if consecutive differences are
BOUNDED, then f must behave like log.
-/

/- **Wirsing's Theorem (1970)**: If f is additive and the consecutive
differences |f(n+1) - f(n)| are bounded by some constant C, then
f(n) = c·log(n) + O(1) for some constant c.

This characterizes log as the essentially unique additive function with
bounded consecutive differences. -/

/-
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

/- **Restricted Variant, Part I (OPEN)**: Same as Part I, but restricted
to functions that are either strongly additive or completely additive. -/

/- **Restricted Variant, Part II (OPEN)**: Same as Part II, but restricted
to functions that are either strongly additive or completely additive. -/

/-
## Classical Examples of Additive Functions
-/

/-- The number of distinct prime divisors function ω(n). -/
noncomputable def omega (n : ℕ) : ℝ := (n.primeFactors.card : ℝ)

/-- The total number of prime factors Ω(n) (with multiplicity). -/
noncomputable def bigOmega (n : ℕ) : ℝ := (n.primeFactorsList.length : ℝ)

/-- The natural logarithm function (restricted to ℕ). -/
noncomputable def logN (n : ℕ) : ℝ := Real.log n

/-
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

/-
## The Classical Examples Are Genuine Instances

The definitions above are only meaningful if the canonical additive functions
actually satisfy them. We verify this, so the predicates are non-vacuous and
correctly capture their intended objects.
-/

/-- The natural logarithm is **completely additive**: `log(ab) = log a + log b`
for positive `a, b`, and `log(p^k) = k·log p`. This is the prototypical
completely additive function (and the unique one, up to scaling, with bounded
consecutive differences — Wirsing's theorem). -/
theorem logN_completelyAdditive : IsCompletelyAdditive logN := by
  refine ⟨?_, ?_⟩
  · intro a b ha hb _hab
    simp only [logN, Nat.cast_mul]
    rw [Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
  · intro p k _hp
    simp only [logN, Nat.cast_pow, Real.log_pow]

/-- `ω(n)` (the number of distinct prime divisors) is **strongly additive**:
it adds over coprime arguments and is constant on prime powers, `ω(p^k) = ω(p) = 1`. -/
theorem omega_stronglyAdditive : IsStronglyAdditive omega := by
  refine ⟨?_, ?_⟩
  · intro a b ha hb hab
    simp only [omega]
    rw [Nat.primeFactors_mul ha.ne' hb.ne',
        Finset.card_union_of_disjoint hab.disjoint_primeFactors]
    push_cast
    ring
  · intro p k _hp hk
    simp only [omega]
    rw [Nat.primeFactors_pow p (by omega : k ≠ 0)]

/-
## Reduction for Completely Additive Functions

For a *completely additive* `f` the prime-power growth hypothesis collapses to a
condition on primes alone. Since `f(p^k) = k·f(p)` and `log(p^k) = k·log p`, the
multiplier `k` cancels in the ratio `f(p^k)/log(p^k) = f(p)/log p`. This turns
the `limsup` over all prime powers into a `limsup` over primes, which is the
form in which Part I is usually analyzed for the completely additive case.
-/

/-- **Reduction theorem.** For completely additive `f`, the hypothesis of
Erdős #897 (`f` unbounded on prime powers relative to `log`) is *equivalent* to
the statement that `f(p)/log p` is unbounded over the primes:
`f(p^k) > M·log(p^k)` for some prime power iff `f(p) > M·log p` for some prime.

The forward direction cancels the common factor `k`; the reverse takes `k = 1`. -/
theorem completelyAdditive_unboundedOnPrimePowers_iff
    (f : ℕ → ℝ) (hf : IsCompletelyAdditive f) :
    UnboundedOnPrimePowers f ↔
      ∀ M : ℝ, ∃ p : ℕ, p.Prime ∧ f p > M * Real.log p := by
  constructor
  · intro h M
    obtain ⟨p, k, hp, hk, hpk⟩ := h M
    refine ⟨p, hp, ?_⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hfk : f (p ^ k) = (k : ℝ) * f p := hf.2 p k hp
    rw [hfk, Real.log_pow] at hpk
    -- hpk : (k:ℝ) * f p > M * ((k:ℝ) * Real.log p)
    rw [show M * ((k : ℝ) * Real.log p) = (k : ℝ) * (M * Real.log p) from by ring] at hpk
    exact lt_of_mul_lt_mul_left hpk hkpos.le
  · intro h M
    obtain ⟨p, hp, hpk⟩ := h M
    refine ⟨p, 1, hp, le_refl 1, ?_⟩
    simpa [hf.2 p 1 hp] using hpk

end Erdos897
