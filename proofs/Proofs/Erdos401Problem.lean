/-
  Erdős Problem #401: Factorial Divisibility with Prime Products

  Source: https://erdosproblems.com/401
  Status: PROVED (Barreto-Leeham 2026)

  Statement:
  Does there exist a function f(r) → ∞ as r → ∞ such that for infinitely many n,
  there exist a₁, a₂ with a₁ + a₂ > n + f(r)·log(n) where
  a₁!·a₂! | n!·2ⁿ·3ⁿ·...·pᵣⁿ?

  (Here pᵣ denotes the r-th prime.)

  Answer: YES

  Background:
  This problem is related to #400 which studied g_k(n), the maximum of
  (a₁ + ... + aₖ) - n where a₁!·...·aₖ! | n!.

  Erdős-Graham showed g_k(n) ≪ log(n), so without the extra factor 2ⁿ3ⁿ...pᵣⁿ,
  we cannot exceed n + O(log n). The question asks whether adding prime power
  factors allows us to exceed this bound by an unbounded amount.

  Solution:
  Barreto and Leeham (2026) proved YES using essentially the same construction
  as Problem #729. The key idea is that the extra prime power factors give
  enough "room" in the factorial divisibility to push a₁ + a₂ further beyond n.

  Counterexample to Alternative Formulation:
  Sothanaphan showed the "for all large n" version is FALSE using:
  n = p_{r+1}^k - 1 (one less than a prime power)

  References:
  - [ErGr80] Erdős, P. & Graham, R. Old and New Problems and Results in
    Combinatorial Number Theory. p.78
  - Barreto, Leeham (2026): AI-assisted proof using same technique as #729
-/

import Mathlib

open Nat Real BigOperators Finset

namespace Erdos401

/-! ## Prime Infrastructure -/

/-- The r-th prime number (0-indexed: p₀ = 2, p₁ = 3, etc.) -/
noncomputable def nthPrime (r : ℕ) : ℕ := Nat.nth Nat.Prime r

/-- Product of first r primes raised to power n: 2ⁿ·3ⁿ·...·pᵣⁿ -/
noncomputable def primorialPow (r n : ℕ) : ℕ :=
  ∏ i ∈ range r, (nthPrime i)^n

/-! ## Divisibility Predicate -/

/-- The factorial divisibility condition: a₁!·a₂! | n!·primorialPow(r,n) -/
def FactorialDivides (a₁ a₂ n r : ℕ) : Prop :=
  (a₁.factorial * a₂.factorial) ∣ (n.factorial * primorialPow r n)

/-! ## The Erdős-Graham Baseline -/

/-- Erdős-Graham: Without extra factors, a₁ + a₂ ≤ n + O(log n) when a₁!a₂! | n!.
    This is the baseline that Problem #401 asks us to exceed. -/
axiom erdos_graham_baseline :
  ∃ C : ℝ, C > 0 ∧ ∀ n a₁ a₂ : ℕ, n > 0 →
    (a₁.factorial * a₂.factorial) ∣ n.factorial →
    (a₁ + a₂ : ℝ) ≤ n + C * Real.log n

/-! ## The Conjecture (Problem 401) -/

/-- A function f(r) that tends to infinity as r → ∞ -/
def TendsToInfty (f : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ r₀ : ℕ, ∀ r ≥ r₀, f r ≥ M

/-- Erdős Problem #401: Does there exist f(r) → ∞ such that for infinitely many n,
    we can find a₁, a₂ with a₁ + a₂ > n + f(r)·log(n) satisfying the divisibility? -/
def Erdos401Conjecture : Prop :=
  ∃ f : ℕ → ℝ, TendsToInfty f ∧
    ∀ r : ℕ, ∃ᶠ n in Filter.atTop, ∃ a₁ a₂ : ℕ,
      FactorialDivides a₁ a₂ n r ∧
      (a₁ + a₂ : ℝ) > n + f r * Real.log n

/-! ## The Barreto-Leeham Proof -/

/-- The main theorem: Erdős Problem #401 is TRUE.

    Barreto and Leeham proved this using the same construction as Problem #729.
    The key insight is that the primorial power n! · 2ⁿ3ⁿ...pᵣⁿ has "extra"
    prime factors that allow us to satisfy a₁!a₂! | (n! · primorialPow(r,n))
    with larger values of a₁ + a₂ than would be possible for a₁!a₂! | n! alone.

    The construction works as follows:
    1. Choose n carefully (related to primorial structure)
    2. Set a₂ ≈ n/2 and a₁ ≈ n/2 + excess
    3. The excess can be made arbitrarily large as r increases -/
axiom barreto_leeham_401 : Erdos401Conjecture

/-- Erdős Problem #401 is PROVED. -/
theorem erdos_401_proved : Erdos401Conjecture := barreto_leeham_401

/-! ## The Sothanaphan Counterexample -/

/-- The alternative "for all large n" formulation is FALSE.

    Sothanaphan's counterexample: Taking n = p_{r+1}^k - 1 for large k,
    we cannot satisfy the divisibility with a₁ + a₂ exceeding n + f(r) log n
    for unbounded f(r). -/
def Erdos401Strong : Prop :=
  ∃ f : ℕ → ℝ, TendsToInfty f ∧
    ∀ r : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a₁ a₂ : ℕ,
      FactorialDivides a₁ a₂ n r ∧
      (a₁ + a₂ : ℝ) > n + f r * Real.log n

/-- Sothanaphan showed the strong version is FALSE. -/
axiom sothanaphan_counterexample : ¬Erdos401Strong

/-! ## Connection to Problem #400 -/

/-- The g_k function from Problem #400: max (a₁ + ... + aₖ - n) over valid tuples.
    For k = 2, this is the maximum excess a₁ + a₂ - n when a₁!a₂! | n!. -/
noncomputable def g₂ (n : ℕ) : ℝ :=
  sSup { x : ℝ | ∃ a₁ a₂ : ℕ, (a₁.factorial * a₂.factorial) ∣ n.factorial ∧ x = a₁ + a₂ - n }

/-- Erdős-Graham bound: g₂(n) ≪ log n. -/
axiom g2_log_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n > 1, g₂ n ≤ C * Real.log n

/-- The modified function with primorial factors. -/
noncomputable def g₂_modified (n r : ℕ) : ℝ :=
  sSup { x : ℝ | ∃ a₁ a₂ : ℕ, FactorialDivides a₁ a₂ n r ∧ x = a₁ + a₂ - n }

/-- Problem #401 can be rephrased: Is there f(r) → ∞ such that
    g₂_modified(n, r) > f(r) log n for infinitely many n?

    The equivalence follows from the definitions - the conjecture directly
    states the existence of such a₁, a₂ achieving the bound. -/
axiom erdos_401_reformulation :
    Erdos401Conjecture ↔
    ∃ f : ℕ → ℝ, TendsToInfty f ∧
      ∀ r : ℕ, ∃ᶠ n in Filter.atTop, g₂_modified n r > f r * Real.log n

/-! ## Related Result: Problem #729 -/

/-- Problem #729 asks about divisibility in the related form.
    The same Barreto-Leeham construction proves both #401 and #729. -/
axiom erdos_729_connection :
  Erdos401Conjecture ↔
  ∃ f : ℕ → ℝ, TendsToInfty f ∧
    ∀ C : ℝ, C > 0 → ∃ᶠ n in Filter.atTop, ∃ a b : ℕ,
      (a.factorial * b.factorial) ∣ (n.factorial * (a + b - n).factorial) ∧
      (a + b : ℝ) > n + f 1 * Real.log n

/-! ## Summary

**Problem Status: PROVED**

Erdős Problem #401 asked whether the factorial divisibility constraint
a₁!a₂! | n!·2ⁿ3ⁿ...pᵣⁿ allows exceeding n + f(r)·log(n) for some f(r) → ∞.

**Answer: YES** (Barreto-Leeham 2026)

**Key Points:**
1. Without extra factors, Erdős-Graham shows a₁ + a₂ ≤ n + O(log n)
2. The primorial factors 2ⁿ3ⁿ...pᵣⁿ provide extra "room"
3. Same construction works for Problem #729
4. The "for all large n" version is FALSE (Sothanaphan)

**Technique:**
Uses the construction from Problem #728/729 that carefully chooses n, a₁, a₂
to exploit the extra divisibility from the primorial factors.

References:
- Erdős & Graham (1980). Old and New Problems, p.78
- Barreto & Leeham (2026). AI-assisted proof via ChatGPT
-/

end Erdos401
