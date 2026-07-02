/-
# Central Binomial Coefficient Asymptotics: C(2n,n) ~ 4ⁿ / √(πn)

This file answers the open question `chebyshev-bounds-oq-06-oq-01`:

> Can the upper bound be sharpened to the standard C(2n,n) ≤ 4ⁿ/√(πn) (Stirling)
> within Mathlib, giving the matching asymptotic C(2n,n) ~ 4ⁿ/√(πn)?

We establish the **asymptotic equivalence**

    (2n).choose n  ~[atTop]  4ⁿ / √(π n)

as `n → ∞`, derived entirely from Mathlib's Stirling approximation
`Stirling.factorial_isEquivalent_stirling`, namely `n! ~ √(2πn)·(n/e)ⁿ`.

## Method

Writing `C(2n,n) = (2n)! / (n!)²` and applying the Stirling equivalence to the
numerator (at index `2n`) and denominator, algebra collapses the Stirling factors:

    √(4πn)·(2n/e)^{2n} / ((2πn)·(n/e)^{2n})
      = √(4πn)·4ⁿ / (2πn)                 [since (2n/e)^{2n} = 4ⁿ·(n/e)^{2n}]
      = 2√(πn)·4ⁿ / (2πn)
      = 4ⁿ / √(πn).

This is a **0-axiom** result: it is a pure consequence of the already-formalised
Stirling asymptotic and elementary `IsEquivalent` algebra (`.mul`, `.div`,
`.comp_tendsto`).

Note the *effective* one-sided inequality `C(2n,n) ≤ 4ⁿ/√(πn)` for every `n`
requires an effective **upper** bound on `n!` (Robbins' bounds), which is not yet
in Mathlib (see the comment in `Mathlib/Analysis/SpecialFunctions/Stirling.lean`).
The asymptotic equivalence proved here is the achievable, and mathematically
substantive, part of the open question.
-/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Central

open Real Filter Asymptotics
open scoped Nat

namespace ChebyshevBoundsOQ0601

/-- **Central binomial asymptotic.**
The central binomial coefficient `C(2n,n) = (2n).choose n` is asymptotically
equivalent to `4ⁿ / √(π n)`.  Derived from Mathlib's Stirling approximation. -/
theorem centralBinom_isEquivalent_four_pow_div_sqrt :
    (fun n : ℕ => (n.centralBinom : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (π * n)) := by
  -- Stirling: `n! ~ √(2πn)·(n/e)ⁿ`.  After `set S`, `H : (fun n => n!) ~ S`.
  have H := Stirling.factorial_isEquivalent_stirling
  set S : ℕ → ℝ := fun n => Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n with hS
  -- `n ↦ 2 * n` tends to infinity.
  have hk : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  -- Numerator asymptotic: `(2n)! ~ S (2n)`.
  have h2n : (fun n : ℕ => ((2 * n)! : ℝ)) ~[atTop] (fun n : ℕ => S (2 * n)) := by
    have := H.comp_tendsto hk
    simpa [Function.comp] using this
  -- Denominator asymptotic: `n! · n! ~ S n · S n`.
  have hmul : (fun n : ℕ => (n ! : ℝ) * (n ! : ℝ)) ~[atTop] (fun n : ℕ => S n * S n) :=
    H.mul H
  -- Exact cast identity: `C(2n,n) = (2n)! / (n! · n!)`.
  have e1 : (fun n : ℕ => (n.centralBinom : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => ((2 * n)! : ℝ) / ((n ! : ℝ) * (n ! : ℝ))) := by
    filter_upwards with n
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, eq_div_iff (by positivity)]
    have hcast : ((2 * n).choose n) * (n ! * n !) = (2 * n)! := by rw [← h]; ring
    exact_mod_cast hcast
  -- Chain the equivalences: `C(2n,n) ~ (2n)!/(n!·n!) ~ S(2n)/(S n · S n)`.
  have hdiv : (fun n : ℕ => ((2 * n)! : ℝ) / ((n ! : ℝ) * (n ! : ℝ))) ~[atTop]
      (fun n : ℕ => S (2 * n) / (S n * S n)) := h2n.div hmul
  refine (e1.isEquivalent.trans hdiv).trans_eventuallyEq ?_
  -- Remaining: `S(2n)/(S n · S n) = 4ⁿ/√(π n)` for `n ≥ 1`.
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set s := Real.sqrt (π * (n : ℝ)) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = π * (n : ℝ) := Real.sq_sqrt (by positivity)
  set P := ((n : ℝ) / Real.exp 1) ^ (2 * n) with hP_def
  have hPpos : 0 < P := by rw [hP_def]; positivity
  have hPne : P ≠ 0 := hPpos.ne'
  -- Unfold `S` into the concrete Stirling expression.
  simp only [hS]
  -- √(2·(2n)·π) = 2s.
  have hnum_sqrt : Real.sqrt (2 * ((2 * n : ℕ) : ℝ) * π) = 2 * s := by
    have h4 : (2 : ℝ) * ((2 * n : ℕ) : ℝ) * π = (2 * s) ^ 2 := by
      push_cast; rw [mul_pow, hs2]; ring
    rw [h4, Real.sqrt_sq (by linarith)]
  -- ((2n)/e)^{2n} = 4ⁿ · P.
  have hnum_pow : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) = 4 ^ n * P := by
    have h1 : ((2 * n : ℕ) : ℝ) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) := by
      push_cast; ring
    rw [h1, mul_pow, hP_def]
    congr 1
    rw [pow_mul]; norm_num
  -- √(2nπ)·√(2nπ) = 2s².
  have hAA : Real.sqrt (2 * (n : ℝ) * π) * Real.sqrt (2 * (n : ℝ) * π) = 2 * s ^ 2 := by
    rw [← pow_two, Real.sq_sqrt (by positivity), hs2]; ring
  -- (n/e)ⁿ·(n/e)ⁿ = P.
  have hBB : ((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n = P := by
    rw [← pow_add, hP_def, two_mul]
  rw [hnum_sqrt, hnum_pow]
  rw [show (Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n) *
          (Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n)
        = (Real.sqrt (2 * (n : ℝ) * π) * Real.sqrt (2 * (n : ℝ) * π)) *
          (((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n) from by ring]
  rw [hAA, hBB]
  -- Final algebra: 2s·(4ⁿ·P) / (2s²·P) = 4ⁿ/s.
  rw [pow_two]
  field_simp

/-- Restatement in terms of `Nat.choose`: `C(2n,n) ~ 4ⁿ / √(π n)`. -/
theorem choose_two_mul_isEquivalent_four_pow_div_sqrt :
    (fun n : ℕ => ((2 * n).choose n : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (π * n)) := by
  have h := centralBinom_isEquivalent_four_pow_div_sqrt
  simpa [Nat.centralBinom_eq_two_mul_choose] using h

end ChebyshevBoundsOQ0601
