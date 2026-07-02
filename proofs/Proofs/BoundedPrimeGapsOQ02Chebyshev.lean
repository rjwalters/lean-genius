/-
# Bounded Prime Gaps — Open Question 02:
# An explicit Chebyshev-type upper bound on π(x), axiom-free

Source: open question `prime-gap-bounds-oq-02` of the prime-gap-bounds gallery.

## Goal

Rosser–Schoenfeld (1962) proved the explicit inequalities

  x / log x  <  π(x)  <  1.25506 · x / log x        (x ≥ 17),

whose sharp constants require a numerically verified zero-free region for ζ and an
explicit prime number theorem. The sharp constants and the *lower* bound are out of
reach of today's Mathlib (which has no Chebyshev lower bound and no explicit PNT).

The **upper** bound, however, is derivable *now* and *axiom-free* from Mathlib's
Chebyshev estimate `Chebyshev.theta_le_log4_mul_x : θ x ≤ log 4 · x`, by the classical
elementary argument. This file carries out that derivation, obtaining a
Rosser–Schoenfeld-*spirit* explicit bound with the concrete (non-sharp) constant
`2 log 4 = log 16 ≈ 2.77`:

  π(⌊x⌋) ≤ √x + 1 + (log 16) · x / log x      (x > 1).

## The argument

Every prime `p` with `√x < p ≤ x` contributes `log p > log √x = ½ log x` to
`θ(x) = Σ_{p ≤ x} log p`. Keeping only this tail,

  θ(x)  ≥  Σ_{√x < p ≤ x} log p  ≥  (½ log x) · #{√x < p ≤ x : p prime}
        =  (½ log x) · (π(⌊x⌋) − π(⌊√x⌋)).

Combined with `θ(x) ≤ log 4 · x` this gives
`π(⌊x⌋) − π(⌊√x⌋) ≤ (2 log 4) x / log x`, and `π(⌊√x⌋) ≤ ⌊√x⌋ + 1 ≤ √x + 1`
finishes it.

The one piece Mathlib lacks is the bridge between `θ`'s prime sum and
`Nat.primeCounting` (an explicit TODO in `Mathlib/NumberTheory/Chebyshev.lean`); it is
supplied here as `count_primes_Ioc`.

## Status

The **upper** bound is fully proved, `0` axioms / `0` sorries. The matching **lower**
bound and the sharp Rosser–Schoenfeld constants remain open, blocked on the absence of
a Chebyshev lower bound and an explicit PNT error term in Mathlib.

References:
- J. B. Rosser and L. Schoenfeld, "Approximate formulas for some functions of prime
  numbers", Illinois J. Math. 6 (1962), 64–94.
- Mathlib `NumberTheory.Chebyshev` (θ, ψ and `theta_le_log4_mul_x`).
-/

import Mathlib

open Finset
open scoped Nat.Prime

namespace BoundedPrimeGapsOQ02Chebyshev

/-- **The θ ↔ π bridge (Mathlib TODO).** The number of primes in the interval
`(a, b]` equals `π(b) − π(a)`. -/
theorem count_primes_Ioc (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card = Nat.primeCounting b - Nat.primeCounting a := by
  -- `#{p ≤ m : prime} = π(m)`.
  have key : ∀ m, ((Finset.Iic m).filter Nat.Prime).card = Nat.primeCounting m := by
    intro m
    have h1 : (Nat.primesBelow (m + 1)).card = Nat.primeCounting m :=
      Nat.primesBelow_card_eq_primeCounting' (m + 1)
    rw [← h1]
    congr 1
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Iic,
      Nat.lt_succ_iff]
  -- `Iic b` splits as `Iic a ⊔ Ioc a b`.
  have hsplit : (Finset.Iic b).filter Nat.Prime =
      (Finset.Iic a).filter Nat.Prime ∪ (Finset.Ioc a b).filter Nat.Prime := by
    rw [← Finset.filter_union]
    congr 1
    ext p
    simp only [Finset.mem_Iic, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint ((Finset.Iic a).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at hp hq
    omega
  have hb := key b
  rw [hsplit, Finset.card_union_of_disjoint hdisj, key a] at hb
  have hmono : Nat.primeCounting a ≤ Nat.primeCounting b := Nat.monotone_primeCounting hab
  omega

/-- `π(n) ≤ n + 1`: the primes `≤ n` are among `{0, 1, …, n}`. -/
theorem primeCounting_le_succ (n : ℕ) : Nat.primeCounting n ≤ n + 1 := by
  have h1 : (Nat.primesBelow (n + 1)).card = Nat.primeCounting n :=
    Nat.primesBelow_card_eq_primeCounting' (n + 1)
  rw [← h1]
  calc (Nat.primesBelow (n + 1)).card
      ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range _

/-- **Explicit Chebyshev upper bound on π.** For `x > 1`,
`π(⌊x⌋) ≤ √x + 1 + (log 16) · x / log x`. This is a Rosser–Schoenfeld-spirit bound
with the concrete constant `2 log 4 = log 16`, derived axiom-free from Mathlib's
`theta_le_log4_mul_x`. -/
theorem primeCounting_floor_le (x : ℝ) (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      Real.sqrt x + 1 + (2 * Real.log 4) * x / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  -- Abbreviations for the floors.
  set s := ⌊Real.sqrt x⌋₊ with hs
  set b := ⌊x⌋₊ with hb
  -- The prime tail `T = (s, b]`.
  set T := (Finset.Ioc s b).filter Nat.Prime with hT
  -- Each prime in `T` exceeds `√x`, so its log is `≥ ½ log x`.
  have hlog_lb : ∀ p ∈ T, Real.log x / 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hps, _⟩, _⟩ := hp
    -- `p > s = ⌊√x⌋`, so `(p : ℝ) ≥ s + 1 > √x`.
    have hsx : Real.sqrt x < (p : ℝ) := by
      have h1 : Real.sqrt x < (s : ℝ) + 1 := by
        rw [hs]; exact Nat.lt_floor_add_one _
      have h2 : (s : ℝ) + 1 ≤ (p : ℝ) := by
        have : s + 1 ≤ p := hps
        exact_mod_cast this
      linarith
    have hple : Real.sqrt x ≤ (p : ℝ) := le_of_lt hsx
    calc Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt (le_of_lt hx0)).symm
      _ ≤ Real.log (p : ℝ) := Real.log_le_log hsx0 hple
  -- Every term of θ's sum is `≥ 0`.
  have hlog_nonneg : ∀ p ∈ (Finset.Ioc 0 b).filter Nat.Prime, 0 ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  -- `T ⊆ (0, b]`-primes.
  have hsub : T ⊆ (Finset.Ioc 0 b).filter Nat.Prime := by
    rw [hT]
    apply Finset.filter_subset_filter
    intro p hp
    rw [Finset.mem_Ioc] at hp ⊢
    exact ⟨by omega, hp.2⟩
  -- Lower bound θ(x) by the tail, then by `(½ log x) · |T|`.
  have hθ_ge : (T.card : ℝ) * (Real.log x / 2) ≤ Chebyshev.theta x := by
    have hθdef : Chebyshev.theta x
        = ∑ p ∈ (Finset.Ioc 0 b).filter Nat.Prime, Real.log (p : ℝ) := rfl
    calc (T.card : ℝ) * (Real.log x / 2)
        = ∑ _p ∈ T, (Real.log x / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ T, Real.log (p : ℝ) := Finset.sum_le_sum hlog_lb
      _ ≤ ∑ p ∈ (Finset.Ioc 0 b).filter Nat.Prime, Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hlog_nonneg p hp)
      _ = Chebyshev.theta x := hθdef.symm
  -- Chebyshev upper bound on θ.
  have hθ_le : Chebyshev.theta x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x (le_of_lt hx0)
  -- Combine: `|T| · (½ log x) ≤ log 4 · x`.
  have hcombine : (T.card : ℝ) * (Real.log x / 2) ≤ Real.log 4 * x := le_trans hθ_ge hθ_le
  -- `s = ⌊√x⌋ ≤ ⌊x⌋ = b`, since `√x ≤ x` for `x ≥ 1`.
  have hsb : s ≤ b := by
    rw [hs, hb]
    apply Nat.floor_le_floor
    have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by
      have := Real.sqrt_le_sqrt (le_of_lt hx); simpa using this
    have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
    nlinarith [Real.sqrt_nonneg x]
  have hmono : Nat.primeCounting s ≤ Nat.primeCounting b := Nat.monotone_primeCounting hsb
  -- Translate `|T|` into `π(b) − π(s)`.
  have hcard : T.card = Nat.primeCounting b - Nat.primeCounting s := by
    rw [hT]; exact count_primes_Ioc s b hsb
  -- `(π b : ℝ) - (π s : ℝ) = |T|`.
  have hTreal : (T.card : ℝ) = (Nat.primeCounting b : ℝ) - (Nat.primeCounting s : ℝ) := by
    rw [hcard, Nat.cast_sub hmono]
  -- Isolate `π b`.
  have hstep : ((Nat.primeCounting b : ℝ) - (Nat.primeCounting s : ℝ)) * (Real.log x / 2)
      ≤ Real.log 4 * x := by rw [← hTreal]; exact hcombine
  have hdiv : (Nat.primeCounting b : ℝ) - (Nat.primeCounting s : ℝ)
      ≤ (2 * Real.log 4) * x / Real.log x := by
    rw [le_div_iff₀ hLpos]
    nlinarith [hstep]
  -- `π s ≤ √x + 1`.
  have hs_le : (Nat.primeCounting s : ℝ) ≤ Real.sqrt x + 1 := by
    have h1 : Nat.primeCounting s ≤ s + 1 := primeCounting_le_succ s
    have h2 : (s : ℝ) ≤ Real.sqrt x := by rw [hs]; exact Nat.floor_le (le_of_lt hsx0)
    have : (Nat.primeCounting s : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast h1
    linarith
  linarith [hdiv, hs_le]

end BoundedPrimeGapsOQ02Chebyshev
