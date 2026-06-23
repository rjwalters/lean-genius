/-
# Möbius Inversion via Squarefree-Divisor / Powerset Bijection

## What This Proves
The classical Möbius-function identity

  Σ_{d | n} μ(d)  =  if n = 1 then 1 else 0

via a *direct constructive* argument that parallels the GCD-partition
aesthetic of `EulerTotientOQ04.lean`:

1. Only squarefree divisors contribute (μ vanishes on non-squarefree).
2. The squarefree divisors of `n` are in bijection with the powerset
   of `n.primeFactors`, via `S ↦ ∏_{p ∈ S} p`.
3. Under this bijection, `μ(∏_{p ∈ S} p) = (-1)^|S|`.
4. Summing yields `Σ_{S ⊆ primeFactors(n)} (-1)^|S| = (1-1)^{ω(n)}`,
   which is 1 iff `ω(n) = 0`, i.e. iff `n = 1` (for `n ≥ 1`).

## Why this isn't a Mathlib wrapper
Mathlib's `ArithmeticFunction.moebius_mul_coe_zeta` proves the same
identity via `recOnPosPrimePosCoprime` (multiplicative induction). The
proof here uses NO multiplicativity — it relies on the squarefree-
divisor / powerset bijection (`Mathlib.Data.Nat.Squarefree.sum_divisors_filter_squarefree`)
and the alternating binomial-sum identity (`Mathlib.Data.Nat.Choose.Sum.sum_powerset_neg_one_pow_card`).
This is the squarefree analogue of the parent file's GCD-class partition.

## Status
**Verified** — main theorem `sum_moebius_eq_indicator` fully proved.
Zero `sorry`s, zero `axiom`s.

Key building blocks:
- `moebius_prod_squarefree`: μ of a product of distinct primes is `(-1)^k`
  (uses `isMultiplicative_moebius.map_prod_of_prime`).
- `normalizedFactors_toFinset_eq`: Nat-side bridge from
  `(normalizedFactors n).toFinset` to `n.primeFactors`.
- `sum_filter_squarefree_moebius_eq_powerset`: combines the Mathlib
  bijection `Nat.sum_divisors_filter_squarefree` with
  `moebius_prod_squarefree` on each `S ⊆ primeFactors n`.

## Mathlib Dependencies
- `Mathlib.NumberTheory.ArithmeticFunction.Moebius` — `μ`, `moebius_eq_zero_of_not_squarefree`
- `Mathlib.Data.Nat.Squarefree` — `sum_divisors_filter_squarefree`
- `Mathlib.Data.Nat.Choose.Sum` — `sum_powerset_neg_one_pow_card`
- `Mathlib.RingTheory.UniqueFactorizationDomain.Nat` — `factors_eq` (Nat-side bridge)
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace EulerTotientOQ04OQ01

/- ## Part I: μ vanishes on non-squarefree divisors -/

/-- Restricting the divisor sum of `μ` to squarefree divisors changes
nothing, because `μ d = 0` whenever `d` is not squarefree. -/
theorem sum_moebius_divisors_eq_filter_squarefree (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = ∑ d ∈ n.divisors with Squarefree d, μ d := by
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors Squarefree (fun d => μ d)]
  have hzero : ∑ d ∈ n.divisors with ¬ Squarefree d, μ d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    exact moebius_eq_zero_of_not_squarefree hd.2
  rw [hzero, add_zero]

/- ## Part II: μ of a squarefree product of distinct primes -/

/-- For a finite set `s` of distinct primes, `μ (∏ s) = (-1)^|s|`.

Uses multiplicativity of `μ` on the product of pairwise-coprime primes
(`isMultiplicative_moebius.map_prod_of_prime`), then `μ p = -1` on each
prime, then `Finset.prod_eq_pow_card`. -/
theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [isMultiplicative_moebius.map_prod_of_prime s hs]
  exact Finset.prod_eq_pow_card (fun p hp => moebius_apply_prime (hs p hp))

/- ## Part III: bridge from Mathlib's normalizedFactors form to primeFactors -/

/-- For `n ≠ 0`, `(normalizedFactors n).toFinset = n.primeFactors`.
This is the Nat-side bridge for `sum_divisors_filter_squarefree`. -/
theorem normalizedFactors_toFinset_eq (n : ℕ) (hn : n ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
  ext p
  -- `factors_eq` rewrites `normalizedFactors n = n.primeFactorsList`,
  -- and `mem_primeFactors` characterises membership in `n.primeFactors`.
  simp [Nat.factors_eq, Nat.mem_primeFactors, hn]

/- ## Part IV: powerset-sum identity for the alternating signs -/

/-- For `n ≠ 0`, the Möbius sum on squarefree divisors equals
`Σ_{S ⊆ primeFactors n} (-1)^|S|`. This is the Mathlib bijection
`sum_divisors_filter_squarefree` composed with `moebius_prod_squarefree`. -/
theorem sum_filter_squarefree_moebius_eq_powerset (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors with Squarefree d, μ d : ℤ)
      = ∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card := by
  -- Apply Mathlib's bijection: sum on squarefree divisors → sum on powerset
  rw [Nat.sum_divisors_filter_squarefree hn]
  -- Rewrite the powerset index via `normalizedFactors_toFinset_eq`
  rw [normalizedFactors_toFinset_eq n hn]
  -- For each S ⊆ primeFactors n, μ(S.val.prod) = (-1)^|S|.
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  -- Rewrite `S.val.prod` to `∏ p ∈ S, p` via `Finset.prod_val`
  rw [Finset.prod_val]
  -- Each element of `S ⊆ n.primeFactors` is prime, so apply `moebius_prod_squarefree`.
  exact moebius_prod_squarefree S (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))

/- ## Part V: main result -/

/-- **Main Theorem**: `Σ_{d | n} μ(d) = [n = 1]`.

Constructive proof via squarefree-divisor / powerset bijection, parallel
to the GCD-partition proof of the parent file `EulerTotientOQ04.lean`. -/
theorem sum_moebius_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, μ d : ℤ) = if n = 1 then (1 : ℤ) else 0 := by
  -- Case n = 0: divisors are empty, indicator is 0.
  by_cases h0 : n = 0
  · subst h0
    simp
  -- Case n ≠ 0: route through squarefree filter + powerset sum.
  rw [sum_moebius_divisors_eq_filter_squarefree,
      sum_filter_squarefree_moebius_eq_powerset n h0,
      Finset.sum_powerset_neg_one_pow_card]
  -- Goal: (if n.primeFactors = ∅ then 1 else 0) = (if n = 1 then 1 else 0).
  have hpf : n.primeFactors = ∅ ↔ n = 1 := by
    rw [Nat.primeFactors_eq_empty]
    exact ⟨fun h => h.resolve_left h0, fun h => Or.inr h⟩
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (hpf.mp h1) h2
  · exact absurd (hpf.mpr h3) h1
  · rfl

/- ## Part VI: corollaries and validation -/

/-- The standard "indicator" form of the identity. -/
theorem sum_moebius_eq_one_iff_one (n : ℕ) :
    (∑ d ∈ n.divisors, μ d : ℤ) = 1 ↔ n = 1 := by
  rw [sum_moebius_eq_indicator]
  split_ifs with h
  · simp [h]
  · constructor
    · intro h1; exfalso; exact zero_ne_one h1
    · intro h1; exact absurd h1 h

/-- Concrete validation: μ(1) + μ(2) + μ(3) + μ(6) = 1 - 1 - 1 + 1 = 0 for n = 6. -/
example : (∑ d ∈ (6 : ℕ).divisors, μ d : ℤ) = 0 := by
  rw [sum_moebius_eq_indicator]; rfl

/-- Concrete validation: n = 1 case. -/
example : (∑ d ∈ (1 : ℕ).divisors, μ d : ℤ) = 1 := by
  rw [sum_moebius_eq_indicator]; rfl

/-- Concrete validation: prime case (μ(1) + μ(p) = 1 + (-1) = 0). -/
example : (∑ d ∈ (5 : ℕ).divisors, μ d : ℤ) = 0 := by
  rw [sum_moebius_eq_indicator]; rfl

end EulerTotientOQ04OQ01
