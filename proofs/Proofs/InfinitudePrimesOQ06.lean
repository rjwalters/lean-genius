import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-!
# Euclid's Doubly-Exponential Prime Bound: `pₙ ≤ 2^(2ⁿ)`

## What This Proves
Let `pₙ = Nat.nth Nat.Prime n` be the `n`-th prime (0-indexed: `p₀ = 2`,
`p₁ = 3`, `p₂ = 5`, …). We prove the classical explicit bound

```
  pₙ ≤ 2^(2ⁿ).
```

This is the quantitative content of Euclid's proof of the infinitude of
primes: not only are there infinitely many primes, but the `n`-th prime is
at most doubly-exponential in `n`. It answers the open question (oq-06)
attached to the gallery's *Infinitude of Primes* entry — a *tighter* witness
than the `n! + 1` construction the parent proof uses.

## Approach
The engine is the **Euclid recurrence**

```
  p_{n+1} ≤ p₀ · p₁ ⋯ pₙ + 1.
```

Proof of the recurrence: the Euclid number `N = ∏_{i ≤ n} pᵢ + 1` is `≥ 2`,
so it has a prime factor `q`. That `q` cannot be any of `p₀, …, pₙ` (each
divides the product, hence would divide `1`). Since `Nat.nth Nat.Prime`
enumerates *all* primes in increasing order, a prime `q` outside the first
`n+1` primes has `Nat.count Nat.Prime q ≥ n+1`, so by strict monotonicity
`p_{n+1} ≤ q ≤ N`.

Feeding the recurrence into a strong induction and using

```
  ∏_{i < k} 2^(2ⁱ) = 2^(2ᵏ - 1)
```

(a clean telescoping of exponents, since `∑_{i<k} 2ⁱ = 2ᵏ - 1`) gives

```
  p_{m+1} ≤ 2^(2^{m+1} - 1) + 1 ≤ 2^(2^{m+1}).
```

## Status
- [x] Complete proof, 0 sorries, 0 axioms
- [x] Uses Mathlib's `Nat.nth` / `Nat.count` prime-enumeration API
- [x] Proves an extension/corollary of Euclid's theorem

## Mathlib Dependencies
- `Nat.nth`, `Nat.count` : the `n`-th element / counting API for predicates
- `Nat.nth_count`, `Nat.nth_le_nth`, `Nat.nth_mem_of_infinite` : `nth`/`count` glue
- `Nat.infinite_setOf_prime` : the set of primes is infinite
- `Nat.exists_prime_and_dvd` : every `n ≠ 1` has a prime divisor
- `Finset.prod_le_prod'`, `Finset.dvd_prod_of_mem` : product monotonicity / divisibility
-/

namespace InfinitudePrimesOQ06

open Nat Finset

/-- The set of primes is infinite (Mathlib's `Nat.infinite_setOf_prime`). -/
theorem primes_infinite : {p | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime

/-- The `n`-th prime, 0-indexed: `p 0 = 2`, `p 1 = 3`, `p 2 = 5`, … -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Each `p n` is prime. -/
theorem p_prime (n : ℕ) : Nat.Prime (p n) :=
  Nat.nth_mem_of_infinite primes_infinite n

@[simp] theorem p_zero : p 0 = 2 := Nat.nth_prime_zero_eq_two

/-- **Euclid recurrence.** The `(n+1)`-th prime is bounded by the Euclid number
`p₀ · p₁ ⋯ pₙ + 1`. This is the heart of the bound. -/
theorem p_succ_le_prod (n : ℕ) :
    p (n + 1) ≤ (∏ i ∈ Finset.range (n + 1), p i) + 1 := by
  -- The Euclid number and its positivity.
  have hprod_pos : 0 < ∏ i ∈ Finset.range (n + 1), p i :=
    Finset.prod_pos (fun i _ => (p_prime i).pos)
  set N := (∏ i ∈ Finset.range (n + 1), p i) + 1 with hN
  have hN1 : N ≠ 1 := by omega
  -- A prime factor `q` of the Euclid number.
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hN1
  -- `q` is not among the first `n+1` primes.
  have hq_ne : ∀ i ∈ Finset.range (n + 1), q ≠ p i := by
    intro i hi hqi
    have hdvd_prod : p i ∣ ∏ j ∈ Finset.range (n + 1), p j :=
      Finset.dvd_prod_of_mem p hi
    rw [← hqi] at hdvd_prod
    have hsub : q ∣ N - (∏ j ∈ Finset.range (n + 1), p j) := Nat.dvd_sub hq_dvd hdvd_prod
    have hone : N - (∏ j ∈ Finset.range (n + 1), p j) = 1 := by omega
    rw [hone] at hsub
    have hqle1 : q ≤ 1 := Nat.le_of_dvd one_pos hsub
    have := hq_prime.two_le
    omega
  -- Hence `count q ≥ n+1`: otherwise `q = p (count q)` would be in the list.
  have hcount : n + 1 ≤ Nat.count Nat.Prime q := by
    by_contra h
    push_neg at h
    have hmem : Nat.count Nat.Prime q ∈ Finset.range (n + 1) := Finset.mem_range.mpr h
    have heq : q = p (Nat.count Nat.Prime q) := (Nat.nth_count hq_prime).symm
    exact hq_ne _ hmem heq
  -- Strict monotonicity: `p (n+1) ≤ p (count q) = q ≤ N`.
  have h1 : p (n + 1) ≤ p (Nat.count Nat.Prime q) :=
    (Nat.nth_le_nth primes_infinite).mpr hcount
  have h2 : p (Nat.count Nat.Prime q) = q := Nat.nth_count hq_prime
  have hqN : q ≤ N := Nat.le_of_dvd (by omega) hq_dvd
  rw [h2] at h1
  omega

/-- Telescoping of exponents: `∏_{i<k} 2^(2ⁱ) = 2^(2ᵏ - 1)`. -/
theorem prod_two_pow_two_pow (n : ℕ) :
    ∏ i ∈ Finset.range n, (2 : ℕ) ^ (2 ^ i) = 2 ^ (2 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, ← pow_add]
    congr 1
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    omega

/-- **Main theorem.** The `n`-th prime satisfies `pₙ ≤ 2^(2ⁿ)`. -/
theorem nth_prime_le_double_exp (n : ℕ) : p n ≤ 2 ^ (2 ^ n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rw [p_zero]; norm_num
    | (m + 1) =>
      have hbound := p_succ_le_prod m
      -- Bound the Euclid product termwise by the inductive hypothesis.
      have hprod_le : (∏ i ∈ Finset.range (m + 1), p i) ≤ 2 ^ (2 ^ (m + 1) - 1) :=
        calc (∏ i ∈ Finset.range (m + 1), p i)
            ≤ ∏ i ∈ Finset.range (m + 1), (2 : ℕ) ^ (2 ^ i) := by
              apply Finset.prod_le_prod'
              intro i hi
              exact ih i (Finset.mem_range.mp hi)
          _ = 2 ^ (2 ^ (m + 1) - 1) := prod_two_pow_two_pow (m + 1)
      -- `2^(A-1) + 1 ≤ 2^A` since `2^A = 2·2^(A-1)`.
      have hstep : 2 ^ (2 ^ (m + 1) - 1) + 1 ≤ 2 ^ (2 ^ (m + 1)) := by
        have hpos : 0 < 2 ^ (m + 1) := pow_pos (by norm_num) (m + 1)
        have hc : 0 < 2 ^ (2 ^ (m + 1) - 1) := pow_pos (by norm_num) _
        have hdouble : 2 ^ (2 ^ (m + 1)) = 2 * 2 ^ (2 ^ (m + 1) - 1) := by
          conv_lhs => rw [show 2 ^ (m + 1) = (2 ^ (m + 1) - 1) + 1 from by omega]
          rw [pow_succ']
        omega
      calc p (m + 1)
          ≤ (∏ i ∈ Finset.range (m + 1), p i) + 1 := hbound
        _ ≤ 2 ^ (2 ^ (m + 1) - 1) + 1 := by omega
        _ ≤ 2 ^ (2 ^ (m + 1)) := hstep

/-- Restated for the prime-counting form: the bound holds for every `n`. -/
theorem exists_prime_doubly_exp_bound (n : ℕ) :
    ∃ q, Nat.Prime q ∧ (∀ k < n, p k < q) ∧ q ≤ 2 ^ (2 ^ n) :=
  ⟨p n, p_prime n,
    fun _ hk => (Nat.nth_lt_nth primes_infinite).mpr hk,
    nth_prime_le_double_exp n⟩

end InfinitudePrimesOQ06
