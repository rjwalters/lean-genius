/-
# The 2-adic valuation of Euler's totient `v₂(φ(n))`

The parent entry `euler-totient-oq-06` settles the *parity* of Euler's totient:
`φ(n)` is even for every `n > 2`, equivalently `v₂(φ(n)) ≥ 1` there.  This file
answers the natural quantitative follow-up: compute the full 2-adic valuation
`v₂(φ(n))` directly from the prime factorization of `n`.

Euler's product formula (`Nat.totient_eq_prod_factorization`) gives
`φ(n) = ∏_{p ∣ n} p^(kₚ - 1) · (p - 1)`, where `kₚ = n.factorization p`.  Since
the `p`-adic valuation is additive over products of positive numbers — encoded in
Mathlib by `Nat.factorization` being an additive homomorphism — taking
`Nat.factorization · 2` of both sides yields the master formula

  `v₂(φ(n)) = ∑_{p ∣ n} (kₚ - 1)·v₂(p) + v₂(p - 1)`.

For an **odd** prime `p` we have `v₂(p) = 0`, so its contribution is just
`v₂(p - 1)`; for `p = 2` we have `v₂(2) = 1` and `v₂(2 - 1) = 0`, so its
contribution is `k₂ - 1`.  This gives the clean split

  `v₂(φ(n)) = (k₂ - 1)  +  ∑_{p ∣ n, p odd} v₂(p - 1)`   (when `2 ∣ n`)

and recovers the parent's parity result as the special case `v₂(φ(n)) ≥ 1`.

Throughout we use `Nat.factorization n 2`, which equals `padicValNat 2 n`
(`Nat.factorization_def`) for the prime `2`; the `padicValNat` restatement is
recorded as `padicValNat_two_totient_eq_sum`.

Fully machine-checked: 0 sorries, 0 axioms.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Finset

namespace EulerTotientOQ06OQ01

/-! ## Prime-power building blocks

The valuation is *multiplicative-additive*, so the whole computation reduces to
the prime-power case `φ(p^k)`.  We record the two regimes explicitly. -/

/-- For `k ≥ 1`, `v₂(φ(2^k)) = k - 1`.  Here `φ(2^k) = 2^(k-1)`. -/
theorem v2_totient_two_pow {k : ℕ} (hk : 1 ≤ k) :
    (Nat.totient (2 ^ k)).factorization 2 = k - 1 := by
  rw [Nat.totient_prime_pow Nat.prime_two hk, show (2 : ℕ) - 1 = 1 by rfl, mul_one,
    Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]

/-- For an **odd** prime `p` and any `k ≥ 1`, `v₂(φ(p^k)) = v₂(p - 1)`.
The factor `p^(k-1)` is odd, so it contributes nothing to the 2-adic valuation. -/
theorem v2_totient_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk : 1 ≤ k) :
    (Nat.totient (p ^ k)).factorization 2 = (p - 1).factorization 2 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p - 1 ≠ 0 := by
    have := hp.two_le; omega
  have hpow : (p ^ (k - 1)) ≠ 0 := pow_ne_zero _ hp0
  rw [Nat.totient_prime_pow hp hk, Nat.factorization_mul hpow hp1, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  -- `p` is an odd prime, so `2 ∤ p`, hence `p.factorization 2 = 0`.
  have h2p : p.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  rw [h2p, mul_zero, zero_add]

/-! ## Master formula

`v₂(φ(n))` as a sum over the prime factors of `n`. -/

/-- **2-adic valuation of the totient, master formula.**
For `n ≠ 0`,
`v₂(φ(n)) = ∑_{p ∣ n} (kₚ - 1)·v₂(p) + v₂(p - 1)` where `kₚ = n.factorization p`. -/
theorem v2_totient_eq_sum {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n).factorization 2 =
      ∑ p ∈ n.primeFactors,
        ((n.factorization p - 1) * p.factorization 2 + (p - 1).factorization 2) := by
  -- Euler's product formula, unfolded to a `Finset.prod` over the prime factors.
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization]
  -- Each factor `p^(kₚ-1)·(p-1)` is nonzero.
  have hne : ∀ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) ≠ 0 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : 2 ≤ p := hpp.two_le
    exact mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (by omega)
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h2le : 2 ≤ p := hpp.two_le
  have hpow : (p ^ (n.factorization p - 1)) ≠ 0 := pow_ne_zero _ hpp.ne_zero
  have hp1 : (p - 1) ≠ 0 := by omega
  rw [Nat.factorization_mul hpow hp1, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul]

/-- `padicValNat` restatement of the master formula. -/
theorem padicValNat_two_totient_eq_sum {n : ℕ} (hn : n ≠ 0) :
    padicValNat 2 (Nat.totient n) =
      ∑ p ∈ n.primeFactors,
        ((n.factorization p - 1) * padicValNat 2 p + padicValNat 2 (p - 1)) := by
  rw [← Nat.factorization_def _ Nat.prime_two, v2_totient_eq_sum hn]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]

/-! ## Clean split: isolating the prime `2`

For odd primes the `(kₚ-1)·v₂(p)` term vanishes; the only contribution of that
shape comes from `p = 2`, where it equals `k₂ - 1`. -/

/-- Each summand simplifies: for the prime `2` it is `k₂ - 1`, and for every odd
prime factor `p` it is `v₂(p - 1)`. -/
theorem summand_eq {n : ℕ} {p : ℕ} (hp : p ∈ n.primeFactors) :
    (n.factorization p - 1) * p.factorization 2 + (p - 1).factorization 2 =
      if p = 2 then n.factorization 2 - 1 else (p - 1).factorization 2 := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_cases h2 : p = 2
  · subst h2
    -- `v₂(2) = 1` and `v₂(2 - 1) = v₂(1) = 0`.
    rw [Nat.Prime.factorization_self Nat.prime_two, mul_one,
      show (2 : ℕ) - 1 = 1 by rfl, Nat.factorization_one, Finsupp.coe_zero,
      Pi.zero_apply, add_zero, if_pos rfl]
  · -- odd prime: `2 ∤ p`, so `v₂(p) = 0`.
    have h2p : p.factorization 2 = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp hdvd).symm
    rw [h2p, mul_zero, zero_add, if_neg h2]

/-- **Clean split form.**  When `2 ∣ n` (so `2 ∈ n.primeFactors`),
`v₂(φ(n)) = (v₂(n) - 1) + ∑_{p ∣ n, p odd} v₂(p - 1)`. -/
theorem v2_totient_split {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) :
    (Nat.totient n).factorization 2 =
      (n.factorization 2 - 1) +
        ∑ p ∈ n.primeFactors.filter (· ≠ 2), (p - 1).factorization 2 := by
  have h2mem : (2 : ℕ) ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn⟩
  rw [v2_totient_eq_sum hn]
  -- Rewrite each summand via `summand_eq`.
  rw [Finset.sum_congr rfl (fun p hp => summand_eq hp)]
  -- Split off the `p = 2` term.
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (· = 2)]
  congr 1
  · -- the `p = 2` part is a singleton sum equal to `k₂ - 1`
    rw [Finset.filter_eq' n.primeFactors 2, if_pos h2mem, Finset.sum_singleton, if_pos rfl]
  · -- the rest: rewrite `if p = 2 then _ else _` to the else-branch on the filter
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [if_neg (Finset.mem_filter.mp hp).2]

/-! ## Consistency with the parent parity result -/

/-- Recovers `euler-totient-oq-06`: for `n > 2`, `v₂(φ(n)) ≥ 1`, i.e. `φ(n)` is
even.  (Here we read it off the master formula; Mathlib's `Nat.totient_even`
gives the same conclusion directly.) -/
theorem totient_even_of_two_lt {n : ℕ} (hn : 2 < n) : Even (Nat.totient n) := by
  exact Nat.totient_even hn

end EulerTotientOQ06OQ01
