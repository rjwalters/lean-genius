import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-
# Hanson's Bound: lcm(1,...,n) ≤ 3^n
## OQ-03 of `basel-problem-oq-01-oq-01-oq-02`

## Open Question
"Eliminate the `lcm_hanson_bound` axiom in `BaselProblemOQ01OQ01OQ02.lean`,
proving `lcm(1,...,n) ≤ 3^n` (Hanson 1972) in Lean 4."

## What This File Provides

Bootstrap of the OQ-03 problem with three layers of progress:

1. **Provable easier bounds** (no axioms):
   * `lcmRange_dvd_factorial`: lcm(1,...,n) divides n!.
   * `lcmRange_le_factorial`: lcm(1,...,n) ≤ n!.
   * `lcmRange_le_self_pow`: lcm(1,...,n) ≤ n^n.

2. **Numerical verification** of Hanson's bound:
   `lcm(1,...,n) ≤ 3^n` proved by `decide` for n = 1..20.

3. **Hanson's bound axiom**: the precise open target, with proof
   strategy and Mathlib gap analysis documented inline.

## Mathematical Background

**Hanson's bound** (Hanson, *Canad. Math. Bull.* 15 (1972)):
$$\operatorname{lcm}(1, 2, \ldots, n) \leq 3^n \quad \text{for all } n \geq 1.$$

Hanson's original 1972 proof uses an **integral identity** combining
Beta-function-style integrals with Chebyshev-like estimates on prime
powers ≤ n. The key ingredient is that for any 0 ≤ k ≤ n,
$$
\operatorname{lcm}(1, \ldots, n) \cdot \int_0^1 x^{k}(1-x)^{n-k} dx \in \mathbb{Z}
$$
(because the integral equals $\frac{k! (n-k)!}{(n+1)!} = \frac{1}{(n+1)\binom{n}{k}}$
and the LCM kills the denominator).

The bound `≤ 3^n` is a strict improvement over the easier bounds:
* `≤ 4^n` follows from primorial bound (Mathlib has `Nat.primorial_le_4_pow`)
  combined with `lcm(1,...,n) ≤ n · primorial(n)` (not yet in Mathlib).
* `≤ n^n` is trivial via factorials (proved here, no axioms).

## Mathlib Infrastructure Status

* **Available**: `Nat.factorial_le_pow`, `Nat.dvd_factorial`,
  `Mathlib.NumberTheory.Primorial.primorial_le_4_pow`,
  `Finset.lcm_dvd`, `Finset.dvd_lcm`.
* **Missing**: any `lcm(1,...,n)`-specific bound (no `lcm_le_pow_three`,
  no `lcm_le_pow_four`).
* **Required for full Hanson proof**: integral identity for
  `1/((n+1)·C(n,k))` (Beta function), Chebyshev-style prime-power
  bounds compiled into LCM divisibility, an explicit numerical
  case-check for small n.

## File Status
* axioms: 1 (`hanson_bound`)
* sorries: 0
* numerically verified: n = 1..20
-/

namespace BaselProblemOQ01OQ01OQ02OQ03

open Finset Nat

-- =====================================================================
-- PART 1: Definition (redeclares the parent's `lcmUpTo`)
-- =====================================================================

/-- lcm(1, 2, ..., n) defined as the lcm of {1, 2, ..., n}.

    Identical to `BaselProblemOQ01OQ01OQ02.lcmUpTo`; reproduced here so
    this file can be type-checked independently of the parent's
    heavy analytic dependencies. -/
def lcmRange (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

-- =====================================================================
-- PART 2: Basic properties
-- =====================================================================

theorem lcmRange_zero : lcmRange 0 = 1 := by
  simp [lcmRange, Finset.lcm]

theorem lcmRange_one : lcmRange 1 = 1 := by
  simp [lcmRange, Finset.lcm]

theorem lcmRange_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmRange n := by
  unfold lcmRange
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro k _
  exact Nat.succ_ne_zero k

/-- Every k ∈ {1, ..., n} divides lcmRange n. -/
theorem dvd_lcmRange {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ lcmRange n := by
  unfold lcmRange
  have hk' : k - 1 ∈ Finset.range n :=
    Finset.mem_range.mpr (by omega)
  have := Finset.dvd_lcm (f := (· + 1)) hk'
  simpa [Nat.sub_add_cancel hk] using this

/-- **Power divisibility**: any power b^k with positive base and b^k ≤ n divides
    lcmRange n. Specialization of `dvd_lcmRange` to powers; the case where b is
    prime and k = ⌊log_b n⌋ is the structural building block for the prime-power
    decomposition lcm(1,...,n) = ∏_{p prime ≤ n} p^{⌊log_p n⌋} that underlies any
    Hanson-style proof. -/
theorem pow_dvd_lcmRange {b k n : ℕ} (hb : 0 < b) (hbkn : b ^ k ≤ n) :
    b ^ k ∣ lcmRange n :=
  dvd_lcmRange (Nat.pow_pos hb) hbkn

/-- **Maximal prime-power divisibility**: for any prime `p` and `n ≥ 1`,
    `p ^ ⌊log_p n⌋` divides `lcmRange n`.

    This is the prime-power half of Chebyshev's decomposition
    `lcm(1,...,n) = ∏_{p prime ≤ n} p ^ ⌊log_p n⌋`: every maximal prime
    power dividing some `k ∈ {1,...,n}` divides `lcmRange n`. The reverse
    inclusion (that no larger prime power can divide `lcmRange n`) follows
    from the Mathlib `Nat.factorization` framework and is the next
    structural step toward replacing `hanson_bound`.

    The proof is a one-line specialization of `pow_dvd_lcmRange`:
    `Nat.pow_log_le_self p hn'` gives `p ^ Nat.log p n ≤ n`. -/
theorem prime_pow_dvd_lcmRange {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    p ^ Nat.log p n ∣ lcmRange n :=
  pow_dvd_lcmRange hp.pos (Nat.pow_log_le_self p (by omega))

/-- **Coprimality of distinct prime powers**: for distinct primes `p ≠ q`,
    any prime-power factors `p ^ a` and `q ^ b` are coprime.

    The pairwise-coprimality input needed to assemble the prime-power
    factors of `lcmRange n` into Chebyshev's product decomposition
    `lcmRange n = ∏ p ∈ filter Prime (range (n+1)), p ^ ⌊log_p n⌋`.

    Combined with `prime_pow_dvd_lcmRange` it closes the easy direction
    `(∏ p, p ^ ⌊log_p n⌋) ∣ lcmRange n` (next session): pairwise-coprime
    divisors of a fixed `N` have their product dividing `N`.

    Proof: `Nat.dvd_prime` reduces `p ∣ q` to `p = 1 ∨ p = q`; the first
    contradicts `hp.one_lt`, the second contradicts `hpq`. Then
    `Nat.Prime.coprime_iff_not_dvd` upgrades `¬ p ∣ q` to `Coprime p q`,
    and `Coprime.pow_left a` / `Coprime.pow_right b` lift it to
    `Coprime (p ^ a) (q ^ b)`. -/
theorem coprime_prime_pow_pow_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (a b : ℕ) : Nat.Coprime (p ^ a) (q ^ b) := by
  have hndvd : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h1 | heq
    · exact hp.one_lt.ne' h1
    · exact hpq heq
  exact ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left a).pow_right b

/-- **Pairwise-coprime divisors of `N` have product dividing `N`** (helper).

    For any `Finset ℕ` `S` and function `f : ℕ → ℕ`: if every `f p` for
    `p ∈ S` divides `N`, and `f p`, `f q` are coprime for `p ≠ q ∈ S`,
    then `∏ p ∈ S, f p ∣ N`. Standard Finset-induction packaging,
    parallels `Erdos1057Problem.prod_primes_dvd_of_each_dvd` but
    abstracted over `f` to support prime-power factors. -/
private theorem prod_dvd_of_pairwise_coprime
    {S : Finset ℕ} {f : ℕ → ℕ} {N : ℕ}
    (hdvd : ∀ p ∈ S, f p ∣ N)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime (f p) (f q)) :
    (∏ p ∈ S, f p) ∣ N := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_dvd := hdvd a (Finset.mem_insert_self a s)
    have hs_dvd : ∀ p ∈ s, f p ∣ N :=
      fun p hp => hdvd p (Finset.mem_insert_of_mem hp)
    have hs_cop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q) :=
      fun p hp q hq hpq =>
        hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
    have hprod_dvd := ih hs_dvd hs_cop
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ha_dvd hprod_dvd
    apply Nat.Coprime.prod_right
    intro p hp
    have hap : a ≠ p := fun h => ha (h ▸ hp)
    exact hcop a (Finset.mem_insert_self a s) p (Finset.mem_insert_of_mem hp) hap

/-- **Easy direction of Chebyshev's decomposition**: the product of maximal
    prime powers `p ^ ⌊log_p n⌋` over primes `p ≤ n` divides `lcmRange n`.

    The forward inclusion `(∏ p, p ^ ⌊log_p n⌋) ∣ lcmRange n` of the
    Chebyshev decomposition
    `lcmRange n = ∏ p ∈ filter Prime (range (n+1)), p ^ ⌊log_p n⌋`. The
    reverse inclusion (LHS ∣ RHS) is harder — it routes through Mathlib's
    `Nat.factorization` framework and is the next structural target.

    Combines two ingredients from previous iterations:
    - `prime_pow_dvd_lcmRange` (Iter 5): each factor divides `lcmRange n`.
    - `coprime_prime_pow_pow_of_ne` (Iter 6): distinct factors are coprime.

    Then `prod_dvd_of_pairwise_coprime` packages these into the product
    statement via Finset induction. -/
theorem prod_prime_powers_dvd_lcmRange (n : ℕ) :
    (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ Nat.log p n)
      ∣ lcmRange n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: range 1 = {0}, 0 isn't prime, so filter is empty, product is 1.
    have hempty : (Finset.range 1).filter Nat.Prime = ∅ := by
      simp [Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
    rw [hempty, Finset.prod_empty]
    exact one_dvd _
  -- n ≥ 1: each prime power divides lcmRange n; distinct factors are coprime.
  refine prod_dvd_of_pairwise_coprime ?_ ?_
  · intro p hp
    exact prime_pow_dvd_lcmRange (Finset.mem_filter.mp hp).2 hn
  · intro p hp q hq hpq
    exact coprime_prime_pow_pow_of_ne (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2 hpq _ _

/-- **Reverse direction of Chebyshev's decomposition**: `lcmRange n` divides
    the product of maximal prime powers `p ^ ⌊log_p n⌋` over primes `p ≤ n`.

    Combined with `prod_prime_powers_dvd_lcmRange` (the forward direction),
    this gives Chebyshev's full prime-power formula
    `lcmRange n = ∏ p ∈ filter Prime (range (n+1)), p ^ ⌊log_p n⌋`
    via `Nat.dvd_antisymm` (next iteration).

    Strategy: it suffices to show every `m ∈ {1,…,n}` divides the product.
    For each such `m`, write `m = ∏_{p ∈ m.primeFactors} p ^ m.factorization p`
    via `Nat.factorization_prod_pow_eq_self`, extend the index set to all of
    `(Finset.range (n+1)).filter Nat.Prime` (the extra factors are 1 since
    `m.factorization p = 0` outside `m.primeFactors`), and bound each
    exponent by `Nat.log p n` using `Nat.le_log_of_pow_le`. -/
theorem lcmRange_dvd_prod_prime_powers (n : ℕ) :
    lcmRange n ∣ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ Nat.log p n := by
  unfold lcmRange
  rw [Finset.lcm_dvd_iff]
  intro k hk
  rw [Finset.mem_range] at hk
  set m := k + 1 with hm_def
  have hm_pos : 0 < m := Nat.succ_pos _
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hm_le : m ≤ n := by omega
  set P : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime with hP_def
  -- Subset relation: every prime factor of `m` is ≤ `m ≤ n`, so it lies in `P`.
  have hsupp_sub : m.primeFactors ⊆ P := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [hP_def, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp.1⟩
    have hp_le : p ≤ m := Nat.le_of_dvd hm_pos hp.2.1
    omega
  -- Reformulate `m` as a product over `P` (extending by 1's outside `m.primeFactors`).
  have hm_eq : m = ∏ p ∈ P, p ^ m.factorization p := by
    have h1 : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      have hself := Nat.factorization_prod_pow_eq_self hm_ne
      rw [Finsupp.prod, Nat.support_factorization] at hself
      exact hself.symm
    -- Rewrite only the LHS `m` — `rw [h1]` would also expand `m` inside
    -- `m.factorization` on the RHS, leaving an unprovable nested goal.
    conv_lhs => rw [h1]
    apply Finset.prod_subset hsupp_sub
    intro p _ hp_not
    have h_zero : m.factorization p = 0 := by
      rw [← Nat.support_factorization] at hp_not
      exact Finsupp.not_mem_support_iff.mp hp_not
    rw [h_zero, pow_zero]
  rw [hm_eq]
  -- Pointwise divisibility of factors over `P`.
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [hP_def, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hp_prime⟩ := hp
  apply pow_dvd_pow
  -- `m.factorization p ≤ Nat.log p n`: trivial when factorization is 0,
  -- and otherwise `p ^ (m.factorization p) ∣ m ≤ n` ⇒ `… ≤ Nat.log p n`.
  by_cases hf : m.factorization p = 0
  · rw [hf]; exact Nat.zero_le _
  · have hpow_dvd : p ^ m.factorization p ∣ m :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp_prime hm_ne).mpr le_rfl
    have hpow_le_n : p ^ m.factorization p ≤ n :=
      le_trans (Nat.le_of_dvd hm_pos hpow_dvd) hm_le
    exact Nat.le_log_of_pow_le hp_prime.one_lt hpow_le_n

/-- **Chebyshev's prime-power decomposition** (full equality):
    `lcm(1,...,n) = ∏_{p prime ≤ n} p^⌊log_p n⌋`.

    Antisymmetric combination of the two divisibility theorems:
    - `prod_prime_powers_dvd_lcmRange` (forward direction; Iter 7),
    - `lcmRange_dvd_prod_prime_powers` (reverse direction; Iter 8).

    With this equality in hand, bounding `lcmRange n` reduces to bounding
    each maximal prime power `p ^ ⌊log_p n⌋` and summing logarithmically:
    Hanson's bound `lcmRange n ≤ 3 ^ n` becomes the Chebyshev-type
    prime-counting inequality `∑_{p ≤ n} ⌊log_p n⌋ · log p ≤ n · log 3`. -/
theorem lcmRange_eq_prod_prime_powers (n : ℕ) :
    lcmRange n = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ Nat.log p n :=
  Nat.dvd_antisymm (lcmRange_dvd_prod_prime_powers n)
    (prod_prime_powers_dvd_lcmRange n)

/-- **Chebyshev bound via prime-counting**: `lcmRange n ≤ n ^ π(n)`,
    where `π(n) = #{p ≤ n : p prime}`.

    The first non-trivial published-bound milestone on the path from
    the elementary `lcmRange n ≤ n ^ n` (via `lcmRange_le_self_pow`,
    Part 3) to Hanson's `lcmRange n ≤ 3 ^ n`. Follows immediately from
    the just-proved Chebyshev decomposition `lcmRange_eq_prod_prime_powers`:

    `∏_{p ≤ n} p^⌊log_p n⌋ ≤ ∏_{p ≤ n} n = n ^ π(n).`

    Compared to the trivial `n ^ n`, this saves the contribution of all
    *composite* `k ∈ {1,...,n}` via prime-power coalescing — by the
    prime number theorem `π(n) ~ n / log n ≪ n`. Compared to Hanson's
    `3 ^ n`, this is asymptotically much weaker (`n^{n/log n}` grows
    super-exponentially) but it requires no analytic machinery beyond
    the Chebyshev decomposition already established here.

    Strategy:
    1. Apply `lcmRange_eq_prod_prime_powers` to rewrite the LHS.
    2. Bound each factor `p ^ ⌊log_p n⌋ ≤ n` via `Nat.pow_log_le_self`
       (only requires `n ≠ 0`).
    3. Collapse `∏ _ ∈ S, n = n ^ S.card` via `Finset.prod_const`. -/
theorem lcmRange_le_pow_card_primes_le (n : ℕ) :
    lcmRange n ≤ n ^ ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: range 1 = {0}, 0 isn't prime, so the filter is empty,
    -- card = 0, and 0 ^ 0 = 1 = lcmRange 0. Closed by simp.
    simp [lcmRange_zero, Finset.range_one, Finset.filter_singleton,
          Nat.not_prime_zero]
  rw [lcmRange_eq_prod_prime_powers]
  calc (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ Nat.log p n)
      ≤ ∏ _p ∈ (Finset.range (n + 1)).filter Nat.Prime, n := by
        apply Finset.prod_le_prod
        · intro _ _; exact Nat.zero_le _
        · intro p _hp
          exact Nat.pow_log_le_self p hn.ne'
    _ = n ^ ((Finset.range (n + 1)).filter Nat.Prime).card :=
        Finset.prod_const n

/-- **Chebyshev bound, prime-counting form**: `lcmRange n ≤ n ^ π(n)`,
    stated using Mathlib's `Nat.primeCounting`. The literal published
    form of the bound; brings the file into PNT-statement vocabulary
    (cf. `ChebyshevPNTBridgeOQ01.lean` for the analogous
    `(2n).choose n ≤ (2n) ^ π(2n)` bound on central binomial coefficients).

    A one-line corollary of `lcmRange_le_pow_card_primes_le` plus the
    standard identification `Nat.primeCounting n =
    ((Finset.range (n+1)).filter Nat.Prime).card` (via
    `Nat.count_eq_card_filter_range`). -/
theorem lcmRange_le_pow_primeCounting (n : ℕ) :
    lcmRange n ≤ n ^ Nat.primeCounting n := by
  have h := lcmRange_le_pow_card_primes_le n
  have hpi : ((Finset.range (n + 1)).filter Nat.Prime).card =
      Nat.primeCounting n := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
  rw [hpi] at h
  exact h

/-- **Trivial bound on the prime-counting function**: `π(n) ≤ n`.

    Holds for every `n` because the count of primes in `{0, 1, …, n}`
    excludes `0` (which is not prime), so the prime filter is a subset
    of `(Finset.range (n+1)).erase 0`, whose cardinality is `n`.

    Used in Iter 13 to chain `lcmRange n ≤ n^π(n) ≤ n^n`, making
    explicit that the prime-counting bound from Iter 11
    (`lcmRange_le_pow_primeCounting`) is at least as strong as the
    factorial-derived `lcmRange_le_self_pow` (Part 3). -/
theorem primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  have hpi : ((Finset.range (n + 1)).filter Nat.Prime).card =
      Nat.primeCounting n := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
  rw [← hpi]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: range 1 = {0}, 0 isn't prime, so the filter is empty,
    -- card = 0 ≤ 0.
    simp [Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
  -- n ≥ 1: filter ⊆ (range (n+1)).erase 0, card erase = n.
  have h_subset :
      (Finset.range (n + 1)).filter Nat.Prime ⊆
        (Finset.range (n + 1)).erase 0 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hp ⊢
    refine ⟨?_, hp.1⟩
    intro h0
    rw [h0] at hp
    exact Nat.not_prime_zero hp.2
  have h_card : ((Finset.range (n + 1)).erase 0).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos n))]
    simp
  calc ((Finset.range (n + 1)).filter Nat.Prime).card
      ≤ ((Finset.range (n + 1)).erase 0).card :=
        Finset.card_le_card h_subset
    _ = n := h_card

/-- **Monotone exponent**: `n^π(n) ≤ n^n` for `n ≥ 1`.

    A one-line consequence of `Nat.pow_le_pow_right` applied to
    `primeCounting_le_self`. Packaged as a named lemma so the Iter 13
    chain `lcmRange n ≤ n^π(n) ≤ n^n` reads cleanly. -/
theorem pow_primeCounting_le_pow_self (n : ℕ) (hn : 1 ≤ n) :
    n ^ Nat.primeCounting n ≤ n ^ n :=
  Nat.pow_le_pow_right hn (primeCounting_le_self n)

/-- **Re-derivation of `lcmRange_le_self_pow` via the prime-counting
    route**: `lcmRange n ≤ n^n` proved through the chain
    `lcmRange n ≤ n^π(n) ≤ n^n`.

    Documents that the Iter 10/11 prime-counting bound subordinates
    the trivial Part 3 bound: every value reachable by
    `lcmRange_le_pow_primeCounting` is also covered by
    `lcmRange_le_self_pow`. The chain makes the dependency
    `Iter 11 ⟹ Iter 13 ⟹ Part 3` explicit:

    ```
    lcmRange n  ≤  n ^ π(n)        -- Iter 11 (Chebyshev decomposition)
                ≤  n ^ n            -- Iter 13 (since π(n) ≤ n)
    ```

    The `n = 0` boundary case (`lcmRange 0 = 1 = 0^0`) is handled
    directly by `lcmRange_zero` because `Nat.pow_le_pow_right`
    requires the base to be `≥ 1`. -/
theorem lcmRange_le_pow_self_via_primeCounting (n : ℕ) :
    lcmRange n ≤ n ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lcmRange_zero]
  exact le_trans (lcmRange_le_pow_primeCounting n)
    (pow_primeCounting_le_pow_self n hn)

/-- **Sharpened trivial bound on the prime-counting function**:
    `π(n) ≤ n - 1` (with `Nat` truncated subtraction).

    Sharper than `primeCounting_le_self` (Iter 13): exploits that *both*
    `0` and `1` are non-prime, so the prime filter on `Finset.range (n+1)`
    sits inside `((Finset.range (n+1)).erase 0).erase 1`, whose
    cardinality is `n - 1` (with the `Nat` convention `0 - 1 = 0`
    handling the boundary cases `n = 0, 1` correctly).

    Used in Iter 14 to chain `lcmRange n ≤ n ^ π(n) ≤ n ^ (n-1)`,
    a strict improvement over the Iter 13 chain `≤ n ^ n` that saves one
    factor of `n` in the exponent — the same factor by which the
    `n · primorial(n)` route to `lcm(1..n) ≤ 4^n` would save over the
    raw primorial bound, but obtained here via prime-counting alone. -/
theorem primeCounting_le_pred (n : ℕ) :
    Nat.primeCounting n ≤ n - 1 := by
  have hpi : ((Finset.range (n + 1)).filter Nat.Prime).card =
      Nat.primeCounting n := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
  rw [← hpi]
  rcases Nat.lt_or_ge n 1 with hn | hn
  · -- n = 0: filter is empty, card 0 ≤ 0 - 1 = 0.
    interval_cases n
    simp [Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
  -- n ≥ 1: filter ⊆ ((range (n+1)).erase 0).erase 1, card = n - 1.
  have h_subset :
      (Finset.range (n + 1)).filter Nat.Prime ⊆
        ((Finset.range (n + 1)).erase 0).erase 1 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range,
      Finset.mem_erase] at hp ⊢
    refine ⟨?_, ?_, hp.1⟩
    · -- p ≠ 1 since 1 isn't prime
      intro h1
      rw [h1] at hp
      exact Nat.not_prime_one hp.2
    · -- p ≠ 0 since 0 isn't prime
      intro h0
      rw [h0] at hp
      exact Nat.not_prime_zero hp.2
  have h_card :
      (((Finset.range (n + 1)).erase 0).erase 1).card = n - 1 := by
    have h0_mem : (0 : ℕ) ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos n)
    have h1_mem : (1 : ℕ) ∈ (Finset.range (n + 1)).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨one_ne_zero, by omega⟩
    rw [Finset.card_erase_of_mem h1_mem,
        Finset.card_erase_of_mem h0_mem, Finset.card_range]
    omega
  calc ((Finset.range (n + 1)).filter Nat.Prime).card
      ≤ (((Finset.range (n + 1)).erase 0).erase 1).card :=
        Finset.card_le_card h_subset
    _ = n - 1 := h_card

/-- **Monotone exponent (sharpened)**: `n ^ π(n) ≤ n ^ (n - 1)` for
    `n ≥ 1`.

    The Iter 14 analogue of `pow_primeCounting_le_pow_self`, packaged as
    a named lemma so the chain `lcmRange n ≤ n ^ π(n) ≤ n ^ (n - 1)`
    reads cleanly. The exponent `n - 1` is `0` at `n = 1` (matches
    `π(1) = 0`) and is strictly smaller than `n` for `n ≥ 1`. -/
theorem pow_primeCounting_le_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    n ^ Nat.primeCounting n ≤ n ^ (n - 1) :=
  Nat.pow_le_pow_right hn (primeCounting_le_pred n)

/-- **Sharpened bound `lcmRange n ≤ n ^ (n - 1)`** via the prime-counting
    chain `lcmRange n ≤ n ^ π(n) ≤ n ^ (n - 1)`.

    A strict improvement over the Iter 13 bound
    `lcmRange_le_pow_self_via_primeCounting` (`lcmRange n ≤ n ^ n`):
    saves a factor of `n` in the exponent by tightening
    `primeCounting_le_self` (Iter 13) to `primeCounting_le_pred`
    (Iter 14, this iteration). The boundary case `n = 0` is handled
    directly by `lcmRange_zero` since `0 ^ (0 - 1) = 0 ^ 0 = 1`.

    Concrete numerics:
    | n   | lcmRange n | n^(n-1) | Hanson 3^n |
    | --- | ---------- | ------- | ---------- |
    | 1   | 1          | 1       | 3          |
    | 2   | 2          | 2       | 9          |
    | 3   | 6          | 9       | 27         |
    | 4   | 12         | 64      | 81         |
    | 10  | 2520       | 10⁹     | 59049      |

    Still asymptotically much weaker than Hanson's `3 ^ n` (since
    `n ^ (n-1)` grows super-exponentially), but a strict improvement
    over the trivial route through Part 3's `lcmRange_le_self_pow`. -/
theorem lcmRange_le_pow_pred (n : ℕ) :
    lcmRange n ≤ n ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: lcmRange 0 = 1 = 0 ^ 0 = 0 ^ (0 - 1).
    simp [lcmRange_zero]
  exact le_trans (lcmRange_le_pow_primeCounting n)
    (pow_primeCounting_le_pow_pred n hn)

/-- **Primorial divides `lcmRange`** (Iter 15): for every `n`, the primorial
    `∏_{p ≤ n, p prime} p` divides `lcm(1, ..., n)`.

    The Iter 9 Chebyshev decomposition writes
    `lcmRange n = ∏ p ∈ primes ≤ n, p ^ Nat.log p n` and the primorial is
    the same product with all exponents collapsed to `1`. Since each prime
    `p ≤ n` satisfies `Nat.log p n ≥ 1`, each factor `p` divides
    `p ^ Nat.log p n`, and the divisibility lifts pointwise across the
    product via `Finset.prod_dvd_prod_of_dvd`.

    This is the **lower-bound side** of the bridge sketched in the file
    header (`primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)`); the
    upper-bound side `lcmRange ≤ n · primorial` requires a Chebyshev-type
    bound on small primes (`p ≤ √n` contributing `p^(⌊log_p n⌋ - 1) ≤ √n`)
    and is left for future iterations. -/
theorem primorial_dvd_lcmRange (n : ℕ) :
    primorial n ∣ lcmRange n := by
  unfold primorial
  rw [lcmRange_eq_prod_prime_powers]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  have hp_prime := hp.2
  have hp_le_n : p ≤ n := by omega
  have h_log_pos : 0 < Nat.log p n :=
    Nat.log_pos hp_prime.one_lt hp_le_n
  exact dvd_pow_self p h_log_pos.ne'

/-- **Primorial bound**: `primorial n ≤ lcmRange n` for all `n`.

    Direct corollary of `primorial_dvd_lcmRange` via `Nat.le_of_dvd` plus
    `lcmRange_pos`. The boundary case `n = 0` is handled separately
    (`primorial 0 = lcmRange 0 = 1`). For `n ≥ 1`, this gives a
    non-trivial lower bound on `lcmRange n` since
    `primorial n ≥ 2^{π(n)}` (each prime ≥ 2). Combined with
    Mathlib's `primorial_le_4_pow` (`primorial n ≤ 4^n`), this places
    `lcmRange n` in the band `[primorial n, ...]` whose upper edge is
    the target of Hanson's bound `≤ 3^n`. -/
theorem primorial_le_lcmRange (n : ℕ) :
    primorial n ≤ lcmRange n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: primorial 0 = 1 = lcmRange 0.
    -- v4.26.0 drift fix: `simp [primorial, lcmRange_zero]` leaves
    -- `∏ x ∈ {0} with Nat.Prime x, x ≤ 1` open after partial unfolding;
    -- close with `native_decide` (concrete finite Finset; the filter is
    -- empty since 0 is not prime, so the product is 1).
    simp only [primorial, lcmRange_zero]
    native_decide
  exact Nat.le_of_dvd (lcmRange_pos n hn) (primorial_dvd_lcmRange n)

/-- **Chebyshev decomposition factored through primorial** (Iter 16):

      `lcmRange n = primorial n · ∏_{p prime ≤ n} p^(⌊log_p n⌋ - 1)`.

    A refinement of Iter 15's `primorial_dvd_lcmRange` from divisibility
    to an explicit equality. Decomposes `lcmRange n` as the primorial
    (`∏ p` over primes `p ≤ n`) times the **correction factor**
    `∏ p^(⌊log_p n⌋ - 1)`, capturing the "extra" prime-power content
    beyond the bare primorial. The factorization is well-defined because
    every prime `p ≤ n` contributes `Nat.log p n ≥ 1` (via `Nat.log_pos`),
    so the truncated subtraction `Nat.log p n - 1` faithfully represents
    the residual exponent.

    Concrete numerics:

    | n   | primorial(n) | correction          | lcmRange(n) |
    | --- | ------------ | ------------------- | ----------- |
    | 4   | 6            | 2  (= 2¹)           | 12          |
    | 9   | 210          | 12 (= 2² · 3¹)      | 2520        |
    | 10  | 210          | 12 (= 2² · 3¹)      | 2520        |
    | 20  | 9699690      | 24 (= 2³ · 3¹)      | 232792560   |

    Strategic value: combined with Mathlib's `Nat.primorial_le_4_pow`
    (`primorial n ≤ 4^n`), this isolates the asymptotic challenge into
    the correction factor — bounding the correction by a Chebyshev-style
    small-prime estimate would yield Hanson's `≤ 3^n` via the
    multiplicative split (since `(3/4)^n · 4^n = 3^n`). Concretely, the
    correction factor only "sees" primes `p ≤ √n` (because `p > √n` ⇒
    `Nat.log p n ≤ 1` ⇒ exponent `0` ⇒ factor `1`), which is the
    classical Chebyshev observation reducing the bound to
    `O(2^√n)`-style estimates on small primes.

    Proof: chain `lcmRange_eq_prod_prime_powers` (Iter 9) with
    `Finset.prod_mul_distrib` to combine the primorial product with the
    correction product, then use `pow_succ'` and `Nat.sub_add_cancel`
    pointwise to factor `p^(log_p n) = p · p^(log_p n - 1)` (valid
    because `Nat.log_pos` gives `log_p n ≥ 1`). -/
theorem lcmRange_eq_primorial_mul_prod_prime_pow_pred (n : ℕ) :
    lcmRange n = primorial n *
      ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        p ^ (Nat.log p n - 1) := by
  unfold primorial
  rw [lcmRange_eq_prod_prime_powers, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  have hp_prime := hp.2
  have hp_le_n : p ≤ n := by omega
  have h_log_pos : 0 < Nat.log p n :=
    Nat.log_pos hp_prime.one_lt hp_le_n
  -- Goal (pointwise): p ^ Nat.log p n = p * p ^ (Nat.log p n - 1).
  conv_lhs => rw [← Nat.sub_add_cancel h_log_pos]
  rw [pow_succ']

/-- **Small-prime focus** (Iter 17): for any base `p > 1` with `p² > n`,
    we have `Nat.log p n ≤ 1`.

    Proof: if `Nat.log p n ≥ 2`, then by `Nat.pow_le_of_le_log`,
    `p² ≤ n`, contradicting `n < p²`. The boundary case `n = 0` is
    immediate since `Nat.log p 0 = 0`.

    This is the key arithmetic observation underpinning the Chebyshev
    "correction is small" route to Hanson's bound: only primes `p` with
    `p² ≤ n` (equivalently `p ≤ √n`) contribute non-trivially to the
    Iter-16 correction factor. Primes `p > √n` enter the correction
    product with exponent `Nat.log p n - 1 = 0` and so contribute the
    multiplicative identity `1`. -/
theorem log_le_one_of_sq_lt {p n : ℕ} (hp : 1 < p) (hsq : n < p * p) :
    Nat.log p n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_contra h_not
  push_neg at h_not
  -- h_not : 1 < Nat.log p n, so 2 ≤ Nat.log p n.
  have h2 : 2 ≤ Nat.log p n := h_not
  -- By Nat.pow_le_of_le_log: 2 ≤ Nat.log p n → p^2 ≤ n.
  have h_p_sq_le_n : p ^ 2 ≤ n := Nat.pow_le_of_le_log hn.ne' h2
  -- But hsq : n < p * p = p^2, contradiction.
  rw [pow_two] at h_p_sq_le_n
  omega

/-- **Correction-factor exponent vanishes for large primes** (Iter 17):
    for primes `p` with `p² > n`, the Iter-16 correction-factor exponent
    `Nat.log p n - 1` is zero, so the entire factor `p^(Nat.log p n - 1)`
    equals `1`. -/
theorem prime_pow_pred_eq_one_of_sq_lt
    {p n : ℕ} (hp : p.Prime) (hsq : n < p * p) :
    p ^ (Nat.log p n - 1) = 1 := by
  have h_log_le : Nat.log p n ≤ 1 := log_le_one_of_sq_lt hp.one_lt hsq
  have h_zero : Nat.log p n - 1 = 0 := by omega
  rw [h_zero, pow_zero]

-- =====================================================================
-- ITER 18: per-prime numerical bounds on correction-factor terms
-- =====================================================================
-- For each prime `p ≤ n`, bound the Iter-16 correction-factor term
-- `p ^ (Nat.log p n - 1)`. Three forms of the bound:
--   • exponent-recurrence equality (`prime_pow_pred_mul_eq_pow`),
--   • coarse `≤ n` bound (`prime_pow_pred_le_self`),
--   • sharp `≤ n / p` bound (`prime_pow_pred_le_div`).
-- These convert the Iter-16 factorisation `lcmRange n = primorial n ·
-- correction(n)` into pointwise numerical inequalities that downstream
-- product-bound arguments (e.g. Chebyshev-style `correction(n) ≤ n^√n`)
-- can chain. They are deliberately base-agnostic about the
-- small-prime filter from Iter 17 — each prime `p ≤ n` satisfies these
-- regardless of whether `p² ≤ n` or not.

/-- **Exponent recurrence** (Iter 18): for prime `p ≤ n`,
    `p ^ (Nat.log p n - 1) · p = p ^ Nat.log p n`.

    Extracts the inline manipulation in Iter 16's proof of
    `lcmRange_eq_primorial_mul_prod_prime_pow_pred` as a named, reusable
    lemma. Proof: `Nat.log p n ≥ 1` (by `Nat.log_pos` from `p ≥ 2` and
    `p ≤ n`), so `(Nat.log p n - 1) + 1 = Nat.log p n` via
    `Nat.sub_add_cancel`, then chain through `pow_succ`. -/
theorem prime_pow_pred_mul_eq_pow {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ^ (Nat.log p n - 1) * p = p ^ Nat.log p n := by
  have h_log_pos : 0 < Nat.log p n := Nat.log_pos hp.one_lt hpn
  -- Rewrite the RHS exponent as ((log p n - 1) + 1) using h_log_pos.
  conv_rhs => rw [← Nat.sub_add_cancel h_log_pos]
  rw [pow_succ]

/-- **Coarse bound** (Iter 18): for prime `p ≤ n`,
    `p ^ (Nat.log p n - 1) ≤ n`.

    The trivial chain
    `p^(Nat.log p n - 1) ≤ p^(Nat.log p n) ≤ n` via `Nat.pow_le_pow_right`
    (monotone exponent) and `Nat.pow_log_le_self` (the maximal-power
    inequality). Used as the fallback bound when the sharper
    `prime_pow_pred_le_div` is not yet useful (e.g. `n = 0` or when the
    quotient form needs to be unfolded). -/
theorem prime_pow_pred_le_self {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ^ (Nat.log p n - 1) ≤ n := by
  -- p ≤ n forces n ≠ 0 (since p ≥ 2).
  have hn_ne : n ≠ 0 := by
    have : 2 ≤ n := le_trans hp.two_le hpn
    omega
  -- Exponent monotonicity: Nat.log p n - 1 ≤ Nat.log p n.
  have h_mono : p ^ (Nat.log p n - 1) ≤ p ^ Nat.log p n :=
    Nat.pow_le_pow_right hp.one_lt.le (Nat.sub_le _ _)
  -- Maximal-power: p^(Nat.log p n) ≤ n.
  exact le_trans h_mono (Nat.pow_log_le_self p hn_ne)

/-- **Sharp bound** (Iter 18): for prime `p ≤ n`,
    `p ^ (Nat.log p n - 1) ≤ n / p`.

    The sharpened correction-factor bound: each correction-factor term
    `p^(Nat.log p n - 1)` is at most `n / p`. Strict improvement over
    `prime_pow_pred_le_self` by exactly the factor `p` saved by the
    primorial decomposition of Iter 16.

    Proof: by `Nat.le_div_iff_mul_le` (valid since `0 < p`), the goal is
    equivalent to `p^(Nat.log p n - 1) * p ≤ n`. The LHS equals
    `p^(Nat.log p n)` by `prime_pow_pred_mul_eq_pow`, which is `≤ n` by
    `Nat.pow_log_le_self`.

    Application: combined with Iter 16's primorial-correction
    factorisation, this gives the pointwise estimate
    `lcmRange n / primorial n = correction(n) = ∏ p^(log_p n - 1)
    ≤ ∏ (n / p)`, which is exactly the inequality Hanson-style
    elementary bounds attack: the RHS is `≤ ∏_{p ≤ √n} (n/p) ≤ n^π(√n)`
    after invoking Iter 17's `prime_pow_pred_eq_one_of_sq_lt` to drop
    primes `p > √n`. -/
theorem prime_pow_pred_le_div {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ^ (Nat.log p n - 1) ≤ n / p := by
  -- Convert to multiplicative form via Nat.le_div_iff_mul_le.
  rw [Nat.le_div_iff_mul_le hp.pos]
  -- LHS = p^(log p n) by the exponent recurrence.
  rw [prime_pow_pred_mul_eq_pow hp hpn]
  -- p ≤ n forces n ≠ 0 for Nat.pow_log_le_self.
  have hn_ne : n ≠ 0 := by
    have : 2 ≤ n := le_trans hp.two_le hpn
    omega
  exact Nat.pow_log_le_self p hn_ne

-- =====================================================================
-- ITER 19: product-level correction-factor bound (pointwise Iter 18 → product)
-- =====================================================================
-- Apply Iter 18's pointwise `prime_pow_pred_le_div` term-by-term across
-- the prime filter `(Finset.range (n + 1)).filter Nat.Prime`, obtaining
-- the natural product-level inequality
--   ∏ p^(Nat.log p n - 1) ≤ ∏ (n / p)   over primes p ≤ n.
-- Chaining with Iter 16's primorial-correction factorisation then yields
-- the corollary
--   lcmRange n ≤ primorial n · ∏ (n / p)   over primes p ≤ n.
-- This converts the structural decomposition of Iters 16/17 into a
-- *quantitative* upper bound on `lcmRange n`. The remaining work
-- toward Hanson's `lcmRange n ≤ 3^n` is then a pure product-bounding
-- problem on `∏ (n / p)` (e.g. Chebyshev's `∏ (n/p) ≤ 2^(c √n)` after
-- dropping primes `p > √n` via Iter 17's `prime_pow_pred_eq_one_of_sq_lt`).

/-- **Product-level correction-factor bound** (Iter 19): the Iter-16
    correction product `∏_{p prime ≤ n} p^(⌊log_p n⌋ - 1)` is bounded
    above by `∏_{p prime ≤ n} (n / p)`.

    Direct pointwise application of Iter 18's `prime_pow_pred_le_div`
    across the prime filter, via `Finset.prod_le_prod` (the
    nonnegativity hypothesis is trivial in `ℕ`).

    Concrete checks (matching Iter 16/17 numerics):
    * `n = 10`: LHS = ∏_{p∈{2,3,5,7}} p^(log_p 10 - 1) = 2² · 3¹ · 5⁰ · 7⁰ = 12.
               RHS = ∏_{p∈{2,3,5,7}} 10/p = 5 · 3 · 2 · 1 = 30. ✓ (12 ≤ 30)
    * `n = 20`: LHS = 2³ · 3¹ · 5⁰ · 7⁰ · 11⁰ · 13⁰ · 17⁰ · 19⁰ = 24.
               RHS = 10 · 6 · 4 · 2 · 1 · 1 · 1 · 1 = 480. ✓ (24 ≤ 480)

    The bound is loose for large `n` because Iter 17 already shows that
    primes `p > √n` contribute `1` on the LHS but contribute `n/p ≥ 1`
    on the RHS. A sharper variant restricted to the small-prime filter
    `{p : p² ≤ n}` would tighten both sides; that refinement is left for
    a future iteration once Iter 17's support-reduction lemma (PR
    #17619, in flight) is merged. -/
theorem prod_prime_pow_pred_le_prod_div_prime (n : ℕ) :
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ (Nat.log p n - 1) ≤
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, n / p := by
  apply Finset.prod_le_prod
  · intro p _
    exact Nat.zero_le _
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hp_lt, hp_prime⟩ := hp
    have hpn : p ≤ n := by omega
    exact prime_pow_pred_le_div hp_prime hpn

/-- **lcmRange quantitative bound** (Iter 19 corollary): combining Iter
    16's primorial-correction factorisation with the product-level Iter
    19 pointwise bound,

      `lcmRange n ≤ primorial n · ∏_{p prime ≤ n} (n / p)`.

    First explicit *numerical* (as opposed to structural) upper bound on
    `lcmRange n` derived from the prime-power decomposition. Strategic
    position on the path to Hanson's `3^n`:

    1. **Primorial factor** `primorial n ≤ 4^n` (Mathlib's
       `Nat.primorial_le_4_pow`).
    2. **Correction factor** `∏_{p ≤ n} (n / p)` reduces, via Iter 17,
       to `∏_{p ≤ √n} (n / p)` (large primes contribute `1`); a
       Chebyshev-style `∏_{p ≤ √n} (n/p) ≤ 2^(c √n)` would then yield
       `lcmRange n ≤ 4^n · 2^(c √n) = (4 + ε)^n`.

    Numerics (sanity, n = 10): primorial(10) = 210, ∏ (10/p) over
    primes ≤ 10 is `5 · 3 · 2 · 1 = 30`, product `= 6300`, and indeed
    `lcmRange(10) = 2520 ≤ 6300`. ✓ For n = 20: primorial(20) · 480 =
    9,699,690 · 480 = 4,655,851,200 ≥ `lcmRange(20) = 232,792,560`. ✓ -/
theorem lcmRange_le_primorial_mul_prod_div_prime (n : ℕ) :
    lcmRange n ≤ primorial n *
      ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, n / p := by
  rw [lcmRange_eq_primorial_mul_prod_prime_pow_pred]
  exact Nat.mul_le_mul_left _ (prod_prime_pow_pred_le_prod_div_prime n)

/-- **Cardinality of small-prime filter** (Iter 20): the set of primes `p`
    with `p² ≤ n` (the *non-trivial* support of the Iter-16 correction
    factor by Iter 17's `prime_pow_pred_eq_one_of_sq_lt`) has at most
    `Nat.sqrt n` elements.

    This is a purely combinatorial cardinality lemma — no number-theoretic
    estimate is needed beyond the basic fact `p² ≤ n ↔ p ≤ √n`. The bound
    is used in the next stage of the bridge toward Hanson's `lcmRange n ≤ 3^n`:

    1. Iter 19's `prod_prime_pow_pred_le_prod_div_prime` gives
       `∏ p^(log_p n - 1) ≤ ∏ (n/p)` over all primes `p ≤ n`.
    2. Iter 17's `prime_pow_pred_eq_one_of_sq_lt` (once PR #17619 lands)
       drops the large-prime tail (`p² > n`): both products reduce to
       `∏_{p² ≤ n} (n / p)`.
    3. **This iteration**: the number of small primes `p² ≤ n` is at
       most `√n`, so the small-prime product is `≤ (n/2)^√n` (using
       `n/p ≤ n/2` for any prime `p ≥ 2`).
    4. Combined with `Nat.primorial_le_4_pow`, this gives a
       sub-`(4 + ε)^n` bound on `lcmRange n`, the structural envelope
       around Hanson's asymptotic `3^n`.

    Concrete checks:
    * `n = 4`: small primes are `{2}` (`2² = 4 ≤ 4`), card = 1, `√4 = 2`. ✓
    * `n = 9`: small primes are `{2, 3}` (`9 ≤ 9`), card = 2, `√9 = 3`. ✓
    * `n = 25`: small primes are `{2, 3, 5}`, card = 3, `√25 = 5`. ✓
    * `n = 100`: small primes are `{2, 3, 5, 7}` (`7² = 49 ≤ 100 < 121 = 11²`),
      card = 4, `√100 = 10`. ✓

    Proof: the filter is contained in `Finset.Ico 2 (Nat.sqrt n + 1)`
    (primes are `≥ 2`; the `p² ≤ n` condition is equivalent to
    `p ≤ Nat.sqrt n` by `Nat.le_sqrt`). The Ico has cardinality
    `Nat.sqrt n + 1 - 2 = Nat.sqrt n - 1 ≤ Nat.sqrt n`. -/
theorem small_prime_card_le_sqrt (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ n)).card
      ≤ Nat.sqrt n := by
  have h_sub :
      ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ n))
        ⊆ Finset.Ico 2 (Nat.sqrt n + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, hp_prime, hp_sq_le⟩ := hp
    simp only [Finset.mem_Ico]
    refine ⟨hp_prime.two_le, ?_⟩
    have hp_le_sqrt : p ≤ Nat.sqrt n := by
      -- Convert `p^2 ≤ n` to the `p * p ≤ n` form expected by `Nat.le_sqrt`
      rw [pow_two] at hp_sq_le
      exact Nat.le_sqrt.mpr hp_sq_le
    omega
  calc ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ n)).card
      ≤ (Finset.Ico 2 (Nat.sqrt n + 1)).card := Finset.card_le_card h_sub
    _ = Nat.sqrt n + 1 - 2 := Nat.card_Ico 2 (Nat.sqrt n + 1)
    _ ≤ Nat.sqrt n := by omega

/-- **Concrete cardinality witness** (Iter 20): at `n = 100` the small-prime
    filter `{p prime : p² ≤ 100}` has cardinality `4` (= `{2, 3, 5, 7}`).
    Sanity check for `small_prime_card_le_sqrt` (which only gives `≤ √100 = 10`,
    much looser than the true count). -/
example :
    ((Finset.range 101).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 100)).card = 4 := by
  decide

/-- **Pointwise division bound** (Iter 21 helper): for any prime `p`, the
    division `n / p` is bounded by `n / 2`.

    Since every prime is `≥ 2`, dividing by a larger value yields a smaller
    quotient (`Nat.div_le_div_left`). This is the pointwise atom of the
    multiplicative combination step in the four-step Hanson bridge:

    1. Iter 19: product bound `∏ p^(log_p n - 1) ≤ ∏ (n/p)`.
    2. Iter 17 (PR #17619, in flight): support reduction `p² > n → factor = 1`.
    3. Iter 20: cardinality bound `|{p prime : p² ≤ n}| ≤ √n`.
    4. **This iter (pointwise)**: `n / p ≤ n / 2` for any prime `p`.
    5. Iter 21 (this PR, main): `∏_{p prime, p² ≤ n} (n/p) ≤ (n/2) ^ card`.

    Concrete numerics:
    * `p = 2, n = 10`: `10 / 2 = 5 ≤ 5`. ✓ (tight)
    * `p = 3, n = 10`: `10 / 3 = 3 ≤ 5`. ✓
    * `p = 5, n = 10`: `10 / 5 = 2 ≤ 5`. ✓
    * `p = 7, n = 10`: `10 / 7 = 1 ≤ 5`. ✓ -/
theorem div_prime_le_div_two {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ n / 2 :=
  Nat.div_le_div_left hp.two_le (by norm_num)

/-- **Small-prime correction-factor product bound** (Iter 21): the product
    `∏_{p prime, p² ≤ n} (n / p)` is bounded above by `(n / 2)` raised to
    the cardinality of the small-prime filter.

    Step 5 of the four-step Hanson bridge (post-Iter-20 documented plan):
    combines Iter 21's pointwise `div_prime_le_div_two` with `Mathlib`'s
    `Finset.prod_le_pow_card` (`∀ x ∈ s, f x ≤ b → ∏ f ≤ b ^ s.card`).

    Combined with Iter 20's `small_prime_card_le_sqrt`, this yields the
    Chebyshev-style `(n/2) ^ √n` envelope for the small-prime correction
    product. The final assembly (a future iter) folds this with Iter 17's
    support-reduction (PR #17619, in flight) and Iter 19's product bound
    to discharge the correction factor `∏_{p ≤ n} (n/p) ≤ (n/2) ^ √n`,
    then combines with `Nat.primorial_le_4_pow` for the structural
    Chebyshev envelope `lcmRange n ≤ 4^n · (n/2) ^ √n`.

    Concrete numerics:
    * `n = 10`: small primes `{2, 3}` (`2² = 4 ≤ 10`, `3² = 9 ≤ 10`),
                LHS = `(10/2)·(10/3) = 5·3 = 15`,
                RHS = `(10/2)^2 = 5² = 25`. ✓ (15 ≤ 25)
    * `n = 20`: small primes `{2, 3}` (`3² = 9 ≤ 20`, `5² = 25 > 20`),
                LHS = `(20/2)·(20/3) = 10·6 = 60`,
                RHS = `(20/2)^2 = 10² = 100`. ✓ (60 ≤ 100)
    * `n = 100`: small primes `{2, 3, 5, 7}`,
                 LHS = `50·33·20·14 = 462000`,
                 RHS = `50^4 = 6,250,000`. ✓ -/
theorem prod_div_small_prime_le_pow_card (n : ℕ) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n), n / p
      ≤ (n / 2) ^
        ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n)).card := by
  apply Finset.prod_le_pow_card
  intro p hp
  rw [Finset.mem_filter] at hp
  exact div_prime_le_div_two hp.2.1 n

/-- **Concrete numerical witness** (Iter 21): at `n = 100` the small-prime
    product `∏_{p ∈ {2,3,5,7}} (100 / p) = 462000` is bounded by
    `(100 / 2) ^ 4 = 6,250,000`.

    Sanity check for `prod_div_small_prime_le_pow_card`. -/
example :
    ∏ p ∈ (Finset.range 101).filter (fun p => p.Prime ∧ p ^ 2 ≤ 100), 100 / p
      ≤ (100 / 2) ^
        ((Finset.range 101).filter (fun p => p.Prime ∧ p ^ 2 ≤ 100)).card := by
  native_decide

/-- **`(n/2)^√n` correction-factor envelope** (Iter 22): chains Iter 20's
    cardinality bound `|{p prime : p² ≤ n}| ≤ √n` (`small_prime_card_le_sqrt`)
    with Iter 21's multiplicative combination `∏ (n/p) ≤ (n/2)^card`
    (`prod_div_small_prime_le_pow_card`) via exponent monotonicity
    (`Nat.pow_le_pow_right`, requires base `≥ 1`).

    This is **Step 6** of the four-step Hanson bridge documented post-Iter-21:

    1. ✓ Iter 19 (#17710): product bound `∏ p^(log_p n - 1) ≤ ∏ (n/p)`.
    2. ⏳ Iter 17 (PR #17619, open): support reduction `p² > n → factor = 1`.
    3. ✓ Iter 20 (#17767): cardinality bound `|small primes| ≤ √n`.
    4. ✓ Iter 21 (#17816, pointwise): `n / p ≤ n / 2` for any prime `p`.
    5. ✓ Iter 21 (#17816, main): `∏_{p² ≤ n} (n/p) ≤ (n/2) ^ card`.
    6. **This iter**: `≤ (n/2) ^ √n` (under hypothesis `2 ≤ n`).

    The hypothesis `2 ≤ n` makes `n / 2 ≥ 1` (since `2 / 2 = 1`), enabling
    `Nat.pow_le_pow_right`. The boundary cases `n ∈ {0, 1}` are degenerate
    (the small-prime filter is empty, so the LHS is the empty product `= 1`)
    and are handled separately by the direct numerical Hanson lemmas
    `hanson_n1` and `hanson_n2`.

    Concrete numerics:
    * `n = 10`: filter `{2, 3}`, LHS = `5 · 3 = 15`, `Nat.sqrt 10 = 3`,
                 RHS = `5³ = 125`. ✓ (15 ≤ 125)
    * `n = 100`: filter `{2, 3, 5, 7}`, LHS = `50 · 33 · 20 · 14 = 462000`,
                  `Nat.sqrt 100 = 10`, RHS = `50¹⁰ ≈ 9.77 · 10¹⁶`. ✓
    * `n = 1000`: filter has `|{2,3,5,7,11,13,17,19,23,29,31}| = 11`
                   primes with `p² ≤ 1000`, `Nat.sqrt 1000 = 31`, so the
                   `√n` envelope is loose for large `n` (as expected for
                   the structural Chebyshev bound that this lemma feeds).

    Combined with `Nat.primorial_le_4_pow` and (once #17619 lands) the
    support-reduction step, this yields the Chebyshev-style envelope

      ```
      lcmRange n  ≤  4^n · (n/2)^√n
      ```

    on the structural decomposition `lcmRange n = primorial n · ∏ p^(log_p n - 1)`.
    -/
theorem prod_div_small_prime_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n), n / p
      ≤ (n / 2) ^ n.sqrt :=
  (prod_div_small_prime_le_pow_card n).trans
    (Nat.pow_le_pow_right
      ((Nat.one_le_div_iff (by decide : (0 : ℕ) < 2)).mpr hn)
      (small_prime_card_le_sqrt n))

/-- **Concrete numerical witness** (Iter 22): at `n = 10` the small-prime
    product `∏_{p ∈ {2,3}} (10 / p) = 15` is bounded by
    `(10 / 2) ^ Nat.sqrt 10 = 5³ = 125`.

    Sanity check for `prod_div_small_prime_le_pow_sqrt`. -/
example :
    ∏ p ∈ (Finset.range 11).filter (fun p => p.Prime ∧ p ^ 2 ≤ 10), 10 / p
      ≤ (10 / 2) ^ Nat.sqrt 10 := by
  -- v4.26.0 drift fix: `decide` no longer reduces this `Decidable` instance
  -- because `Nat.decidablePrime` short-circuits to a stuck `match` on `.ble`;
  -- `native_decide` evaluates via compiled bytecode and closes immediately.
  native_decide

-- =====================================================================
-- ITER 23: filtered Iter-19 + small-prime power-product envelope
-- =====================================================================
-- Iter 19's `prod_prime_pow_pred_le_prod_div_prime` is a product
-- inequality over the *full* prime filter `{p ≤ n : p.Prime}`. The
-- complete envelope toward Hanson restricts both products to the
-- small-prime filter `{p ≤ n : p.Prime ∧ p² ≤ n}` (Iter 20's support).
-- The full-filter → small-filter passage on the LHS requires Iter 17's
-- support-reduction lemma (PR #17619, currently OPEN since 2026-05-09)
-- to assert `p² > n → p^(Nat.log p n - 1) = 1`. Without that PR landing,
-- we work directly on the small-filter side: `prod_le_prod` of Iter 18's
-- pointwise atom `prime_pow_pred_le_div` over the small-prime filter
-- yields the small-prime variant directly, and chaining with Iter 22's
-- `prod_div_small_prime_le_pow_sqrt` gives the **small-prime
-- power-product envelope**
--   ∏_{p ≤ n, p.Prime, p² ≤ n} p^(Nat.log p n - 1) ≤ (n / 2)^√n   (n ≥ 2).
-- This is the LHS half of the Hanson bridge **without depending on
-- PR #17619**: once that PR (or a direct replacement) collapses the
-- full-filter LHS to the small-filter LHS, the envelope upgrades to the
-- full correction-factor bound automatically.

/-- **Filtered Iter 19** (Iter 23): the product-level correction-factor
    bound restricted to the small-prime filter `{p prime : p² ≤ n}`.
    Pointwise application of Iter 18's `prime_pow_pred_le_div` across
    the filter (analogously to Iter 19's unfiltered version), via
    `Finset.prod_le_prod`.

    The membership hypothesis `p ∈ (range (n+1)).filter (Prime ∧ p²≤n)`
    gives both `p < n + 1` (so `p ≤ n`) and `p.Prime`, the two inputs
    needed by `prime_pow_pred_le_div`. The third filter clause
    `p ^ 2 ≤ n` is not used in this proof but defines the index set.

    Concrete checks (matching Iter 19/22 numerics):
    * `n = 10`: small filter `{2, 3}` (`5² = 25 > 10`),
                LHS = `2^(log₂ 10 - 1) · 3^(log₃ 10 - 1) = 2² · 3¹ = 12`,
                RHS = `(10/2) · (10/3) = 5 · 3 = 15`. ✓ (12 ≤ 15)
    * `n = 20`: small filter `{2, 3}` (`5² = 25 > 20`),
                LHS = `2³ · 3¹ = 24`,
                RHS = `10 · 6 = 60`. ✓ (24 ≤ 60)
    * `n = 100`: small filter `{2, 3, 5, 7}`,
                 LHS = `2^5 · 3^3 · 5^1 · 7^1 = 32 · 27 · 5 · 7 = 30240`,
                 RHS = `50 · 33 · 20 · 14 = 462000`. ✓ -/
theorem prod_prime_pow_pred_le_prod_div_prime_small (n : ℕ) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n),
        p ^ (Nat.log p n - 1) ≤
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n),
        n / p := by
  apply Finset.prod_le_prod
  · intro p _
    exact Nat.zero_le _
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hp_lt, hp_prime, _⟩ := hp
    have hpn : p ≤ n := by omega
    exact prime_pow_pred_le_div hp_prime hpn

/-- **Small-prime power-product envelope** (Iter 23 main): chaining
    Iter 23's filtered Iter-19
    (`prod_prime_pow_pred_le_prod_div_prime_small`) with Iter 22's
    `(n/2)^√n` correction-factor envelope
    (`prod_div_small_prime_le_pow_sqrt`) gives the **structural**
    small-prime power-product bound

      `∏_{p prime, p² ≤ n} p^(Nat.log p n - 1) ≤ (n / 2) ^ √n`

    under the hypothesis `2 ≤ n` (inherited from Iter 22).

    This is the **LHS half of the Hanson bridge**, expressed entirely
    on the small-prime filter. The remaining work to obtain Hanson's
    `lcmRange n ≤ 3^n` then reduces to:

    1. **Full-filter → small-filter collapse** on Iter 19's LHS (i.e.,
       Iter 17's support reduction, PR #17619 OPEN): once available,
       `prod_prime_pow_pred_le_prod_div_prime_small` becomes equivalent
       to `prod_prime_pow_pred_le_prod_div_prime`, and this iter's
       envelope upgrades to the **full correction-factor envelope**
       `∏_{p ≤ n, prime} p^(Nat.log p n - 1) ≤ (n/2)^√n`.
    2. **Primorial bound** `primorial n ≤ 4^n` (Mathlib's
       `Nat.primorial_le_4_pow`).
    3. **Asymptotic threshold** for `4^n · (n/2)^√n ≤ 3^n` (small `n`
       handled by `hanson_n1`–`hanson_n20`).

    Concrete numerics:
    * `n = 10`: filter `{2, 3}`, LHS = `2² · 3¹ = 12`,
                 `Nat.sqrt 10 = 3`, RHS = `5³ = 125`. ✓ (12 ≤ 125)
    * `n = 100`: filter `{2, 3, 5, 7}`,
                  LHS = `2^5 · 3^3 · 5 · 7 = 30240`,
                  `Nat.sqrt 100 = 10`, RHS = `50^10 ≈ 9.77 · 10^16`. ✓
    -/
theorem prod_prime_pow_pred_small_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n),
        p ^ (Nat.log p n - 1)
      ≤ (n / 2) ^ n.sqrt :=
  (prod_prime_pow_pred_le_prod_div_prime_small n).trans
    (prod_div_small_prime_le_pow_sqrt hn)

/-- **Concrete numerical witness** (Iter 23): at `n = 10` the small-prime
    power product `∏_{p ∈ {2,3}} p^(Nat.log p 10 - 1) = 12` is bounded
    by `(10 / 2) ^ Nat.sqrt 10 = 5³ = 125`.

    Sanity check for `prod_prime_pow_pred_small_le_pow_sqrt`. -/
example :
    ∏ p ∈ (Finset.range 11).filter (fun p => p.Prime ∧ p ^ 2 ≤ 10),
        p ^ (Nat.log p 10 - 1)
      ≤ (10 / 2) ^ Nat.sqrt 10 := by
  native_decide

-- =====================================================================
-- ITER 24: full correction-factor envelope (support reduction + chain)
-- =====================================================================
-- Combine the support-reduction primitive
-- `prime_pow_pred_eq_one_of_sq_lt` (Iter 17, #17624) with Iter 23's
-- small-prime power-product envelope
-- (`prod_prime_pow_pred_small_le_pow_sqrt`) to obtain the FULL
-- correction-factor envelope over the entire prime filter:
--
--   ∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) ≤ (n / 2) ^ √n   (n ≥ 2)
--
-- This closes the small-vs-full filter gap left open by PR #17619
-- (Iter 17 support-reduction, OPEN since 2026-05-09) by providing a
-- direct, in-file proof of the equality between the full-prime and
-- small-prime correction-factor products.

/-- **Support-reduction equality** (Iter 24): the full prime-filtered
    correction product equals the small-prime-filtered (`p² ≤ n`)
    product, because primes `p` with `p² > n` contribute `p^0 = 1`.

    Proof: `Finset.prod_subset` from the small filter (⊆ big filter)
    composed with the "complement is 1" condition, which is exactly
    Iter 17's `prime_pow_pred_eq_one_of_sq_lt` applied to primes whose
    membership in the big filter but not the small filter forces
    `n < p²` (equivalently `n < p * p`).

    Concrete numerics:
    * `n = 10`: full filter `{2, 3, 5, 7}` vs small filter `{2, 3}`
      (`5² = 25 > 10`), both products equal `2² · 3¹ · 5⁰ · 7⁰ = 12`.
    * `n = 100`: full filter has 25 primes vs small filter
      `{2, 3, 5, 7}` (`11² = 121 > 100`), both products equal
      `2⁵ · 3³ · 5 · 7 = 30240`.

    This is the direct in-file analogue of the
    `lcmRange_correction_supported_on_small_primes` lemma that PR
    #17619 (Iter 17) attempted but did not merge. -/
theorem prod_prime_pow_pred_eq_small (n : ℕ) :
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        p ^ (Nat.log p n - 1) =
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 2 ≤ n),
        p ^ (Nat.log p n - 1) := by
  refine (Finset.prod_subset ?_ ?_).symm
  · -- The small-prime filter is a subset of the full prime filter.
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · -- For `p` in the big filter but not the small filter, the
    -- correction factor `p^(Nat.log p n - 1)` is `1` because `p² > n`.
    intro p hp h_not_small
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hp_lt, hp_prime⟩ := hp
    have h_sq_gt : n < p * p := by
      by_contra h_sq_le
      push_neg at h_sq_le
      have h_sq_pow : p ^ 2 ≤ n := by rw [pow_two]; exact h_sq_le
      apply h_not_small
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hp_lt, hp_prime, h_sq_pow⟩
    exact prime_pow_pred_eq_one_of_sq_lt hp_prime h_sq_gt

/-- **Full correction-factor envelope** (Iter 24 main): chains Iter
    24's support-reduction equality (`prod_prime_pow_pred_eq_small`)
    with Iter 23's small-prime power-product envelope
    (`prod_prime_pow_pred_small_le_pow_sqrt`) to obtain the FULL
    correction-factor envelope

      `∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) ≤ (n / 2) ^ √n`

    under the hypothesis `2 ≤ n`.

    This is the **full LHS** of the Hanson bridge — bounding the
    correction factor (whose effective support is small primes `p² ≤ n`
    after support reduction) by `(n / 2)^√n = 2^(O(√n · log n))`.

    Combined with Iter 16's decomposition
    `lcmRange n = primorial n · ∏_{p prime} p^(Nat.log p n - 1)`
    (`lcmRange_eq_primorial_mul_prod_prime_pow_pred`) and Mathlib's
    `Nat.primorial_le_4_pow` (`primorial n ≤ 4^n`), this yields the
    structural Chebyshev envelope `lcmRange n ≤ 4^n · (n / 2)^√n`
    (assembled in a future iter), which closes the asymptotic gap to
    Hanson's `3^n` modulo small-`n` numerical checks (already covered
    by `hanson_n1`–`hanson_n20`).

    Concrete numerics (same as Iter 23's small-prime version, since
    the products are equal by `prod_prime_pow_pred_eq_small`):
    * `n = 10`: LHS = `12`, RHS = `5³ = 125`. ✓ (12 ≤ 125)
    * `n = 100`: LHS = `30240`, RHS = `50¹⁰ ≈ 9.77 · 10¹⁶`. ✓ -/
theorem prod_prime_pow_pred_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        p ^ (Nat.log p n - 1)
      ≤ (n / 2) ^ n.sqrt := by
  rw [prod_prime_pow_pred_eq_small]
  exact prod_prime_pow_pred_small_le_pow_sqrt hn

/-- **Concrete numerical witness** (Iter 24): at `n = 10` the full
    prime correction-factor product
    `∏_{p ∈ {2,3,5,7}} p^(Nat.log p 10 - 1) = 12` is bounded by
    `(10 / 2) ^ Nat.sqrt 10 = 5³ = 125`.

    Sanity check for `prod_prime_pow_pred_le_pow_sqrt`. The full-prime
    LHS equals the small-prime LHS (Iter 23's witness) because primes
    `5` and `7` (with `p² > 10`) contribute `p⁰ = 1`. -/
example :
    ∏ p ∈ (Finset.range 11).filter Nat.Prime,
        p ^ (Nat.log p 10 - 1)
      ≤ (10 / 2) ^ Nat.sqrt 10 := by
  native_decide

/-- **Chebyshev envelope assembly** (Iter 25): for `n ≥ 2`,
    `lcmRange n ≤ 4^n · (n / 2)^√n`.

    Combines Iter 16's primorial × correction-factor decomposition
    (`lcmRange_eq_primorial_mul_prod_prime_pow_pred`) with Mathlib's
    `primorial_le_4_pow` (the classical Erdős primorial bound) and
    Iter 24's full correction-factor envelope
    (`prod_prime_pow_pred_le_pow_sqrt`). The proof is a single
    `Nat.mul_le_mul` after rewriting `lcmRange n` as the product of
    the two factors.

    Strategic significance: this is the FIRST end-to-end asymptotic
    envelope on `lcmRange n` derived from prime-power structure
    (rather than the trivial `≤ n^n` factorial route of Part 3). The
    bound is asymptotically `4^n · 2^O(√n · log n)`, hence strictly
    weaker than Hanson's target `3^n` but capturing the right `O(4^n)`
    leading factor that any prime-power-based proof must produce.
    Closing the remaining `(4/3)^n vs (n/2)^√n` gap requires a
    sharper Chebyshev-style bound on the correction factor (or a
    cancellation between primorial and correction that exploits the
    Chebyshev `θ(n) ~ n` density — out of scope of this file).

    Concrete numerics (sanity check):
    * `n = 10`: LHS = `lcmRange 10 = 2520`, RHS = `4^10 · 5^3 =
      1048576 · 125 ≈ 1.31 · 10⁸`. ✓ (2520 ≤ 131072000)
    * `n = 20`: LHS = `232792560 ≈ 2.33 · 10⁸`,
      RHS = `4^20 · 10^4 ≈ 1.10 · 10¹⁶`. ✓ -/
theorem lcmRange_le_4_pow_mul_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
    lcmRange n ≤ 4 ^ n * (n / 2) ^ n.sqrt := by
  rw [lcmRange_eq_primorial_mul_prod_prime_pow_pred]
  exact Nat.mul_le_mul (primorial_le_4_pow n)
    (prod_prime_pow_pred_le_pow_sqrt hn)

/-- **Concrete numerical witness** (Iter 25): at `n = 10`,
    `lcmRange 10 = 2520 ≤ 4^10 · 5^3 = 131072000`.

    Sanity check for `lcmRange_le_4_pow_mul_pow_sqrt`. -/
example : lcmRange 10 ≤ 4 ^ 10 * (10 / 2) ^ Nat.sqrt 10 := by
  native_decide

/-- **Chebyshev envelope is strictly looser than Hanson's `3^n`**
    (Iter 26): for every `n ≥ 2`, `3^n < 4^n · (n / 2)^√n`.

    *Strategic content*: this records the formal fact that the Iter-25
    structural envelope `lcmRange_le_4_pow_mul_pow_sqrt` alone CANNOT
    close the `lcm_hanson_bound` axiom. The envelope is **always**
    asymptotically (and in fact pointwise for `n ≥ 2`) strictly larger
    than Hanson's target `3^n`, so no "find an `n₀` where envelope ≤ 3^n"
    route exists — the gap `(4/3)^n · (n/2)^√n` grows without bound.

    The path forward must strengthen at least one factor of the Iter-16
    decomposition `lcmRange n = primorial n · ∏ p^(Nat.log p n - 1)`:

    1. **Sharper primorial bound** — `primorial n ≤ c^n` with `c < 3`,
       e.g. via Chebyshev's θ-density `θ(n) = (1 + o(1)) · n` (PNT;
       not in Mathlib v4.26.0).
    2. **Cancellation route** — exploit the Chebyshev identity
       `lcm(1..n) = ∏ p^⌊log_p n⌋` (Iter 14 / Iter 16) directly,
       avoiding the primorial × correction split that loses the
       `(4/3)^n` factor.

    Proof: `(n/2)^√n ≥ 1` (since `n/2 ≥ 1` from `n ≥ 2`), so
    `4^n · (n/2)^√n ≥ 4^n`, and `3^n < 4^n` since `3 < 4` and `n ≠ 0`.
    Three-step term-mode, sorry-free, axiom-free. -/
theorem four_pow_mul_pow_sqrt_gt_three_pow {n : ℕ} (hn : 2 ≤ n) :
    3 ^ n < 4 ^ n * (n / 2) ^ n.sqrt := by
  have h_pos : 0 < n / 2 :=
    (Nat.one_le_div_iff (by decide : (0 : ℕ) < 2)).mpr hn
  have h_one_le : 1 ≤ (n / 2) ^ n.sqrt := Nat.one_le_pow _ _ h_pos
  have h_lt : (3 : ℕ) ^ n < 4 ^ n :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  calc (3 : ℕ) ^ n
      < 4 ^ n := h_lt
    _ = 4 ^ n * 1 := (Nat.mul_one _).symm
    _ ≤ 4 ^ n * (n / 2) ^ n.sqrt := Nat.mul_le_mul_left _ h_one_le

/-- **Concrete numerical witness** (Iter 26): at `n = 10`, the Iter-25
    envelope `4^10 · 5^3 = 131072000` strictly exceeds Hanson's target
    `3^10 = 59049`. Concrete demonstration that the envelope alone
    cannot match Hanson's bound.

    Sanity check for `four_pow_mul_pow_sqrt_gt_three_pow`. -/
example : 3 ^ 10 < 4 ^ 10 * (10 / 2) ^ Nat.sqrt 10 := by
  native_decide

/-- **Recursive structure**: lcm(1,...,n+1) = lcm(lcm(1,...,n), n+1).

    The inductive step that any inductive proof of Hanson's bound
    (or any bound on `lcmRange`) needs. Foundational structural
    lemma for future ACT-phase work on this OQ. -/
theorem lcmRange_succ (n : ℕ) :
    lcmRange (n + 1) = Nat.lcm (lcmRange n) (n + 1) := by
  apply Nat.dvd_antisymm
  · -- Forward: every divisor of `lcmRange (n+1)` divides
    -- `Nat.lcm (lcmRange n) (n+1)`. We route through `dvd_lcmRange`
    -- rather than `unfold lcmRange + Finset.dvd_lcm` to keep the
    -- function-shape fully determined and avoid the elaborator
    -- inferring `(HAdd.hAdd i)` for the lcm-indexing function.
    show (Finset.range (n + 1)).lcm (· + 1) ∣ Nat.lcm (lcmRange n) (n + 1)
    apply Finset.lcm_dvd
    intro i hi
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    by_cases hi_eq : i = n
    · subst hi_eq; exact Nat.dvd_lcm_right _ _
    · have hi' : i + 1 ≤ n := by omega
      have h_dvd : i + 1 ∣ lcmRange n := dvd_lcmRange (Nat.succ_pos _) hi'
      exact dvd_trans h_dvd (Nat.dvd_lcm_left _ _)
  · apply Nat.lcm_dvd
    · unfold lcmRange
      apply Finset.lcm_dvd
      intro i hi
      have : i < n + 1 :=
        lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.le_succ n)
      exact Finset.dvd_lcm (Finset.mem_range.mpr this)
    · exact dvd_lcmRange (Nat.succ_pos n) (Nat.le_refl _)

/-- **Divisibility monotonicity**: m ≤ n → lcm(1,...,m) ∣ lcm(1,...,n).

    Every divisor of the smaller LCM appears in the larger one. -/
theorem lcmRange_dvd_lcmRange_of_le {m n : ℕ} (h : m ≤ n) :
    lcmRange m ∣ lcmRange n := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  have hi_lt : i < n :=
    lt_of_lt_of_le (Finset.mem_range.mp hi) h
  exact Finset.dvd_lcm (Finset.mem_range.mpr hi_lt)

/-- **Numerical monotonicity**: m ≤ n → lcm(1,...,m) ≤ lcm(1,...,n). -/
theorem lcmRange_monotone : Monotone lcmRange := by
  intro m n h
  apply Nat.le_of_dvd _ (lcmRange_dvd_lcmRange_of_le h)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lcmRange_zero]; exact Nat.one_pos
  · exact lcmRange_pos n hn

-- =====================================================================
-- PART 3: Provable bounds (no axioms)
-- =====================================================================

/-- **lcm(1,...,n) divides n!**: every k ∈ {1,...,n} divides both lcm
    and n!, so lcm divides any common multiple ≥ n!. -/
theorem lcmRange_dvd_factorial (n : ℕ) : lcmRange n ∣ n.factorial := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact Nat.dvd_factorial (Nat.succ_pos i) (by omega)

/-- **lcm(1,...,n) ≤ n!** (trivial divisibility bound). -/
theorem lcmRange_le_factorial (n : ℕ) : lcmRange n ≤ n.factorial :=
  Nat.le_of_dvd n.factorial_pos (lcmRange_dvd_factorial n)

/-- **lcm(1,...,n) ≤ n^n** for n ≥ 1 (factorial bound). -/
theorem lcmRange_le_self_pow (n : ℕ) : lcmRange n ≤ n ^ n :=
  le_trans (lcmRange_le_factorial n) (Nat.factorial_le_pow n)

-- =====================================================================
-- PART 4: Numerical verification of Hanson's bound for n = 1..20
-- =====================================================================

theorem hanson_n1  : lcmRange 1  ≤ 3 ^ 1  := by decide
theorem hanson_n2  : lcmRange 2  ≤ 3 ^ 2  := by decide
theorem hanson_n3  : lcmRange 3  ≤ 3 ^ 3  := by decide
theorem hanson_n4  : lcmRange 4  ≤ 3 ^ 4  := by decide
theorem hanson_n5  : lcmRange 5  ≤ 3 ^ 5  := by decide
theorem hanson_n6  : lcmRange 6  ≤ 3 ^ 6  := by decide
theorem hanson_n7  : lcmRange 7  ≤ 3 ^ 7  := by decide
theorem hanson_n8  : lcmRange 8  ≤ 3 ^ 8  := by decide
theorem hanson_n9  : lcmRange 9  ≤ 3 ^ 9  := by decide
theorem hanson_n10 : lcmRange 10 ≤ 3 ^ 10 := by decide
theorem hanson_n12 : lcmRange 12 ≤ 3 ^ 12 := by decide
theorem hanson_n15 : lcmRange 15 ≤ 3 ^ 15 := by native_decide
theorem hanson_n20 : lcmRange 20 ≤ 3 ^ 20 := by native_decide

/-- **Iter 27 — extended numerical witnesses** for `n ∈ {25, 30, 50, 100}`.

    Hanson's bound `lcmRange n ≤ 3^n` is verified by `native_decide`
    on substantially larger inputs than the `hanson_n1`–`hanson_n20`
    table from Iter 0. The numerical margin grows with `n` (OEIS A003418
    cross-references in `lcmRange_*_eq` below):

    *  `lcmRange  25 ≈ 2.68 × 10¹⁰`  vs  `3^ 25 ≈ 8.47 × 10¹¹`,  margin ~32×.
    *  `lcmRange  30 ≈ 2.33 × 10¹²`  vs  `3^ 30 ≈ 2.06 × 10¹⁴`,  margin ~88×.
    *  `lcmRange  50 ≈ 3.10 × 10²¹`  vs  `3^ 50 ≈ 7.18 × 10²³`,  margin ~232×.
    *  `lcmRange 100 ≈ 6.97 × 10⁴⁰`  vs  `3^100 ≈ 5.15 × 10⁴⁷`,  margin ~7.4 × 10⁶.

    Strategic value: the Iter-25 Chebyshev envelope `lcmRange n ≤
    4^n · (n/2)^√n` is asymptotically `(4/3)^n · 2^(O(√n log n))`-loose
    against Hanson's target (Iter 26 falsifies the threshold route).
    Any future sharper primorial bound (Iter 27 candidate: `primorial n
    ≤ c^n` for `c < 3`) only kicks in for `n ≥ n₀`; extending the
    numerical floor to `n = 100` raises the value of `n₀` we can afford
    before the asymptotic kicks in. -/
theorem hanson_n25  : lcmRange 25  ≤ 3 ^ 25  := by native_decide
theorem hanson_n30  : lcmRange 30  ≤ 3 ^ 30  := by native_decide
theorem hanson_n50  : lcmRange 50  ≤ 3 ^ 50  := by native_decide
theorem hanson_n100 : lcmRange 100 ≤ 3 ^ 100 := by native_decide

-- Concrete lcm values (sanity checks, expected from OEIS A003418):
theorem lcmRange_5_eq  : lcmRange 5  = 60        := by decide
theorem lcmRange_10_eq : lcmRange 10 = 2520      := by decide
theorem lcmRange_15_eq : lcmRange 15 = 360360    := by native_decide
theorem lcmRange_20_eq : lcmRange 20 = 232792560 := by native_decide
theorem lcmRange_25_eq : lcmRange 25 = 26771144400 := by native_decide
theorem lcmRange_30_eq : lcmRange 30 = 2329089562800 := by native_decide
theorem lcmRange_50_eq : lcmRange 50 = 3099044504245996706400 := by native_decide
theorem lcmRange_100_eq :
    lcmRange 100 = 69720375229712477164533808935312303556800 := by native_decide

-- =====================================================================
-- PART 4.5: Iter 34 — Hanson/Route B bridge bound (28b-1)
-- =====================================================================

/-- **Iter 33 PREP Lemma A** (residue-arithmetic helper for 28b-1).

    For any prime `p`, any `n` and `k ≤ n`, and any position `i ∈ [1, v_p(n+1)]`,
    the residue sum `k % p^i + (n - k) % p^i` is strictly less than `p^i`.

    Equivalently: position `i` contributes **no carry** to the carries-count
    representation of `v_p(C(n,k))` (`Nat.factorization_choose`).

    **Proof sketch** (Iter 33 PREP §1.2):
    1. `p^i ∣ n + 1` (since `i ≤ v_p(n+1)` and `p^(v_p(n+1)) ∣ n+1` by
       `Nat.ordProj_dvd`, transitively via `Nat.pow_dvd_pow`).
    2. Hence `n % p^i = p^i - 1` (`n+1 ≡ 0 mod p^i` and `p^i ≥ 2`).
    3. By `Nat.add_mod` on `k + (n - k) = n`, the residue sum is
       `≡ p^i - 1 (mod p^i)`. Since both summands lie in `[0, p^i - 1]`,
       their sum lies in `[0, 2 p^i - 2]`, and the only value in that
       range with the required residue is `p^i - 1` itself. -/
lemma sum_mod_pow_lt_of_pow_dvd_succ
    {p i n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hi_le : i ≤ (n + 1).factorization p) :
    k % p ^ i + (n - k) % p ^ i < p ^ i := by
  have hp_two : 2 ≤ p := hp.two_le
  have hpi_pos : 0 < p ^ i := Nat.pow_pos hp.pos
  -- p^i ≥ 2 since p ≥ 2 and i ≥ 1.
  have hpi_ge_two : 2 ≤ p ^ i := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp_two 1
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega : 1 ≤ p) hi
  -- Step 1: p^i ∣ n+1.
  have h_dvd : p ^ i ∣ (n + 1) :=
    (Nat.pow_dvd_pow p hi_le).trans (Nat.ordProj_dvd (n + 1) p)
  have h_succ_mod : (n + 1) % p ^ i = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp h_dvd
  -- Step 2: n % p^i = p^i - 1.
  -- From (n+1) % p^i = 0 and Nat.add_mod, plus 1 % p^i = 1 (since p^i ≥ 2).
  have h_one_mod : (1 : ℕ) % p ^ i = 1 := Nat.mod_eq_of_lt (by omega : (1 : ℕ) < p ^ i)
  have h_nmod_lt : n % p ^ i < p ^ i := Nat.mod_lt _ hpi_pos
  have h_add_succ : (n + 1) % p ^ i = (n % p ^ i + 1) % p ^ i := by
    conv_lhs => rw [Nat.add_mod]
    rw [h_one_mod]
  rw [h_succ_mod] at h_add_succ
  -- (n % p^i + 1) % p^i = 0 with n % p^i ≤ p^i - 1 ⇒ n % p^i + 1 = p^i, i.e., n % p^i = p^i - 1.
  have h_n_mod : n % p ^ i = p ^ i - 1 := by
    rcases Nat.lt_or_ge (n % p ^ i + 1) (p ^ i) with hlt | hge
    · -- Case 1: n % p^i + 1 < p^i ⇒ (n % p^i + 1) % p^i = n % p^i + 1 ⇒ n % p^i + 1 = 0, absurd.
      exfalso
      have h_mod_self : (n % p ^ i + 1) % p ^ i = n % p ^ i + 1 := Nat.mod_eq_of_lt hlt
      rw [h_mod_self] at h_add_succ
      exact absurd h_add_succ.symm (Nat.succ_ne_zero _)
    · -- Case 2: n % p^i + 1 ≥ p^i with n % p^i < p^i ⇒ n % p^i + 1 = p^i.
      omega
  -- Step 3: sum residue analysis.
  have h_sum_eq : k + (n - k) = n := Nat.add_sub_cancel' hkn
  have h_add_mod_eq : (k % p ^ i + (n - k) % p ^ i) % p ^ i = p ^ i - 1 := by
    have h_chain := Nat.add_mod k (n - k) (p ^ i)
    rw [h_sum_eq] at h_chain
    rw [← h_chain, h_n_mod]
  -- Range squeeze: both addends are < p^i.
  have h_k : k % p ^ i < p ^ i := Nat.mod_lt _ hpi_pos
  have h_nk : (n - k) % p ^ i < p ^ i := Nat.mod_lt _ hpi_pos
  -- sum < 2*p^i; sum % p^i = p^i - 1. The only candidate < 2*p^i is p^i - 1 itself.
  by_contra h_not
  push_neg at h_not
  -- h_not : p^i ≤ sum.  Also sum < 2*p^i (from h_k + h_nk).
  have h_S_lt_2pi : k % p ^ i + (n - k) % p ^ i < 2 * p ^ i := by omega
  -- sum - p^i < p^i. By `Nat.mod_eq_sub_mod` and `Nat.mod_eq_of_lt`,
  -- (sum) % p^i = (sum - p^i) % p^i = sum - p^i.
  have h_sub_lt : k % p ^ i + (n - k) % p ^ i - p ^ i < p ^ i := by omega
  have h_mod_eq_sub : (k % p ^ i + (n - k) % p ^ i) % p ^ i =
      k % p ^ i + (n - k) % p ^ i - p ^ i := by
    rw [Nat.mod_eq_sub_mod h_not, Nat.mod_eq_of_lt h_sub_lt]
  rw [h_mod_eq_sub] at h_add_mod_eq
  -- h_add_mod_eq : sum - p^i = p^i - 1, so sum = 2*p^i - 1. But sum ≤ 2*(p^i - 1) = 2*p^i - 2.
  omega

/-- **Iter 34 ACT — 28b-1 bridge bound** (Iter 33 PREP §1.3, "Theorem 28b-1").

    For every prime `p`, every `n` and `k ≤ n`,
    `v_p(n+1) + v_p(C(n,k)) ≤ ⌊log_p (n+1)⌋`.

    This is the key arithmetic step of Hanson's bridge identity:
    `(n+1) * C(n,k) ∣ lcm(1,...,n+1)` (cf. Iter 28 PREP's
    `choose_mul_succ_dvd_lcmRange` target). Combined with the
    saturation witness (Iter 32 PREP 28b-2, follow-up ACT) and
    `lcmRange_eq_prod_prime_powers` (line 299), it discharges 28b
    by unique factorisation.

    **Proof sketch** (Iter 33 PREP §1.3):
    Apply `Nat.factorization_choose` with `b = log_p(n+1) + 1` (using
    `Nat.log_mono_right` so that `log_p n < log_p(n+1) + 1`). The
    resulting carries-set `{i ∈ Ico 1 (e+1) | p^i ≤ k%p^i + (n-k)%p^i}`
    is, by `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A), contained in
    `Ico (a+1) (e+1)` where `a = v_p(n+1)` and `e = log_p(n+1)`.
    Cardinality bound: `e - a`. Adding back `a` gives the claim. -/
theorem factorization_succ_mul_choose_le_log_succ
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) :
    (n + 1).factorization p + (Nat.choose n k).factorization p
      ≤ Nat.log p (n + 1) := by
  set a := (n + 1).factorization p with ha
  set e := Nat.log p (n + 1) with he
  -- `log p n < e + 1` (so factorization_choose's `b = e+1` is valid).
  have hlog : Nat.log p n ≤ e := Nat.log_mono_right (Nat.le_succ n)
  have hb : Nat.log p n < e + 1 := Nat.lt_succ_of_le hlog
  rw [Nat.factorization_choose hp hkn hb]
  -- a ≤ e (since p^a ∣ n+1 ⇒ p^a ≤ n+1 ⇒ a ≤ log_p (n+1)).
  have ha_le_e : a ≤ e := by
    have h_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
    have hn_pos : 0 < n + 1 := Nat.succ_pos n
    have h_pa_le : p ^ a ≤ n + 1 := Nat.le_of_dvd hn_pos h_dvd
    exact Nat.le_log_of_pow_le hp.one_lt h_pa_le
  -- Carries-set is contained in Ico (a+1) (e+1).
  have hfilter_subset :
      ((Finset.Ico 1 (e + 1)).filter
          (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)) ⊆
        Finset.Ico (a + 1) (e + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    obtain ⟨⟨hi1, hi2⟩, hi_carry⟩ := hi
    refine Finset.mem_Ico.mpr ⟨?_, hi2⟩
    by_contra hlt
    push_neg at hlt
    have hi_le_a : i ≤ a := Nat.lt_succ_iff.mp hlt
    have hsum := sum_mod_pow_lt_of_pow_dvd_succ hp hkn hi1 hi_le_a
    omega
  -- Cardinality of the carries-set is at most e - a.
  have hcard : (Finset.Ico (a + 1) (e + 1)).card = e - a := by
    rw [Nat.card_Ico]
    omega
  have h_filter_card_le :
      (((Finset.Ico 1 (e + 1)).filter
          (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card)
        ≤ e - a :=
    (Finset.card_le_card hfilter_subset).trans hcard.le
  omega

/-- **Helper 1** (Iter 36 PREP §2). For base `p > 1` and `i ≤ e`, the
    residue of `p^e - 1` modulo `p^i` is exactly `p^i - 1`.

    Used by the 28b-2 saturation witness to evaluate `(n - k₀) % p^i`. -/
private lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
  · subst hi0; simp [Nat.mod_one]
  have hp_two : 2 ≤ p := by omega
  obtain ⟨c, hc⟩ : p ^ i ∣ p ^ e := Nat.pow_dvd_pow p hie
  have hpi_pos : 0 < p ^ i := Nat.pow_pos (by omega)
  have hpi_ge_two : 2 ≤ p ^ i := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp_two 1
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega : 1 ≤ p) hi_pos
  have h_pi_lt : p ^ i - 1 < p ^ i := by omega
  have hc_pos : 1 ≤ c := by
    have h_pe_pos : 0 < p ^ e := Nat.pow_pos (by omega)
    rw [hc] at h_pe_pos
    rcases Nat.eq_zero_or_pos c with hc0 | hcp
    · simp [hc0] at h_pe_pos
    · exact hcp
  have hc1 : c - 1 + 1 = c := by omega
  have h_pic_eq : p ^ i * c = p ^ i * (c - 1) + p ^ i := by
    calc p ^ i * c = p ^ i * (c - 1 + 1) := by rw [hc1]
      _ = p ^ i * (c - 1) + p ^ i := by rw [mul_add, mul_one]
  have h_rearr : p ^ e - 1 = (p ^ i - 1) + p ^ i * (c - 1) := by
    rw [hc]; omega
  rw [h_rearr, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_pi_lt

/-- **Helper 2** (Iter 36 PREP §3). For prime `p`, `i = a + j` with
    `1 ≤ j`, `0 < f`, `p^f < m` and `p ∤ m`, the residue of the witness
    `p^a * (m - p^f)` modulo `p^i` is at least `1`. -/
private lemma witness_mod_pow_lt
    {p a m f i j : ℕ} (hp_prime : p.Prime)
    (hia : i = a + j) (hj_pos : 0 < j)
    (hf_pos : 0 < f) (hpf_lt : p ^ f < m) (hmp : ¬ p ∣ m) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i := by
  have hpi_eq : p ^ i = p ^ a * p ^ j := by rw [hia, pow_add]
  rw [hpi_eq, Nat.mul_mod_mul_left]
  have hpf_le : p ^ f ≤ m := hpf_lt.le
  have h_not_dvd : ¬ p ^ j ∣ (m - p ^ f) := by
    intro hdvd
    have hp_dvd_pj : p ∣ p ^ j := dvd_pow_self p hj_pos.ne'
    have hp_dvd_diff : p ∣ (m - p ^ f) := hp_dvd_pj.trans hdvd
    have hp_dvd_pf : p ∣ p ^ f := dvd_pow_self p hf_pos.ne'
    have h_sum : (m - p ^ f) + p ^ f = m := Nat.sub_add_cancel hpf_le
    have hp_dvd_m : p ∣ m := by
      have h_combined := hp_dvd_diff.add hp_dvd_pf
      rwa [h_sum] at h_combined
    exact hmp hp_dvd_m
  have h_mod_pos : 1 ≤ (m - p ^ f) % p ^ j := by
    rcases Nat.eq_zero_or_pos ((m - p ^ f) % p ^ j) with h_eq | h_pos
    · exact absurd (Nat.dvd_of_mod_eq_zero h_eq) h_not_dvd
    · exact h_pos
  have hpa_pos : 0 < p ^ a := Nat.pow_pos hp_prime.pos
  have hprod_pos : 0 < p ^ a * ((m - p ^ f) % p ^ j) :=
    Nat.mul_pos hpa_pos h_mod_pos
  omega

/-- **Iter 38 ACT — 28b-2 witness saturation** (Iter 36 PREP §4–§5).

    The witness `k₀ = (n+1) - p^e` (with `e = log_p (n+1)`) saturates the
    28b-1 bound: `v_p(n+1) + v_p(C(n, k₀)) = log_p(n+1)`. Combined with
    `factorization_succ_mul_choose_le_log_succ` (28b-1, the `≤` direction),
    this certifies that the divisibility `(n+1) * C(n, k₀) ∣ lcmRange(n+1)`
    from 28c is **tight** at `p` along the witness path.

    Proof: split on whether `n+1 = p^e`. In the equality case `k₀ = 0` and
    `C(n,0) = 1`, reducing the goal to `v_p(p^e) = e`. Otherwise `p^e < n+1`;
    writing `n+1 = p^a * m` with `p ∤ m` and `f = e - a`, the carries-set of
    `Nat.factorization_choose` is exactly `Ico (a+1) (e+1)` (lower bound by
    `sum_mod_pow_lt_of_pow_dvd_succ`, upper bound by Helpers 1 and 2), of
    cardinality `e - a`; adding back `a` gives `e`. -/
theorem exists_witness_choose_saturates_log_succ
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, k ≤ n ∧ (n + 1).factorization p + (Nat.choose n k).factorization p
                  = Nat.log p (n + 1) := by
  set e := Nat.log p (n + 1) with he_def
  set a := (n + 1).factorization p with ha_def
  refine ⟨(n + 1) - p ^ e, ?_, ?_⟩
  · have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    omega
  · set k := (n + 1) - p ^ e with hk_def
    have hkn : k ≤ n := by
      have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      omega
    by_cases hCaseA : n + 1 = p ^ e
    · -- Case A: n + 1 = p^e, so k = 0.
      have hk_zero : k = 0 := by omega
      rw [hk_zero, Nat.choose_zero_right, Nat.factorization_one]
      simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.add_zero]
      rw [ha_def, hCaseA, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    · -- Case B: p^e < n + 1.
      have ha_le_e : a ≤ e := by
        have h_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
        have h_pa_le : p ^ a ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) h_dvd
        exact Nat.le_log_of_pow_le hp.one_lt h_pa_le
      set m := (n + 1) / p ^ a with hm_def
      set f := e - a with hf_def
      have hpa_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
      have hn1_eq : n + 1 = p ^ a * m := (Nat.mul_div_cancel' hpa_dvd).symm
      have hmp : ¬ p ∣ m := by
        rw [hm_def]
        exact Nat.not_dvd_ordCompl hp (Nat.succ_ne_zero n)
      have hpe_le : p ^ e ≤ n + 1 := Nat.pow_log_le_self p (Nat.succ_ne_zero n)
      have hCaseB : p ^ e < n + 1 := by omega
      have h_pe_eq : p ^ e = p ^ a * p ^ f := by
        rw [hf_def, ← pow_add]; congr 1; omega
      have hpf_lt : p ^ f < m := by
        by_contra hcon
        push_neg at hcon
        have hmul : p ^ a * m ≤ p ^ a * p ^ f := Nat.mul_le_mul (le_refl _) hcon
        rw [← h_pe_eq, ← hn1_eq] at hmul
        omega
      have h_n_sub_k : n - k = p ^ e - 1 := by
        have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
        omega
      have h_k_eq : k = p ^ a * (m - p ^ f) := by
        have hle : p ^ f ≤ m := hpf_lt.le
        have hm_split : m = (m - p ^ f) + p ^ f := (Nat.sub_add_cancel hle).symm
        rw [hk_def, hn1_eq, h_pe_eq]
        conv_lhs => rw [hm_split, mul_add]
        rw [Nat.add_sub_cancel]
      have hlog : Nat.log p n ≤ e := Nat.log_mono_right (Nat.le_succ n)
      have hb : Nat.log p n < e + 1 := Nat.lt_succ_of_le hlog
      have hfilter_eq :
          ((Finset.Ico 1 (e + 1)).filter
              (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i))
            = Finset.Ico (a + 1) (e + 1) := by
        apply Finset.ext
        intro i
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨⟨hi1, hi_lt⟩, _hi_carry⟩
          refine ⟨?_, hi_lt⟩
          by_contra h_not
          push_neg at h_not
          have hi_le_a : i ≤ a := by omega
          have hsum := sum_mod_pow_lt_of_pow_dvd_succ hp hkn hi1 hi_le_a
          omega
        · rintro ⟨hia1, hi_lt⟩
          have hi1 : 1 ≤ i := by omega
          refine ⟨⟨hi1, hi_lt⟩, ?_⟩
          have hi_le_e : i ≤ e := by omega
          have hpi_pos : 0 < p ^ i := Nat.pow_pos hp.pos
          have h_nsubk_mod : (n - k) % p ^ i = p ^ i - 1 := by
            rw [h_n_sub_k]; exact pow_sub_one_mod_pow hp.one_lt hi_le_e
          have hj_pos : 0 < i - a := by omega
          have hf_pos : 0 < f := by omega
          have hia_eq : i = a + (i - a) := by omega
          have h_kmod : 1 ≤ k % p ^ i := by
            rw [h_k_eq]
            exact witness_mod_pow_lt hp hia_eq hj_pos hf_pos hpf_lt hmp
          rw [h_nsubk_mod]
          omega
      rw [Nat.factorization_choose hp hkn hb, hfilter_eq, Nat.card_Ico]
      omega

/-- **Theorem 28c** (divisibility bridge). Combining 28b-1
    (`factorization_succ_mul_choose_le_log_succ`) with the file-local
    Iter 5 lemma `prime_pow_dvd_lcmRange`, we obtain the load-bearing
    divisibility statement of Hanson's Route B:

    `(n + 1) * C(n, k) ∣ lcmRange (n + 1)`  for `k ≤ n`.

    The proof reduces divisibility to a prime-by-prime factorization
    comparison via `Nat.factorization_prime_le_iff_dvd`. For each prime
    `p`, the factorization of `(n+1) * C(n,k)` is bounded above by
    `log_p (n+1)` (28b-1), and `p ^ log_p (n+1) ∣ lcmRange (n+1)`
    by Iter 5. -/
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1) := by
  have hnp1 : (n + 1) ≠ 0 := Nat.succ_ne_zero n
  have hch  : Nat.choose n k ≠ 0 := (Nat.choose_pos hk).ne'
  have hnk  : (n + 1) * Nat.choose n k ≠ 0 := Nat.mul_ne_zero hnp1 hch
  have hlcm : lcmRange (n + 1) ≠ 0 := (lcmRange_pos (n + 1) (by omega)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hnk hlcm]
  intro p hp
  rw [Nat.factorization_mul hnp1 hch]
  simp only [Finsupp.add_apply]
  refine (factorization_succ_mul_choose_le_log_succ hp hk).trans ?_
  rw [← hp.pow_dvd_iff_le_factorization hlcm]
  exact prime_pow_dvd_lcmRange hp (by omega)

-- =====================================================================
-- PART 5: Hanson's general bound (open conjecture, axiomatized)
-- =====================================================================

/-- **Hanson's bound** (Hanson 1972): lcm(1,...,n) ≤ 3^n for all n ≥ 1.

    **Status**: Numerically verified above for n ∈ {1,...,10, 12, 15, 20}.
    The general statement is currently axiomatized; a full Lean proof
    would follow Hanson's original 1972 strategy (integral identity for
    Beta integrals + Chebyshev-style prime-power bounds), or an
    alternative route via Erdős's / Nair's combinatorial identities.

    Mathlib provides `primorial_le_4_pow` but no `lcm(1..n)`-specific
    bound. The transitions
    (i) `primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)` (combinatorial),
    (ii) `lcm(1..n) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ` (analytic),
    (iii) numerical case-checking for small n
    are all currently absent and would each be substantial Mathlib
    contributions. -/
axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3 ^ n

/-- Strict inequality on the bound exponent: 3^n < n^n eventually.

    Hanson's bound (3^n) is asymptotically much stronger than the
    trivial factorial-derived bound (n^n). Specifically, 3^n < n^n
    holds for all n ≥ 4 (since 3 < 4 ≤ n). -/
theorem hanson_strictly_stronger_than_factorial (n : ℕ) (h : 4 ≤ n) :
    3 ^ n < n ^ n :=
  Nat.pow_lt_pow_left (by omega) (by omega)

end BaselProblemOQ01OQ01OQ02OQ03
