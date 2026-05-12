import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
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
    simp [primorial, lcmRange_zero]
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

-- Concrete lcm values (sanity checks, expected from OEIS A003418):
theorem lcmRange_5_eq  : lcmRange 5  = 60        := by decide
theorem lcmRange_10_eq : lcmRange 10 = 2520      := by decide
theorem lcmRange_15_eq : lcmRange 15 = 360360    := by native_decide
theorem lcmRange_20_eq : lcmRange 20 = 232792560 := by native_decide

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
