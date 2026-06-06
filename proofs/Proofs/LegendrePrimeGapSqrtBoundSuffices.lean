/-
# Legendre's Conjecture: Sqrt Prime-Gap Bound Suffices

This file formalizes the **one-way implication** that

  `(∀ k, p_{k+1} - p_k ≤ 2 * √p_k + 1) ⟹ LegendreConjecture`

where `p_k := Nat.nth Nat.Prime k` is the (k+1)-th prime (0-indexed). That is,
the prime-gap upper bound `2 * Nat.sqrt p_k + 1` is **sufficient** for Legendre.

## Mathematical content

**Proof** (for any `n ≥ 1`, exhibit a prime in `(n², (n+1)²)`):

* **Case `n = 1`**: prime `2` lies in `(1, 4)` directly.
* **Case `n ≥ 2`**: `n²` is composite (since `n² = n · n` with `1 < n < n²`).
  Let `k = Nat.findGreatest (fun k => p_k ≤ n²) n²`, so `p_k` is the largest
  prime `≤ n²`. Two facts about this `k`:
  - `p_k ≤ n² - 1` (strict, since `n²` is composite);
  - `p_{k+1} > n²` (by maximality of `k`).
  Applying the gap-bound hypothesis at this `k`:
  ```
  p_{k+1} ≤ p_k + 2 · √p_k + 1
        ≤ (n² - 1) + 2 · √(n² - 1) + 1
        = n² + 2 · √(n² - 1)
        ≤ n² + 2(n − 1)            [since √(n² − 1) ≤ n − 1 for n ≥ 1]
        = n² + 2n − 2
        < n² + 2n + 1
        = (n + 1)².
  ```
  Hence `n² < p_{k+1} < (n+1)²` with `p_{k+1}` prime, so `LegendreAt n` holds.

## Asymmetry: the converse direction is NOT provable from `LegendreConjecture` alone

The seemingly natural iff statement

  `LegendreConjecture ↔ ∀ k, p_{k+1} - p_k ≤ 2 · √p_k + 1`

is **not** a true equivalence. The forward direction
`Legendre ⟹ gap bound` is only provable up to `4 · √p_k + 2` in the worst
case, because `LegendreConjecture` asserts only the *existence* of a prime in
each `(m², (m+1)²)`, not that *every* prime is followed by another prime in
the same square interval.

Concrete failure mode (see §4 of the iter-4 PREP-1 audit memo):
for a prime `p_k` with `m := Nat.sqrt p_k` and `m² < p_k < (m+1)²`, Legendre
at `m` may be witnessed by some prime `q ≤ p_k`. In that case no prime is
forced in `(p_k, (m+1)²)`, and the next prime falls back to Legendre at `m+1`,
giving only `p_{k+1} ≤ (m+2)² - 1` and gap up to `4m + 2`.

See
`research/problems/bertrands-postulate-oq-02/sessions/2026-06-05-iter4-prep-1-gap-bound-asymmetry.md`
for the full audit. We formalize **only the salvageable (reverse) direction**.

## Axioms

This file introduces **0 new axioms**. The conclusion `LegendreConjecture` is
declared as an axiom in `LegendrePartial.lean`; here it is proved
*conditionally* on the gap-bound hypothesis, without strengthening the
ambient axiom basis of the project.
-/

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Proofs.LegendrePartial
import Proofs.LegendreGapEquivalence
import Proofs.PrimeGapBounds

namespace LegendrePrimeGapSqrtBoundSuffices

open Legendre LegendreGapEquivalence PrimeGapBounds

/-- The sqrt prime-gap upper bound hypothesis: for every `k`, the gap between
the (k+1)-th and (k+2)-th primes (0-indexed) is at most `2 · √p_k + 1`. -/
def PrimeGapSqrtBound : Prop :=
  ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
       ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1

/-! ## Auxiliary lemmas -/

/-- For `n ≥ 2`, `n^2` is not prime. -/
lemma not_prime_sq_of_ge_two {n : ℕ} (hn : 2 ≤ n) : ¬ Nat.Prime (n^2) := by
  rw [sq]
  intro hp
  rcases hp.eq_one_or_self_of_dvd n (Dvd.intro n rfl) with h | h
  · -- n = 1 contradicts n ≥ 2
    omega
  · -- n = n * n; with n ≥ 2 this forces n = 1, contradiction
    have hmul : n * 1 = n * n := by omega
    have heq : (1 : ℕ) = n := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) hmul
    omega

/-- The (k+1)-th prime (0-indexed) is at least `k + 2`. Proved by induction
using `Nat.nth_prime_zero_eq_two` and strict monotonicity of
`Nat.nth Nat.Prime`. -/
lemma nth_prime_ge (k : ℕ) : k + 2 ≤ Nat.nth Nat.Prime k := by
  induction k with
  | zero =>
    show 0 + 2 ≤ Nat.nth Nat.Prime 0
    rw [first_prime]
  | succ j ih =>
    have hmono : Nat.nth Nat.Prime j < Nat.nth Nat.Prime (j + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : j < j + 1)
    omega

/-! ## Main theorem -/

/-- **Sqrt prime-gap upper bound implies Legendre's Conjecture.**

If consecutive prime gaps are bounded by `2 · √p_k + 1` for every `k`, then
for every `n ≥ 1` there is a prime in `(n², (n+1)²)`. The proof uses the
largest prime ≤ `n²` (existence via `Nat.findGreatest`) and the strict
inequality `p_k < n²` from compositeness of `n²` for `n ≥ 2`. -/
theorem prime_gap_sqrt_bound_implies_legendre (h : PrimeGapSqrtBound) :
    LegendreConjecture := by
  intro n hn
  rcases lt_or_ge n 2 with hn1 | hn2
  · -- n = 1 case: prime 2 witnesses LegendreAt 1
    interval_cases n
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩
  · -- n ≥ 2 case: use the largest prime ≤ n²
    set P : ℕ → Prop := fun k => Nat.nth Nat.Prime k ≤ n^2 with hP_def
    set k := Nat.findGreatest P (n^2) with hk_def
    -- P 0 holds: nth Prime 0 = 2 ≤ n² (since n ≥ 2 implies n² ≥ 4)
    have hP0 : P 0 := by
      show Nat.nth Nat.Prime 0 ≤ n^2
      rw [first_prime]
      nlinarith [sq_nonneg n]
    -- The predicate holds at the maximizer.
    have hP_k : P k := Nat.findGreatest_spec (Nat.zero_le _) hP0
    -- The maximizer is ≤ the search bound.
    have hk_le : k ≤ n^2 := Nat.findGreatest_le _
    -- nth Prime k is itself prime.
    have hk_prime : Nat.Prime (Nat.nth Nat.Prime k) := nth_prime_is_prime k
    -- n² is composite for n ≥ 2.
    have hn2_not_prime : ¬ Nat.Prime (n^2) := not_prime_sq_of_ge_two hn2
    -- So the inequality `nth Prime k ≤ n²` is strict.
    have hk_lt : Nat.nth Nat.Prime k < n^2 := by
      rcases lt_or_eq_of_le hP_k with h | h
      · exact h
      · exfalso
        rw [← h] at hn2_not_prime
        exact hn2_not_prime hk_prime
    -- k + 1 ≤ n² (since nth Prime k ≥ k + 2 and nth Prime k < n²).
    have hk_succ_le : k + 1 ≤ n^2 := by
      have hge := nth_prime_ge k
      omega
    -- The predicate fails at k + 1, since k = findGreatest.
    have hPk1_not : ¬ P (k + 1) := by
      have hlt : Nat.findGreatest P (n^2) < k + 1 := by
        rw [← hk_def]; omega
      exact Nat.findGreatest_is_greatest hlt hk_succ_le
    -- Therefore nth Prime (k+1) > n².
    have hkp1_gt : n^2 < Nat.nth Nat.Prime (k + 1) := by
      change ¬ (Nat.nth Nat.Prime (k + 1) ≤ n^2) at hPk1_not
      omega
    -- Apply the gap-bound hypothesis at k.
    have hgap : Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
              ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1 := h k
    -- Strict monotonicity converts the Nat-subtraction into addition.
    have hkp1_strict : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self k)
    -- Bound the sqrt term by `n - 1`.
    have hsqrt_mono : Nat.sqrt (Nat.nth Nat.Prime k) ≤ Nat.sqrt (n^2 - 1) := by
      apply Nat.sqrt_le_sqrt; omega
    have hsqrt_n_sub : Nat.sqrt (n^2 - 1) ≤ n - 1 := by
      have h_lt_n : Nat.sqrt (n^2 - 1) < n := by
        rw [Nat.sqrt_lt']
        have hpos : (0 : ℕ) < n^2 := by positivity
        omega
      omega
    have hsqrt_bound : Nat.sqrt (Nat.nth Nat.Prime k) ≤ n - 1 := by omega
    -- Combine: nth Prime (k+1) < (n+1)² = n² + 2n + 1.
    have hkp1_lt : Nat.nth Nat.Prime (k + 1) < (n + 1)^2 := by
      have hpow : (n + 1)^2 = n^2 + 2 * n + 1 := by ring
      rw [hpow]
      omega
    exact ⟨Nat.nth Nat.Prime (k + 1), nth_prime_is_prime (k + 1), hkp1_gt, hkp1_lt⟩

/-! ## Corollary: the gap bound suffices in all equivalent forms

Combining the main theorem with the iter-2 equivalences from
`LegendreGapEquivalence`, the sqrt prime-gap hypothesis suffices for each of
the four equivalent reformulations of Legendre's Conjecture.
-/

/-- Sqrt gap bound suffices for the gap-form of Legendre's Conjecture. -/
theorem prime_gap_sqrt_bound_implies_gap_form (h : PrimeGapSqrtBound) :
    LegendreGapForm :=
  (legendre_iff_gap_form).mp (prime_gap_sqrt_bound_implies_legendre h)

/-- Sqrt gap bound suffices for the distance-form of Legendre's Conjecture. -/
theorem prime_gap_sqrt_bound_implies_distance_form (h : PrimeGapSqrtBound) :
    LegendreDistanceForm :=
  (legendre_iff_distance_form).mp (prime_gap_sqrt_bound_implies_legendre h)

/-- Sqrt gap bound suffices for the half-open form of Legendre's Conjecture. -/
theorem prime_gap_sqrt_bound_implies_halfOpen_form (h : PrimeGapSqrtBound) :
    LegendreHalfOpenForm :=
  (legendre_iff_halfOpen_form).mp (prime_gap_sqrt_bound_implies_legendre h)

/-! ## Summary

This file proves:

1. `PrimeGapSqrtBound` — the hypothesis `∀ k, p_{k+1} - p_k ≤ 2 · √p_k + 1`
   (where `p_k = Nat.nth Nat.Prime k`).
2. `prime_gap_sqrt_bound_implies_legendre`:
   `PrimeGapSqrtBound → LegendreConjecture`.
3. Three corollaries via the iter-2 equivalences: the same hypothesis suffices
   for the gap form, distance form, and half-open form of Legendre.

### Axiom delta

This file introduces **0 new axioms**. The pre-existing axiom
`Legendre.legendre_conjecture` (in `LegendrePartial.lean`) is unchanged.

### What this file does NOT prove

The converse direction (`Legendre ⟹ gap bound ≤ 2√p_k + 1`) is **not** a
theorem of pure logic from `LegendreConjecture` alone. See the iter-4 PREP-1
audit memo for a concrete failure mode (gap of up to `4√p_k + 2` is consistent
with `LegendreConjecture`).
-/

end LegendrePrimeGapSqrtBoundSuffices
