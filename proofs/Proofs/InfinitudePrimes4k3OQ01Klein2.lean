import Proofs.InfinitudePrimes4k3
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Parametric Klein-2 Infinitude: primes ≡ -1 (mod q) for q ∈ {3, 4, 6}

S3 ACT deliverable for `infinitude-primes-4k3-oq-01`. Implements PREP #18426
(researcher-10) Approach 3 (`rcases`-based) for the clean Klein-2 moduli
`q ∈ {3, 4, 6}` where `(ℤ/q)ˣ ≅ ℤ/2`, so "prime p coprime to q with
p ≢ 1 (mod q)" collapses to "p ≡ q - 1 (mod q)".

## What this file contributes

1. **q = 3** (new): bespoke Euclid-style proof
   `infinitely_many_primes_2_mod_3 : ∀ n, ∃ p > n, p.Prime ∧ p % 3 = 2`
   mirroring the parent's q = 4 structure (mul_mod / prime_mod / factors_determine
   / has_prime_factor / main).

2. **q = 4** (reuse): parent's `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4`.

3. **q = 6** (new corollary): primes ≡ 5 (mod 6) are exactly the odd primes
   ≡ 2 (mod 3), so the q = 3 result delivers infinitely many such primes by
   discarding the singleton `p = 2`.

4. **Combined**: `infinitely_many_primes_neg_one_mod_q` over `q = 3 ∨ q = 4 ∨ q = 6`,
   plus the `Set.Infinite` form `primes_neg_one_mod_q_infinite`.

## Why a separate file from `InfinitudePrimes4k3OQ01.lean`

The sibling file `InfinitudePrimes4k3OQ01.lean` imports `Proofs.DirichletsTheorem`
to provide the q = 4 bridge corollary. As of 2026-05-14, `DirichletsTheorem.lean`
has a v4.26.0 parent regression (9 errors at lines 124/140/148/178/186/201/215/226/238)
that blocks any file transitively importing it. This Klein-2 file imports only
`Proofs.InfinitudePrimes4k3` (clean) and `Mathlib`, so it builds independently
of the DirichletsTheorem regression.

## Counts

- 0 axioms, 0 sorries.
- 5 lemmas (q = 3 chain), 1 helper lemma (q = 6 bridge), 3 theorems
  (`infinitely_many_primes_2_mod_3`, `infinitely_many_primes_5_mod_6`,
  `infinitely_many_primes_neg_one_mod_q`, `primes_neg_one_mod_q_infinite`).
- ~190 lines including this docstring.
-/

namespace InfinitudePrimes4k3OQ01.Klein2

open Nat

/-! ## Helpers for q = 3

These mirror the parent file's q = 4 helpers (`mul_mod_four_one`, `prime_mod_four`,
`factors_determine_mod_four`, `has_prime_factor_3_mod_4`) under the substitution
`4 → 3` and `3 → 2` (the target residue class).
-/

/-- Product of two integers ≡ 1 (mod 3) is ≡ 1 (mod 3). -/
lemma mul_mod_three_one {a b : ℕ} (ha : a % 3 = 1) (hb : b % 3 = 1) :
    (a * b) % 3 = 1 := by
  calc (a * b) % 3 = ((a % 3) * (b % 3)) % 3 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 3 := by rw [ha, hb]
    _ = 1 := by norm_num

/-- Every prime `p ≠ 3` has `p % 3 ∈ {1, 2}`. (For `p = 2`, `2 % 3 = 2`; for
    `p ≥ 5` prime, `p % 3 ≠ 0` since otherwise `3 ∣ p` forces `p = 3`.) -/
lemma prime_mod_three {p : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  -- p % 3 ∈ {0, 1, 2}; rule out p % 3 = 0.
  have hp_mod_lt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hp_mod_ne0 : p % 3 ≠ 0 := by
    intro h0
    have h3_dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have h_or := hp.eq_one_or_self_of_dvd 3 h3_dvd
    have : p = 3 := (h_or.resolve_left (by norm_num)).symm
    exact hp3 this
  omega

/-- If `n ≥ 1` and every prime factor of `n` is ≡ 1 (mod 3), then `n % 3 ≠ 2`.
    (Strong induction on `n`, mirroring the parent's `factors_determine_mod_four`.) -/
lemma factors_determine_mod_three {n : ℕ} (hn : n ≥ 1)
    (h_factors : ∀ p : ℕ, Nat.Prime p → p ∣ n → p % 3 = 1) :
    n % 3 ≠ 2 := by
  intro hmod2
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn_ne1 : n ≠ 1 := by omega
    obtain ⟨p, hp_prime, hp_div⟩ := Nat.exists_prime_and_dvd hn_ne1
    have hp1 : p % 3 = 1 := h_factors p hp_prime hp_div
    obtain ⟨m, hm⟩ := hp_div
    have hm_pos : m ≥ 1 := by
      by_contra h; push_neg at h
      simp_all
    by_cases hm1 : m = 1
    · simp only [hm1, mul_one] at hm
      omega
    · have hm_ge2 : m ≥ 2 := by omega
      have hp_ge2 : p ≥ 2 := hp_prime.two_le
      have hm_lt : m < n := by
        rw [hm]
        calc m < 2 * m := by omega
          _ ≤ p * m := Nat.mul_le_mul_right m hp_ge2
      have h_m_factors : ∀ q : ℕ, Nat.Prime q → q ∣ m → q % 3 = 1 := by
        intro q hq_prime hq_div
        exact h_factors q hq_prime (by rw [hm]; exact dvd_mul_of_dvd_right hq_div p)
      have hn_eq : n % 3 = (p * m) % 3 := by rw [hm]
      have hmod_prod : (p * m) % 3 = ((p % 3) * (m % 3)) % 3 := Nat.mul_mod p m 3
      rw [hn_eq, hmod_prod, hp1] at hmod2
      simp only [one_mul] at hmod2
      have hm_mod2 : m % 3 = 2 := by omega
      exact ih m hm_lt hm_pos h_m_factors hm_mod2

/-- If `n ≥ 2` and `n ≡ 2 (mod 3)`, then `n` has a prime factor ≡ 2 (mod 3). -/
lemma has_prime_factor_2_mod_3 {n : ℕ} (hn : n ≥ 2) (hmod : n % 3 = 2) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p % 3 = 2 := by
  by_contra hno
  push_neg at hno
  have h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p % 3 = 1 := by
    intro p hp hdiv
    by_cases hp3 : p = 3
    · -- p = 3 ⟹ 3 ∣ n ⟹ n % 3 = 0, contradicts hmod = 2
      exfalso
      have h3_dvd : 3 ∣ n := by rw [hp3] at hdiv; exact hdiv
      have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_dvd
      omega
    · rcases prime_mod_three hp hp3 with h1 | h2
      · exact h1
      · exfalso; exact hno p hp hdiv h2
  exact factors_determine_mod_three (by omega : n ≥ 1) h hmod

/-- **Infinitely many primes ≡ 2 (mod 3).** Given any `n`, there exists a prime
    `p > n` with `p % 3 = 2`. Euclid-style: `N := 3 · (n+1)! - 1`. -/
theorem infinitely_many_primes_2_mod_3 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 3 = 2 := by
  intro n
  let N := 3 * (n + 1).factorial - 1
  have hfact_pos : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hN_mod : N % 3 = 2 := by simp only [N]; omega
  have hN_ge2 : N ≥ 2 := by simp only [N]; omega
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_2_mod_3 hN_ge2 hN_mod
  refine ⟨p, hp_prime, ?_, hp_mod⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_3fact : p ∣ 3 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 3
  have hN_add : N + 1 = 3 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N := Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_3fact) hp_div
  simp only [add_tsub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff

/-! ## q = 6 corollary

For an odd prime `p ≠ 2` with `p % 3 = 2`: `p % 6 = 5` (via CRT
`ZMod 6 ≅ ZMod 2 × ZMod 3`). Infinitely many primes ≡ 2 (mod 3) gives
infinitely many odd primes ≡ 2 (mod 3) (since at most one is `2`), which
are exactly the primes ≡ 5 (mod 6).
-/

/-- A prime `p ≠ 2` with `p % 3 = 2` has `p % 6 = 5`. -/
lemma prime_ne_two_mod_three_two_implies_mod_six_five {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp_mod3 : p % 3 = 2) : p % 6 = 5 := by
  have hp_odd : p % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one p with h | h
    · -- p % 2 = 0 ⟹ 2 ∣ p ⟹ p = 2
      exfalso
      have h2_dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
      have h_or := hp.eq_one_or_self_of_dvd 2 h2_dvd
      have : p = 2 := (h_or.resolve_left (by norm_num)).symm
      exact hp2 this
    · exact h
  -- p % 6 ∈ {0,…,5}; need both p % 2 = 1 and p % 3 = 2 ⟹ p % 6 = 5 by CRT.
  omega

/-- **Infinitely many primes ≡ 5 (mod 6).** Given any `n`, there exists a prime
    `p > n` with `p % 6 = 5`. Reduce to `infinitely_many_primes_2_mod_3`,
    extracting a prime strictly greater than `max n 2` so that `p ≠ 2`. -/
theorem infinitely_many_primes_5_mod_6 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 6 = 5 := by
  intro n
  obtain ⟨p, hp_prime, hp_gt, hp_mod3⟩ := infinitely_many_primes_2_mod_3 (max n 2)
  have hp_gt_n : p > n := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt_2 : p > 2 := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hp_ne_2 : p ≠ 2 := by omega
  refine ⟨p, hp_prime, hp_gt_n, ?_⟩
  exact prime_ne_two_mod_three_two_implies_mod_six_five hp_prime hp_ne_2 hp_mod3

/-! ## Combined parametric theorem -/

/-- **Parametric Klein-2 infinitude theorem**: for each `q ∈ {3, 4, 6}` there are
    infinitely many primes ≡ `q − 1` (mod `q`).

    Discharges:
    - q = 3 via `infinitely_many_primes_2_mod_3` (new this file),
    - q = 4 via `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4` (parent),
    - q = 6 via `infinitely_many_primes_5_mod_6` (new corollary). -/
theorem infinitely_many_primes_neg_one_mod_q {q : ℕ} (hq : q = 3 ∨ q = 4 ∨ q = 6) :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % q = q - 1 := by
  rcases hq with rfl | rfl | rfl
  · -- q = 3 (q - 1 = 2)
    intro n
    obtain ⟨p, hp, hgt, hm⟩ := infinitely_many_primes_2_mod_3 n
    exact ⟨p, hp, hgt, hm⟩
  · -- q = 4 (q - 1 = 3), parent's main theorem
    intro n
    obtain ⟨p, hp, hgt, hm⟩ := InfinitudePrimes4k3.infinitely_many_primes_3_mod_4 n
    exact ⟨p, hp, hgt, hm⟩
  · -- q = 6 (q - 1 = 5)
    intro n
    obtain ⟨p, hp, hgt, hm⟩ := infinitely_many_primes_5_mod_6 n
    exact ⟨p, hp, hgt, hm⟩

/-- Set-formulation: for each `q ∈ {3, 4, 6}`, the set of primes ≡ `q − 1` (mod `q`)
    is infinite. -/
theorem primes_neg_one_mod_q_infinite {q : ℕ} (hq : q = 3 ∨ q = 4 ∨ q = 6) :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p % q = q - 1} := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨n, hn⟩
  obtain ⟨p, hp_prime, hp_gt, hp_mod⟩ := infinitely_many_primes_neg_one_mod_q hq n
  have hp_mem : p ∈ {p : ℕ | Nat.Prime p ∧ p % q = q - 1} := ⟨hp_prime, hp_mod⟩
  have hp_le : p ≤ n := hn hp_mem
  omega

end InfinitudePrimes4k3OQ01.Klein2
