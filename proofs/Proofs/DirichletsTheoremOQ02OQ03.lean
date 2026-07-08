/-
Certified Growth Bound for the k-th Prime ≡ 3 (mod 4)

The parent `DirichletsTheoremOQ02` proves there are infinitely many primes
`p ≡ 3 (mod 4)` by a Euclid-style construction: for every `n`, the number
`N = 4·(n+1)! − 1` satisfies `N ≡ 3 (mod 4)`, so it has a prime factor
`p ≡ 3 (mod 4)`, and that factor exceeds `n` because `p ∤ (n+1)!`.

This file quantifies *what growth bound that construction actually certifies*
for the k-th such prime.  Writing `p₀ < p₁ < p₂ < …` for the increasing
enumeration of primes `≡ 3 (mod 4)` (so `p₀ = 3`), the construction gives the
interval bound

    n < (next prime ≡ 3 mod 4 after n) ≤ 4·(n+1)! − 1,

and iterating it yields the explicit **iterated-factorial tower** upper bound

    pₖ ≤ Bₖ,   where   B₀ = 3,   B_{k+1} = 4·(Bₖ + 1)! − 1.

So `B₁ = 4·4! − 1 = 95`, `B₂ = 4·96! − 1`, `B₃ = 4·(B₂+1)! − 1`, …: a tower of
factorials.  The genuine asymptotic (PNT for arithmetic progressions) is
`pₖ ∼ 2k·ln k` — polynomial-ish.  The gap between the certified elementary bound
and the truth is therefore enormous; this file makes the certified side precise
and honest (it is an upper bound on `pₖ`, in no way tight).

Everything here is `native_decide`/`ofReduceBool`-free.

Status: Fully proved (0 sorry, 0 axiom)
-/

import Mathlib

open Finset Nat

namespace DirichletsTheoremOQ02OQ03

/-! ## Step 1: the Euclid interval bound

We reprove (self-contained) the parent's factor lemma and package the
construction as an *interval* statement: for every `n` there is a prime
`p ≡ 3 (mod 4)` with `n < p ≤ 4·(n+1)! − 1`. -/

/-- Any `n > 1` with `n ≡ 3 (mod 4)` has a prime factor `p ≡ 3 (mod 4)`.
    (Same argument as the parent file, included here to stay self-contained.) -/
theorem exists_prime_factor_three_mod_four (n : ℕ) (hn : 1 < n) (hmod : n % 4 = 3) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  have ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  by_cases hpmod : p % 4 = 3
  · exact ⟨p, hp, hpn, hpmod⟩
  · have hn_odd : ¬ 2 ∣ n := by omega
    have hp_ne_2 : p ≠ 2 := fun h => hn_odd (h ▸ hpn)
    have hpmod1 : p % 4 = 1 := by
      have hp_ge := hp.two_le
      have hp_odd : p % 2 = 1 := by
        have := hp.odd_of_ne_two hp_ne_2
        rwa [Nat.odd_iff] at this
      omega
    obtain ⟨k, hk⟩ := hpn
    have hk_gt : 1 < k := by
      rcases k with _ | _ | k
      · simp at hk; omega
      · simp at hk; subst hk; omega
      · omega
    have hk_mod : k % 4 = 3 := by
      have h1 : (p * k) % 4 = 3 := hk ▸ hmod
      rw [Nat.mul_mod, hpmod1] at h1
      simpa using h1
    have hk_lt : k < n := by subst hk; nlinarith [hp.one_lt]
    obtain ⟨q, hq, hqk, hqmod⟩ := exists_prime_factor_three_mod_four k hk_gt hk_mod
    exact ⟨q, hq, dvd_trans hqk ⟨p, by linarith⟩, hqmod⟩
termination_by n
decreasing_by exact hk_lt

/-- **Euclid interval bound.** For every `n`, there is a prime `p ≡ 3 (mod 4)`
with `n < p ≤ 4·(n+1)! − 1`.  This is exactly the certified content of the
Euclid construction: a prime `≡ 3 (mod 4)` always appears in the window
`(n, 4·(n+1)! − 1]`. -/
theorem exists_prime_three_mod_four_in_interval (n : ℕ) :
    ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ n < p ∧ p ≤ 4 * (n + 1)! - 1 := by
  set N := 4 * (n + 1)! - 1 with hN_def
  have hfac_pos : 0 < (n + 1)! := Nat.factorial_pos _
  have hN_gt_one : 1 < N := by simp only [hN_def]; omega
  have hN_mod : N % 4 = 3 := by simp only [hN_def]; omega
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_factor_three_mod_four N hN_gt_one hN_mod
  have hp_le_N : p ≤ N := Nat.le_of_dvd (by omega) hpN
  refine ⟨p, hp, hpmod, ?_, hp_le_N⟩
  -- p > n: otherwise p ∣ (n+1)! ∣ N+1 while p ∣ N, forcing p ∣ 1.
  by_contra h_le
  push_neg at h_le
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fac : p ∣ (n + 1)! := hp.dvd_factorial.mpr hp_le
  have hp_dvd_Nsucc : p ∣ N + 1 := by
    have hNS : N + 1 = 4 * (n + 1)! := by simp only [hN_def]; omega
    rw [hNS]; exact dvd_mul_of_dvd_right hp_dvd_fac 4
  obtain ⟨a, ha⟩ := hpN
  obtain ⟨b, hb⟩ := hp_dvd_Nsucc
  have : p ≤ 1 := by nlinarith [hp.pos, Nat.mul_le_mul_left p (show a + 1 ≤ b by nlinarith)]
  exact absurd this (not_le.mpr hp.one_lt)

/-- Existence of *some* prime `≡ 3 (mod 4)` above any `n` (drops the upper
bound; used to feed `Nat.find`). -/
theorem exists_prime_three_mod_four_gt (n : ℕ) :
    ∃ p, n < p ∧ Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hp, hpmod, hgt, _⟩ := exists_prime_three_mod_four_in_interval n
  exact ⟨p, hgt, hp, hpmod⟩

/-! ## Step 2: the next prime ≡ 3 (mod 4) and the certified tower

`nextP3 n` is the *least* prime `≡ 3 (mod 4)` strictly greater than `n`.  It is
well defined because such primes exist above every `n`. -/

/-- The least prime `≡ 3 (mod 4)` strictly greater than `n`. -/
def nextP3 (n : ℕ) : ℕ := Nat.find (exists_prime_three_mod_four_gt n)

theorem nextP3_gt (n : ℕ) : n < nextP3 n :=
  (Nat.find_spec (exists_prime_three_mod_four_gt n)).1

theorem nextP3_prime (n : ℕ) : Nat.Prime (nextP3 n) :=
  (Nat.find_spec (exists_prime_three_mod_four_gt n)).2.1

theorem nextP3_mod (n : ℕ) : nextP3 n % 4 = 3 :=
  (Nat.find_spec (exists_prime_three_mod_four_gt n)).2.2

/-- Minimality: any prime `q ≡ 3 (mod 4)` with `q > n` satisfies `nextP3 n ≤ q`.
This certifies that `nextP3 n` really is the *immediately next* such prime — no
prime `≡ 3 (mod 4)` is skipped in the interval `(n, nextP3 n)`. -/
theorem nextP3_le_of {n q : ℕ} (hq : n < q) (hprime : Nat.Prime q) (hmod : q % 4 = 3) :
    nextP3 n ≤ q :=
  Nat.find_min' (exists_prime_three_mod_four_gt n) ⟨hq, hprime, hmod⟩

/-- The Euclid construction bounds the next prime: `nextP3 n ≤ 4·(n+1)! − 1`. -/
theorem nextP3_le_factorial (n : ℕ) : nextP3 n ≤ 4 * (n + 1)! - 1 := by
  obtain ⟨p, hp, hpmod, hgt, hle⟩ := exists_prime_three_mod_four_in_interval n
  exact le_trans (nextP3_le_of hgt hp hpmod) hle

/-! ### The increasing enumeration `p3` of primes ≡ 3 (mod 4)

`p3 0 = 3` (the least such prime) and `p3 (k+1) = nextP3 (p3 k)`.  By
construction `p3` is strictly increasing, every value is a prime `≡ 3 (mod 4)`,
and (via `nextP3_le_of`) no such prime is skipped — so `p3 k` is exactly the
`k`-th prime `≡ 3 (mod 4)`. -/

/-- The increasing enumeration of primes `≡ 3 (mod 4)`, starting at `3`. -/
def p3 : ℕ → ℕ
  | 0 => 3
  | (k + 1) => nextP3 (p3 k)

@[simp] theorem p3_zero : p3 0 = 3 := rfl
@[simp] theorem p3_succ (k : ℕ) : p3 (k + 1) = nextP3 (p3 k) := rfl

/-- Every `p3 k` is prime. -/
theorem p3_prime (k : ℕ) : Nat.Prime (p3 k) := by
  cases k with
  | zero => simpa using (by norm_num : Nat.Prime 3)
  | succ k => simpa using nextP3_prime (p3 k)

/-- Every `p3 k` is `≡ 3 (mod 4)`. -/
theorem p3_mod (k : ℕ) : p3 k % 4 = 3 := by
  cases k with
  | zero => rfl
  | succ k => simpa using nextP3_mod (p3 k)

/-- `p3` is strictly increasing. -/
theorem p3_lt_succ (k : ℕ) : p3 k < p3 (k + 1) := by
  simpa using nextP3_gt (p3 k)

theorem p3_strictMono : StrictMono p3 :=
  strictMono_nat_of_lt_succ p3_lt_succ

/-! ### `p3` enumerates *exactly* the primes ≡ 3 (mod 4)

Strict monotonicity says `p3` lists primes `≡ 3 (mod 4)` in increasing order
without repetition; what makes "`p3 k` is *the* k-th such prime" rigorous is the
*completeness* statement — no prime `≡ 3 (mod 4)` is skipped.  This follows from
the minimality of `nextP3` (`nextP3_le_of`): the values of `p3` are gapless. -/

/-- `p3` grows at least as fast as the index (a strictly increasing `ℕ → ℕ`
sequence dominates the identity).  Used to locate any target below some `p3 k`. -/
theorem p3_le_self (k : ℕ) : k ≤ p3 k := by
  induction k with
  | zero => simp
  | succ k ih => have := p3_lt_succ k; omega

/-- **Completeness of the enumeration.**  Every prime `q ≡ 3 (mod 4)` occurs as
`p3 k` for some `k`; combined with `p3_strictMono` this certifies that `p3` is
the increasing enumeration of *all* primes `≡ 3 (mod 4)`, so `p3 k` really is the
`k`-th such prime and the tower bound `p3_le_tower` bounds every one of them. -/
theorem p3_surjective {q : ℕ} (hq : Nat.Prime q) (hmod : q % 4 = 3) :
    ∃ k, p3 k = q := by
  have hex : ∃ k, q ≤ p3 k := ⟨q, p3_le_self q⟩
  have hk : q ≤ p3 (Nat.find hex) := Nat.find_spec hex
  refine ⟨Nat.find hex, le_antisymm ?_ hk⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · -- q ≤ p3 0 = 3, and a prime ≡ 3 (mod 4) is ≥ 3, so q = 3
    rw [h0]; have hq2 := hq.two_le; simp only [p3]; omega
  · -- the predecessor is below q, so minimality of nextP3 pins p3 (Nat.find hex) ≤ q
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hmin : p3 j < q :=
      not_le.mp (Nat.find_min hex (show j < Nat.find hex by omega))
    rw [hj, p3_succ]
    exact nextP3_le_of hmin hq hmod

/-- **`p3` characterizes the primes `≡ 3 (mod 4)`.**  A number is a value of the
enumeration iff it is a prime `≡ 3 (mod 4)`: `p3` is onto that set, and (by
`p3_prime`/`p3_mod`) lands only in it. -/
theorem mem_range_p3_iff (q : ℕ) :
    (∃ k, p3 k = q) ↔ (Nat.Prime q ∧ q % 4 = 3) := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨p3_prime k, p3_mod k⟩
  · rintro ⟨hq, hmod⟩; exact p3_surjective hq hmod

/-! ## Step 3: the certified iterated-factorial tower bound

`B 0 = 3` and `B (k+1) = 4·(B k + 1)! − 1`.  We prove `p3 k ≤ B k`: the k-th
prime `≡ 3 (mod 4)` never exceeds this explicit tower of factorials. -/

/-- The certified upper-bound tower: `B 0 = 3`, `B (k+1) = 4·(B k + 1)! − 1`. -/
def B : ℕ → ℕ
  | 0 => 3
  | (k + 1) => 4 * (B k + 1)! - 1

@[simp] theorem B_zero : B 0 = 3 := rfl
@[simp] theorem B_succ (k : ℕ) : B (k + 1) = 4 * (B k + 1)! - 1 := rfl

/-- Monotonicity of the one-step map `x ↦ 4·(x+1)! − 1`. -/
theorem step_mono {a b : ℕ} (h : a ≤ b) : 4 * (a + 1)! - 1 ≤ 4 * (b + 1)! - 1 := by
  have hfac : (a + 1)! ≤ (b + 1)! := Nat.factorial_le (by omega)
  have : 4 * (a + 1)! ≤ 4 * (b + 1)! := by omega
  omega

/-- **Main certified bound.** The `k`-th prime `≡ 3 (mod 4)` satisfies
`p₃(k) ≤ B(k)`, the explicit iterated-factorial tower.  Concretely
`B 0 = 3`, `B 1 = 95`, `B 2 = 4·96! − 1`, …  — astronomically weaker than the
true asymptotic `pₖ ∼ 2k·ln k`, but fully certified by the elementary Euclid
construction. -/
theorem p3_le_tower (k : ℕ) : p3 k ≤ B k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc p3 (k + 1) = nextP3 (p3 k) := by simp
      _ ≤ 4 * (p3 k + 1)! - 1 := nextP3_le_factorial (p3 k)
      _ ≤ 4 * (B k + 1)! - 1 := step_mono ih
      _ = B (k + 1) := by simp

/-- **Certified linear lower bound.** The values `p3 k` are strictly increasing and all
`≡ 3 (mod 4)`, so consecutive ones differ by at least `4`; hence `p3 k ≥ 4k + 3`. This
is elementary (no primality input beyond the mod-4 residue) and complements the tower
upper bound. -/
theorem p3_ge_linear (k : ℕ) : 4 * k + 3 ≤ p3 k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt := p3_lt_succ k
    have hmk := p3_mod k
    have hmk1 := p3_mod (k + 1)
    omega

/-- **Bracketing the k-th prime `≡ 3 (mod 4)`.** Combining the two certified bounds,
`4k + 3 ≤ p3 k ≤ B k`: the k-th such prime is pinned between an explicit linear lower
bound and the iterated-factorial tower `B`. (The true growth is `p_k ∼ 2k·ln k`, which
sits between them.) -/
theorem p3_bracketed (k : ℕ) : 4 * k + 3 ≤ p3 k ∧ p3 k ≤ B k :=
  ⟨p3_ge_linear k, p3_le_tower k⟩

/-! ## Step 4: sanity checks and the honest contrast

Small values of both sides, confirming the bound holds and quantifying its
looseness.  `B 1 = 95` while the actual 2nd prime `≡ 3 (mod 4)` is `p3 1 = 7`. -/

/-- `p3 1 = 7` (the second prime `≡ 3 (mod 4)`). -/
theorem p3_one : p3 1 = 7 := by
  have hval : nextP3 3 = 7 := by
    apply le_antisymm
    · exact nextP3_le_of (by norm_num) (by norm_num) (by norm_num)
    · -- nothing in {4,5,6} is a prime ≡ 3 (mod 4) above 3
      have h := nextP3_gt 3
      have hp := nextP3_prime 3
      have hm := nextP3_mod 3
      by_contra hlt
      push_neg at hlt
      interval_cases (nextP3 3) <;> revert hp hm <;> decide
  simpa using hval

/-- `B 1 = 95`: the certified bound on the 2nd prime `≡ 3 (mod 4)` is `95`,
versus the true value `7`. -/
theorem B_one : B 1 = 95 := by decide

/-- The certified bound is (very) loose already at `k = 1`: `p3 1 = 7 ≤ 95 = B 1`. -/
theorem tower_loose_at_one : p3 1 < B 1 := by
  rw [p3_one, B_one]; norm_num

end DirichletsTheoremOQ02OQ03
