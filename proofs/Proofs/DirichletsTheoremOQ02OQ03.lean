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

/-! ## Step 5: the tighter **primorial** bound

The iterated-factorial tower `B` is astronomically loose because each step takes
a *factorial of the whole previous bound*.  The classical Euclid argument for
`≡ 3 (mod 4)` in fact only needs the *product of the primes found so far*, not a
factorial: given the first `k` primes `p3 0, …, p3 (k−1) ≡ 3 (mod 4)`, the number

    N = 4·(p3 0 · p3 1 ⋯ p3 (k−1)) − 1

is `≡ 3 (mod 4)`, so it has a prime factor `p ≡ 3 (mod 4)`; and `p` cannot be any
of `p3 0, …, p3 (k−1)` (each of those divides the product, hence `4·product`,
while `p ∣ N = 4·product − 1`, forcing `p ∣ 1`).  So `p` is a *new* prime
`≡ 3 (mod 4)`, giving `p3 k ≤ p ≤ N`.  This is the **primorial bound**

    p3 k ≤ 4·(∏_{i<k} p3 i) − 1,

replacing the factorial by a product.  It is enormously tighter: e.g.
`p3 1 ≤ 4·3 − 1 = 11` versus the factorial tower's `B 1 = 95`. -/

/-- **Primorial bound (actual-prime form).** The `k`-th prime `≡ 3 (mod 4)` is
bounded by four times the product of the previous ones, minus one:
`p3 k ≤ 4·(∏_{i<k} p3 i) − 1`.  This is the certified content of the *primorial*
Euclid construction and is far tighter than the factorial tower `B`. -/
theorem p3_le_primorial (k : ℕ) :
    p3 k ≤ 4 * (∏ i ∈ range k, p3 i) - 1 := by
  set M := ∏ i ∈ range k, p3 i with hM_def
  have hM_pos : 0 < M := Finset.prod_pos (fun i _ => (p3_prime i).pos)
  set N := 4 * M - 1 with hN_def
  have hN_gt_one : 1 < N := by omega
  have hN_mod : N % 4 = 3 := by omega
  obtain ⟨p, hp, hpN, hpmod⟩ := exists_prime_factor_three_mod_four N hN_gt_one hN_mod
  have hp_le_N : p ≤ N := Nat.le_of_dvd (by omega) hpN
  -- `p` is a prime `≡ 3 (mod 4)`, hence appears in the enumeration: `p = p3 m`.
  obtain ⟨m, hm⟩ := p3_surjective hp hpmod
  -- `p` is NOT among the first `k` primes: else it divides the product and `N`.
  have hp_new : k ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hdvd_M : p ∣ M := by
      rw [hM_def, ← hm]; exact Finset.dvd_prod_of_mem p3 (Finset.mem_range.mpr hlt)
    have hdvd_4M : p ∣ 4 * M := hdvd_M.mul_left 4
    have hNp1 : N + 1 = 4 * M := by omega
    rw [← hNp1] at hdvd_4M
    -- `p ∣ N` and `p ∣ N + 1` force `p ∣ 1`.
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpN).mp hdvd_4M
    have hp1 := hp.one_lt
    have := Nat.le_of_dvd one_pos h1
    omega
  calc p3 k ≤ p3 m := p3_strictMono.monotone hp_new
    _ = p := hm
    _ ≤ N := hp_le_N

/-! ### The explicit primorial tower `C`

`C k = 4·(∏_{i<k} C i) − 1`, computed via the running product `towerProd`.
Unrolling: `C 0 = 3`, `C 1 = 11`, `C 2 = 131`, `C 3 = 17291`, … — doubly
exponential, but incomparably smaller than the factorial tower `B` (`B 2 = 4·96!−1`).
We prove `p3 k ≤ C k` by strong induction, feeding `p3_le_primorial` the pointwise
bound `p3 i ≤ C i` for `i < k`. -/

/-- Running product `towerProd k = ∏_{i<k} C i`, defined structurally so that the
primorial tower `C` is a genuine recursion. -/
def towerProd : ℕ → ℕ
  | 0 => 1
  | (k + 1) => towerProd k * (4 * towerProd k - 1)

/-- The explicit primorial tower `C k = 4·(∏_{i<k} C i) − 1`. -/
def C (k : ℕ) : ℕ := 4 * towerProd k - 1

theorem C_eq (k : ℕ) : C k = 4 * towerProd k - 1 := rfl

@[simp] theorem towerProd_zero : towerProd 0 = 1 := rfl
@[simp] theorem towerProd_succ (k : ℕ) :
    towerProd (k + 1) = towerProd k * (4 * towerProd k - 1) := rfl

/-- `towerProd k` is the product `∏_{i<k} C i`, so `C` really is the primorial tower. -/
theorem towerProd_eq_prod (k : ℕ) : towerProd k = ∏ i ∈ range k, C i := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_range_succ, ← ih, C_eq, towerProd_succ]

/-- **Main tighter bound.** The `k`-th prime `≡ 3 (mod 4)` is bounded by the
explicit primorial tower: `p3 k ≤ C k`.  Compared with the factorial tower
`p3 k ≤ B k`, this replaces a tower of factorials by a doubly-exponential
primorial tower — still not tight (`p_k ∼ 2k·ln k`), but vastly closer. -/
theorem p3_le_primorialTower (k : ℕ) : p3 k ≤ C k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hle : (∏ i ∈ range k, p3 i) ≤ ∏ i ∈ range k, C i :=
      Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i hi => ih i (Finset.mem_range.mp hi))
    have hstep := p3_le_primorial k
    rw [C_eq, towerProd_eq_prod]
    omega

/-! ### Worked values and the honest contrast with the factorial tower -/

/-- `C 0 = 3`. -/
theorem C_zero_eq : C 0 = 3 := rfl

/-- `C 1 = 11`: the primorial bound on the 2nd prime `≡ 3 (mod 4)` is `11`
(true value `7`), versus the factorial tower's `B 1 = 95`. -/
theorem C_one_eq : C 1 = 11 := by decide

/-- `C 2 = 131`: the primorial bound on the 3rd prime `≡ 3 (mod 4)` is `131`,
versus `B 2 = 4·96! − 1`. -/
theorem C_two_eq : C 2 = 131 := by decide

/-- **The primorial tower is strictly tighter than the factorial tower** already
at `k = 1`, while remaining a valid upper bound:
`p3 1 = 7 ≤ 11 = C 1 < 95 = B 1`. -/
theorem primorial_tighter_than_factorial : p3 1 ≤ C 1 ∧ C 1 < B 1 := by
  rw [p3_one, C_one_eq, B_one]; exact ⟨by norm_num, by norm_num⟩

/-- **Sharper bracketing.** Combining the linear lower bound with the primorial
tower: `4k + 3 ≤ p3 k ≤ C k`, a strictly tighter ceiling than `p3_bracketed`. -/
theorem p3_bracketed_primorial (k : ℕ) : 4 * k + 3 ≤ p3 k ∧ p3 k ≤ C k :=
  ⟨p3_ge_linear k, p3_le_primorialTower k⟩

/-! ## Step 6: the primorial tower never exceeds the factorial tower (`C k ≤ B k`)

`primorial_tighter_than_factorial` established `C 1 < B 1` at the single index
`k = 1`.  We now upgrade this to a *theorem for all `k`*: the primorial tower `C`
is dominated by the iterated-factorial tower `B` everywhere, `C k ≤ B k`.

The engine is the reduction `C (k+1) ≤ B (k+1) ⇔ towerProd (k+1) ≤ (B k + 1)!`
(both sides are `4·· − 1`), so it suffices to bound the running product
`towerProd` by the factorial appearing in `B`.  That product bound is proved by
induction: writing `F = (B k + 1)!`, the inductive hypothesis gives
`towerProd (k+1) ≤ F`, and then
`towerProd (k+2) = towerProd (k+1)·(4·towerProd (k+1) − 1) ≤ F·(4F − 1)
   ≤ (4F)·(4F − 1) ≤ (4F)! = (B (k+1) + 1)!`,
using only the elementary factorial lower bound `n·(n−1) ≤ n!`. -/

/-- Elementary factorial lower bound `n·(n−1) ≤ n!` (from `n! = n·(n−1)!` and
`n−1 ≤ (n−1)!`).  Supplies the single non-arithmetic step in `C_le_B`. -/
theorem factorial_ge_mul_pred : ∀ n : ℕ, n * (n - 1) ≤ n !
  | 0 => by simp
  | (m + 1) => by
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      exact Nat.mul_le_mul (le_refl (m + 1)) (Nat.self_le_factorial m)

/-- The running product is bounded by the factorial appearing in the next `B`
step: `towerProd (k+1) ≤ (B k + 1)!`.  This is the crux of `C_le_B`. -/
theorem towerProd_succ_le_factorial (k : ℕ) : towerProd (k + 1) ≤ (B k + 1)! := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hFpos := Nat.factorial_pos (B k + 1)
    have hB1 : B (k + 1) + 1 = 4 * (B k + 1)! := by rw [B_succ]; omega
    rw [towerProd_succ, hB1]
    set F := (B k + 1)! with hF
    set tp := towerProd (k + 1) with htp
    calc tp * (4 * tp - 1)
        ≤ F * (4 * F - 1) := Nat.mul_le_mul ih (by omega)
      _ ≤ (4 * F) * (4 * F - 1) := Nat.mul_le_mul (by omega) (le_refl _)
      _ ≤ (4 * F)! := factorial_ge_mul_pred (4 * F)

/-- **The primorial tower never exceeds the factorial tower.** For every `k`,
`C k ≤ B k`: the doubly-exponential primorial tower `C` is dominated everywhere
by the iterated-factorial tower `B`.  Equality holds only at `k = 0`
(`C 0 = B 0 = 3`); for `k ≥ 1` the domination is strict already at `k = 1`
(`C 1 = 11 < 95 = B 1`, see `primorial_tighter_than_factorial`).  This makes the
tightness of the primorial refinement a *theorem for all `k`* rather than a
single-index observation. -/
theorem C_le_B (k : ℕ) : C k ≤ B k := by
  cases k with
  | zero => decide
  | succ k =>
    have h := towerProd_succ_le_factorial k
    rw [C_eq, B_succ]; omega

/-! ## Step 7: the domination is **strict** for every `k ≥ 1` (`C k < B k`)

`C_le_B` gives `C k ≤ B k` everywhere, with equality at `k = 0`
(`C 0 = B 0 = 3`).  We now upgrade the inequality to a *strict* one for all
`k ≥ 1`, matching the single-index observation `C 1 = 11 < 95 = B 1` of
`primorial_tighter_than_factorial`.  The slack is already present in the
factorial step: the ceiling `n·(n−1) ≤ n!` used in `C_le_B` is in fact *strict*
for `n ≥ 4` (`n! = n·(n−1)!` and `(n−1)! > (n−1)` once `n−1 ≥ 3`), and the
argument `4·(B k + 1)! ≥ 4` always lands in that regime.  So the running-product
bound `towerProd (k+1) ≤ (B k + 1)!` sharpens to a strict `<`, and the strictness
transfers to `C (k+1) < B (k+1)` because both towers apply the same monotone
`x ↦ 4·(x+1)! − 1` (resp. `x ↦ 4·x − 1`) map. -/

/-- Strict elementary factorial bound `n·(n−1) < n!` for `n ≥ 4`.  From
`n! = n·(n−1)!` together with `(n−1) < (n−1)!` (valid since `n − 1 ≥ 3`), i.e.
`Nat.lt_factorial_self`.  This is the strict refinement of `factorial_ge_mul_pred`
that supplies the strictness in `C_lt_B`. -/
theorem factorial_gt_mul_pred {n : ℕ} (hn : 4 ≤ n) : n * (n - 1) < n ! := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hp : 3 ≤ p := by omega
  have hlt : p < p ! := Nat.lt_factorial_self hp
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  exact mul_lt_mul_of_pos_left hlt (by omega)

/-- Strict running-product bound `towerProd (k+1) < (B k + 1)!`.  Identical to
`towerProd_succ_le_factorial` except the final factorial step is strict via
`factorial_gt_mul_pred` (its argument `4·(B k + 1)!` is always `≥ 4`). -/
theorem towerProd_succ_lt_factorial (k : ℕ) : towerProd (k + 1) < (B k + 1)! := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hFpos := Nat.factorial_pos (B k + 1)
    have hB1 : B (k + 1) + 1 = 4 * (B k + 1)! := by rw [B_succ]; omega
    rw [towerProd_succ, hB1]
    set F := (B k + 1)! with hF
    set tp := towerProd (k + 1) with htp
    calc tp * (4 * tp - 1)
        ≤ F * (4 * F - 1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (4 * F) * (4 * F - 1) := Nat.mul_le_mul (by omega) (le_refl _)
      _ < (4 * F)! := factorial_gt_mul_pred (by omega)

/-- **The primorial tower is strictly below the factorial tower for every
`k ≥ 1`.**  `C k < B k` whenever `k ≥ 1`, sharpening `C_le_B` (which allows
equality) and promoting the single-index fact `C 1 = 11 < 95 = B 1` to a theorem
for all `k ≥ 1`.  Equality holds *only* at `k = 0` (`C 0 = B 0 = 3`), so together
with `C_le_B` this pins down the comparison exactly: `C k = B k ⇔ k = 0`. -/
theorem C_lt_B {k : ℕ} (hk : 1 ≤ k) : C k < B k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := towerProd_succ_lt_factorial j
  rw [C_eq, B_succ]; omega

/-- **Exact comparison of the two towers.** `C k = B k` if and only if `k = 0`;
for all `k ≥ 1` the primorial tower is strictly smaller.  Combines `C_le_B`,
`C_lt_B`, and the base equality `C 0 = B 0 = 3`. -/
theorem C_eq_B_iff (k : ℕ) : C k = B k ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    exact absurd h (Nat.ne_of_lt (C_lt_B (by omega)))
  · rintro rfl; decide

end DirichletsTheoremOQ02OQ03
