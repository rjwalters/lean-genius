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

/-! ### An explicit (non-recursive) closed-form certified bound

The bounds `p3 k ≤ B k` and `p3 k ≤ C k` are both *recursive*: to evaluate them
one must unfold the tower.  Here we collapse the primorial recursion into a single
explicit closed form, `p3 k ≤ 4^(2^k)`, which makes the *doubly-exponential* growth
of the certified bound literally visible in the exponent `2^k`.  The proof is a clean
squaring induction: `4·towerProd (k+1) = (4·towerProd k)·(4·towerProd k − 1) ≤
(4·towerProd k)^2`, and squaring the inductive bound `4·towerProd k ≤ 4^(2^k)` gives
`(4^(2^k))^2 = 4^(2^(k+1))`. -/

/-- Squaring induction: `4·towerProd k ≤ 4^(2^k)`.  This is the engine converting the
recursive primorial tower into a closed-form bound; the leading factor `4` is carried so
that `C k = 4·towerProd k − 1` inherits the bound with no residual arithmetic. -/
theorem four_mul_towerProd_le (k : ℕ) : 4 * towerProd k ≤ 4 ^ (2 ^ k) := by
  induction k with
  | zero => decide
  | succ n ih =>
    have h1 : 4 * towerProd (n + 1) ≤ (4 * towerProd n) * (4 * towerProd n) := by
      rw [towerProd_succ]
      calc 4 * (towerProd n * (4 * towerProd n - 1))
            = (4 * towerProd n) * (4 * towerProd n - 1) := by ring
        _ ≤ (4 * towerProd n) * (4 * towerProd n) :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h3 : 4 ^ (2 ^ n) * 4 ^ (2 ^ n) = 4 ^ (2 ^ (n + 1)) := by
      rw [← pow_add, pow_succ, Nat.mul_two]
    calc 4 * towerProd (n + 1) ≤ (4 * towerProd n) * (4 * towerProd n) := h1
      _ ≤ 4 ^ (2 ^ n) * 4 ^ (2 ^ n) := Nat.mul_le_mul ih ih
      _ = 4 ^ (2 ^ (n + 1)) := h3

/-- **Closed-form primorial-tower bound.** `C k ≤ 4^(2^k)`: the primorial tower is
dominated by the explicit doubly-exponential `4^(2^k)`, no recursion required. -/
theorem C_le_doubly_exp (k : ℕ) : C k ≤ 4 ^ (2 ^ k) :=
  le_trans (by rw [C_eq]; exact Nat.sub_le _ _) (four_mul_towerProd_le k)

/-- **Explicit doubly-exponential certified bound.** The `k`-th prime `≡ 3 (mod 4)`
satisfies `p3 k ≤ 4^(2^k)` — a single closed-form expression, no tower to unfold.
This exposes the exact order of the certified elementary bound: doubly exponential in
`k` (true value `∼ 2k·ln k`).  It is a corollary of `p3_le_primorialTower` and
`C_le_doubly_exp`. -/
theorem p3_le_doubly_exp (k : ℕ) : p3 k ≤ 4 ^ (2 ^ k) :=
  le_trans (p3_le_primorialTower k) (C_le_doubly_exp k)

/-- The closed-form bound is consistent with the primorial tower at `k = 2`:
`p3 2 ≤ C 2 = 131 ≤ 256 = 4^(2^2)`. -/
theorem doubly_exp_at_two : C 2 ≤ 4 ^ (2 ^ 2) := by rw [C_two_eq]; norm_num

/-! ### The doubly-exponential growth is *intrinsic* (matching lower bound)

`C_le_doubly_exp` shows the primorial tower `C` is bounded *above* by the
doubly-exponential `4^(2^k)`.  On its own an upper bound leaves open whether the
tower is actually much smaller — perhaps only singly-exponential.  We rule that
out with a matching *lower* bound: the running product satisfies
`towerProd k ≥ 3^(2^k − 1)`, so `C` is also bounded *below* by a
doubly-exponential.  The engine is the reverse of the squaring induction: since
each factor `4·towerProd k − 1 ≥ 3·towerProd k` (as `towerProd k ≥ 1`), we get
`towerProd (k+1) ≥ 3·towerProd k²`, and squaring `towerProd k ≥ 3^(2^k − 1)`
gives `3·(3^(2^k − 1))² = 3^(2^{k+1} − 1)`.  Together with the upper bound this
brackets `C` between two doubly-exponentials, so the certified elementary bound
is *intrinsically* doubly-exponential — no re-evaluation of this tower can yield
a sub-exponential certificate. -/

/-- **Doubly-exponential lower bound on the running product.**
`3^(2^k − 1) ≤ towerProd k`: the primorial running product grows at least
doubly-exponentially, the reverse of the squaring induction in
`four_mul_towerProd_le`. -/
theorem towerProd_ge (k : ℕ) : 3 ^ (2 ^ k - 1) ≤ towerProd k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h3 : (1 : ℕ) ≤ 3 ^ (2 ^ k - 1) := Nat.one_le_pow _ _ (by norm_num)
    have htp : 1 ≤ towerProd k := le_trans h3 ih
    -- each step at least triples-and-squares: towerProd (k+1) ≥ 3 · towerProd k²
    have hstep : 3 * towerProd k ^ 2 ≤ towerProd (k + 1) := by
      rw [towerProd_succ]
      calc 3 * towerProd k ^ 2 = towerProd k * (3 * towerProd k) := by ring
        _ ≤ towerProd k * (4 * towerProd k - 1) :=
            Nat.mul_le_mul (le_refl _) (by omega)
    -- exponent identity: 3 · (3^(2^k−1))² = 3^(2^{k+1}−1)
    have hexp : 3 * (3 ^ (2 ^ k - 1)) ^ 2 = 3 ^ (2 ^ (k + 1) - 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      have hk1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      omega
    calc 3 ^ (2 ^ (k + 1) - 1) = 3 * (3 ^ (2 ^ k - 1)) ^ 2 := hexp.symm
      _ ≤ 3 * towerProd k ^ 2 := Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left ih 2)
      _ ≤ towerProd (k + 1) := hstep

/-- **Doubly-exponential lower bound on the primorial tower.**
`4·3^(2^k − 1) − 1 ≤ C k`.  Combined with `C_le_doubly_exp` the tower is
bracketed by two doubly-exponentials. -/
theorem C_ge_doubly_exp (k : ℕ) : 4 * 3 ^ (2 ^ k - 1) - 1 ≤ C k := by
  have h := towerProd_ge k
  rw [C_eq]
  omega

/-- **The certified tower is intrinsically doubly-exponential.**
`4·3^(2^k − 1) − 1 ≤ C k ≤ 4^(2^k)`: the primorial tower `C` is sandwiched
between two doubly-exponential functions of `k`.  So the elementary Euclid
certificate for the `k`-th prime `≡ 3 (mod 4)` is doubly-exponential in an
essential two-sided sense — the enormous gap to the truth `p_k ∼ 2k·ln k` is a
genuine feature of the method, not an artifact of a loose upper estimate. -/
theorem C_doubly_exp_bracket (k : ℕ) :
    4 * 3 ^ (2 ^ k - 1) - 1 ≤ C k ∧ C k ≤ 4 ^ (2 ^ k) :=
  ⟨C_ge_doubly_exp k, C_le_doubly_exp k⟩

/-! ## Step 9: the factorial tower `B` is **tower-exponential** — the gap to the
primorial tower diverges

Step 8 pinned the primorial tower `C` between two doubly-exponentials
(`C_doubly_exp_bracket`): each `C` step only squares-and-triples the previous
value (`C (k+1) ≈ C k²`), so `C` stays in the doubly-exponential growth class.
The factorial tower `B` is fundamentally larger: one step applies a whole
*factorial*, so `B` climbs an iterated exponential.

We make the separation precise with the lower bound `2^(B k) ≤ B (k+1)`: each
`B` step at least exponentiates the previous value base `2` (so `B k ≥ 2 ↑↑ k`,
a tower of exponentials — a strictly larger growth class than `C`'s
doubly-exponential one).  As a consequence, a *single* factorial step already
exceeds `2` raised to the *entire* primorial-tower value, `2^(C k) ≤ B (k+1)`.
This quantifies exactly how the gap between the two certified bounds diverges:
where the primorial step merely squares `C k`, the factorial in `B` turns the
whole of `C k` into the exponent `2^(C k)`, an exponential blow-up recurring at
every level. -/

/-- Elementary bound `2^n ≤ (n+1)!`: the factorial dominates the base-2
exponential.  Supplies the exponential lower bound feeding the tower-growth
estimate for `B`.  (Proved by a direct induction: `2·2^n ≤ 2·(n+1)! ≤
(n+2)·(n+1)! = (n+2)!`.) -/
theorem two_pow_le_succ_factorial (n : ℕ) : 2 ^ n ≤ (n + 1)! := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.factorial_succ]
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      _ ≤ 2 * (n + 1)! := Nat.mul_le_mul (le_refl 2) ih
      _ ≤ (n + 1 + 1) * (n + 1)! := Nat.mul_le_mul (by omega) (le_refl _)

/-- **Each factorial step exponentiates the previous value: `2^(B k) ≤ B (k+1)`.**
The iterated-factorial tower `B` therefore grows at least like an iterated base-2
exponential (`B k ≥ 2 ↑↑ k`), a strictly larger growth class than the
doubly-exponential primorial tower `C` (`C_doubly_exp_bracket`).  Uses only
`2^(B k) ≤ (B k + 1)!` (`two_pow_le_succ_factorial`) and the fact that
`B (k+1) = 4·(B k + 1)! − 1 ≥ (B k + 1)!`. -/
theorem B_succ_ge_two_pow (k : ℕ) : 2 ^ B k ≤ B (k + 1) := by
  have hf := two_pow_le_succ_factorial (B k)
  have hpos := Nat.factorial_pos (B k + 1)
  rw [B_succ]
  omega

/-- **One factorial step exceeds `2` raised to the whole primorial tower:
`2^(C k) ≤ B (k+1)`.**  Chaining `C k ≤ B k` (`C_le_B`) with the exponential
step `B_succ_ge_two_pow`, a single step of the factorial tower dominates
`2^(C k)`.  Since the primorial tower only squares each step (`C (k+1) ≈ C k²`,
still doubly-exponential by `C_doubly_exp_bracket`), this is a certified,
`native_decide`-free quantification of the divergence of the gap between the two
towers: the factorial replaces the squaring `C k ↦ C k²` by a full base-2
exponentiation `C k ↦ 2^(C k)` of the primorial value, at every level. -/
theorem two_pow_C_le_B_succ (k : ℕ) : 2 ^ C k ≤ B (k + 1) :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (C_le_B k)) (B_succ_ge_two_pow k)

/-! ## Step 10: the ratio `B / C` diverges — `B k ≥ (C k)²` and `∀ m, m·C k ≤ B k`

Steps 8–9 separated the two towers by *growth class* (primorial `C` is
doubly-exponential, factorial `B` is tower-exponential).  Here we turn that
qualitative separation into a quantitative statement about the ratio: the
factorial tower eventually dominates the **square** of the primorial tower,
`(C k)² ≤ B k`, and consequently `B k / C k → ∞` in the division-free form
`∀ m, ∃ K, ∀ k ≥ K, m·C k ≤ B k`.

The mechanism is the exponential step `2^(C k) ≤ B (k+1)`
(`two_pow_C_le_B_succ`): one factorial step raises `2` to the whole primorial
value, and a base-2 exponential of `C k` dwarfs any fixed power of `C (k+1)`
(which is only `≈ (C k)²`).  The single analytic-free input is the elementary
`(n+1)^4 ≤ 2^n` for `n ≥ 17`. -/

/-- Closed multiplicative form of the primorial recursion:
`C (k+1) + 1 = (C k + 1)·C k`.  Equivalently `C (k+1) = (C k)² + C k − 1`, so
each step squares the previous value up to lower-order terms — the source of the
doubly-exponential growth of `C`. -/
theorem C_succ_add_one (k : ℕ) : C (k + 1) + 1 = (C k + 1) * C k := by
  have ht : 1 ≤ towerProd k :=
    le_trans (Nat.one_le_pow _ _ (by norm_num)) (towerProd_ge k)
  have ht1 : 1 ≤ towerProd (k + 1) :=
    le_trans (Nat.one_le_pow _ _ (by norm_num)) (towerProd_ge (k + 1))
  have hCk : C k + 1 = 4 * towerProd k := by rw [C_eq]; omega
  have hCk1 : C (k + 1) + 1 = 4 * towerProd (k + 1) := by rw [C_eq]; omega
  rw [hCk1, towerProd_succ, hCk, C_eq]
  set d := 4 * towerProd k - 1
  ring

/-- Each primorial step is bounded by the square of the successor:
`C (k+1) ≤ (C k + 1)²`.  Immediate from `C_succ_add_one`. -/
theorem C_succ_le_sq (k : ℕ) : C (k + 1) ≤ (C k + 1) ^ 2 := by
  have h := C_succ_add_one k
  have hle : (C k + 1) * C k ≤ (C k + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  omega

/-- The primorial tower is monotone: `C k ≤ C (k+1)`.  Since
`C (k+1) + 1 = (C k + 1)·C k ≥ C k + 1` (as `C k ≥ 1`). -/
theorem C_le_succ (k : ℕ) : C k ≤ C (k + 1) := by
  have h := C_succ_add_one k
  have hpos : 1 ≤ C k := by
    have := towerProd_ge k
    have h1 : 1 ≤ towerProd k := le_trans (Nat.one_le_pow _ _ (by norm_num)) this
    rw [C_eq]; omega
  nlinarith [h, hpos]

/-- Monotonicity of the primorial tower. -/
theorem C_mono : Monotone C := monotone_nat_of_le_succ C_le_succ

/-- Linear lower bound `k + 3 ≤ C k`: in particular `C` is unbounded, so it
eventually exceeds any fixed multiplier. -/
theorem C_ge_add (k : ℕ) : k + 3 ≤ C k := by
  induction k with
  | zero => rw [C_zero_eq]
  | succ n ih =>
    have h := C_succ_add_one n
    nlinarith [ih, h]

/-- **Exponential beats a fixed power:** `(n+1)^4 ≤ 2^n` for `n ≥ 17`.  The one
elementary, `native_decide`-free input to the ratio-divergence result.  Proved by
induction from the base `18^4 = 104976 ≤ 131072 = 2^17`, with the multiplicative
step `(n+2)^4 ≤ 2·(n+1)^4` (valid for `n ≥ 5`). -/
theorem quartic_le_two_pow (n : ℕ) (hn : 17 ≤ n) : (n + 1) ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 289 ≤ n * n := by nlinarith [hn]
    have h2 : 289 * (n * n) ≤ (n * n) * (n * n) := by nlinarith [h1]
    have hstep : (n + 2) ^ 4 ≤ 2 * (n + 1) ^ 4 := by nlinarith [hn, h1, h2]
    calc (n + 1 + 1) ^ 4 = (n + 2) ^ 4 := by ring
      _ ≤ 2 * (n + 1) ^ 4 := hstep
      _ ≤ 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **The factorial tower dominates the square of the primorial tower:**
`(C k)² ≤ B k` for all `k ≥ 3`.  Writing `k = j+1`, the exponential step gives
`B (j+1) ≥ 2^(C j)`, while `C (j+1) ≤ (C j + 1)²` so `C (j+1)² ≤ (C j + 1)^4`,
and `(C j + 1)^4 ≤ 2^(C j)` once `C j ≥ 17` (true for `j ≥ 2`, since `C 2 = 131`
and `C` is monotone).  Certified, `native_decide`-free. -/
theorem C_sq_le_B {k : ℕ} (hk : 3 ≤ k) : C k ^ 2 ≤ B k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj2 : 2 ≤ j := by omega
  have hCj : 17 ≤ C j := by
    have hmono := C_mono hj2
    rw [C_two_eq] at hmono
    omega
  have hquartic : (C j + 1) ^ 4 ≤ 2 ^ C j := quartic_le_two_pow (C j) hCj
  have hsucc : C (j + 1) ^ 2 ≤ (C j + 1) ^ 4 := by
    calc C (j + 1) ^ 2 ≤ ((C j + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (C_succ_le_sq j) 2
      _ = (C j + 1) ^ 4 := by ring
  calc C (j + 1) ^ 2 ≤ (C j + 1) ^ 4 := hsucc
    _ ≤ 2 ^ C j := hquartic
    _ ≤ B (j + 1) := two_pow_C_le_B_succ j

/-- **The ratio `B / C` diverges (division-free form):**
`∀ m, ∃ K, ∀ k ≥ K, m·C k ≤ B k`.  Since `C k → ∞` (`C_ge_add`), taking
`k ≥ max 3 m` gives `m ≤ C k`, and then `m·C k ≤ (C k)² ≤ B k` by `C_sq_le_B`.
This is the precise quantitative statement that the elementary factorial
certificate `B` outgrows the primorial certificate `C` without bound — a
certified counterpart to `p_k / C_k → ∞` for the two Euclid-style towers. -/
theorem B_div_C_diverges (m : ℕ) : ∃ K, ∀ k, K ≤ k → m * C k ≤ B k := by
  refine ⟨max 3 m, fun k hk => ?_⟩
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkm : m ≤ k := le_trans (le_max_right _ _) hk
  have hCk : m ≤ C k := by have := C_ge_add k; omega
  have hsq : C k ^ 2 ≤ B k := C_sq_le_B hk3
  calc m * C k ≤ C k * C k := Nat.mul_le_mul_right _ hCk
    _ = C k ^ 2 := (sq (C k)).symm
    _ ≤ B k := hsq

/-! ## Step 11: the factorial tower `B` is **tetrational** (`2 ↑↑ k ≤ B k`), and
the growth-class separation from `C` is sharp

Step 9 established the recursive exponential step `2^(B k) ≤ B (k+1)`
(`B_succ_ge_two_pow`), and Step 10 turned it into the ratio divergence
`B / C → ∞`.  What was still missing is a *closed-form* placement of `B` in the
tetration (iterated-exponential) growth class.  We supply it: writing `2 ↑↑ k`
for the tower of `k` twos (`tower2`), we prove `2 ↑↑ k ≤ B k`.

Combined with the doubly-exponential *upper* bound `C k ≤ 4^(2^k)`
(`C_le_doubly_exp`, Step 8), this separates the two certified towers by growth
class in the sharpest possible sense: tetration eventually dominates any fixed
doubly-exponential, so for `k ≥ 5` the closed-form lower bound on `B` already
exceeds the closed-form upper bound on `C`,

    C k ≤ 4^(2^k) ≤ 2 ↑↑ k ≤ B k.

The threshold `k = 5` is sharp: at `k = 4` one still has
`2 ↑↑ 4 = 65536 < 4^(2^4)` (`tower2_lt_doubly_exp_at_four`). -/

/-- Base-2 tetration `tower2 k = 2 ↑↑ k`, the tower of `k` twos:
`tower2 0 = 1`, `tower2 (k+1) = 2 ^ tower2 k`.  Values `1, 2, 4, 16, 65536,
2^65536, …` — an iterated exponential, a strictly larger growth class than any
doubly-exponential. -/
def tower2 : ℕ → ℕ
  | 0 => 1
  | (k + 1) => 2 ^ tower2 k

@[simp] theorem tower2_zero : tower2 0 = 1 := rfl
@[simp] theorem tower2_succ (k : ℕ) : tower2 (k + 1) = 2 ^ tower2 k := rfl

/-- Self-contained `n < 2^n` (used to convert the exponential lower bound on
`tower2` into a linear one). -/
theorem lt_two_pow_aux (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    omega

/-- **The factorial tower is tetrational: `2 ↑↑ k ≤ B k`.**  Each factorial step
of `B` base-2 exponentiates the previous value (`B_succ_ge_two_pow`), so `B`
dominates the tower of twos of the same height.  This closed-form
iterated-exponential lower bound complements the doubly-exponential *upper* bound
`C k ≤ 4^(2^k)`: the factorial certificate `B` lives in the tetration growth
class, strictly above the primorial certificate `C`. -/
theorem tower2_le_B (k : ℕ) : tower2 k ≤ B k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc tower2 (k + 1) = 2 ^ tower2 k := rfl
      _ ≤ 2 ^ B k := Nat.pow_le_pow_right (by norm_num) ih
      _ ≤ B (k + 1) := B_succ_ge_two_pow k

/-- Linear-in-exponent lower bound on tetration: `2^(k+2) ≤ 2 ↑↑ k` for `k ≥ 4`.
The engine converting the tetration recursion into the doubly-exponential
comparison below.  Inductive step: `2 ↑↑ (k+1) = 2^(2 ↑↑ k) ≥ 2^(k+3)` because
`2 ↑↑ k ≥ 2^(k+2) ≥ k+3` (the second gap from `n < 2^n`). -/
theorem two_pow_le_tower2 {k : ℕ} (hk : 4 ≤ k) : 2 ^ (k + 2) ≤ tower2 k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [tower2_succ]
    have hklin : k + 1 + 2 ≤ tower2 k := by
      have h1 : k + 2 < 2 ^ (k + 2) := lt_two_pow_aux (k + 2)
      omega
    exact Nat.pow_le_pow_right (by norm_num) hklin

/-- **Tetration overtakes the doubly-exponential ceiling of `C`:**
`4^(2^k) ≤ 2 ↑↑ k` for `k ≥ 5`.  Writing `k = j+1`, one has
`4^(2^(j+1)) = 2^(2·2^(j+1)) = 2^(2^(j+2))` and `2 ↑↑ (j+1) = 2^(2 ↑↑ j)`, so the
claim reduces to `2^(j+2) ≤ 2 ↑↑ j` (`two_pow_le_tower2`, valid for `j ≥ 4`). -/
theorem doubly_exp_le_tower2 {k : ℕ} (hk : 5 ≤ k) : 4 ^ (2 ^ k) ≤ tower2 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 4 ≤ j := by omega
  have hexp : 2 ^ (j + 2) ≤ tower2 j := two_pow_le_tower2 hj
  have hpow : (2 : ℕ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    have hjj : j + 2 = (j + 1) + 1 := by omega
    rw [hjj, pow_succ]; ring
  have key : (4 : ℕ) ^ (2 ^ (j + 1)) = 2 ^ (2 ^ (j + 2)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, hpow]
  rw [key, tower2_succ]
  exact Nat.pow_le_pow_right (by norm_num) hexp

/-- The separation threshold `k = 5` is sharp: at `k = 4` the tetration lower
bound is still below the doubly-exponential, `2 ↑↑ 4 = 65536 < 4294967296 =
4^(2^4)`.  So `doubly_exp_le_tower2` genuinely requires `k ≥ 5`. -/
theorem tower2_lt_doubly_exp_at_four : tower2 4 < 4 ^ (2 ^ 4) := by decide

/-- **Sharp growth-class separation of the two certified towers.**  For every
`k ≥ 5`,

    C k ≤ 4^(2^k) ≤ 2 ↑↑ k ≤ B k,

so the doubly-exponential *upper* bound on the primorial tower `C` is dominated
by the tetration *lower* bound on the factorial tower `B`.  This upgrades the
qualitative "different growth classes" picture (Steps 8–9) and the ratio
divergence (Step 10) to an explicit sandwich in which a closed-form
iterated-exponential on the `B` side overtakes a closed-form doubly-exponential
on the `C` side.  The `k = 5` threshold is sharp
(`tower2_lt_doubly_exp_at_four`). -/
theorem growth_class_separation {k : ℕ} (hk : 5 ≤ k) :
    C k ≤ 4 ^ (2 ^ k) ∧ 4 ^ (2 ^ k) ≤ tower2 k ∧ tower2 k ≤ B k :=
  ⟨C_le_doubly_exp k, doubly_exp_le_tower2 hk, tower2_le_B k⟩

/-! ## Step 12: the counting-function side — a certified lower bound on `π(x; 4, 3)`

Steps 1–10 quantified the `k`-th prime `≡ 3 (mod 4)` (the *value* `p3 k`).  The
dual object is the **counting function** `π(x; 4, 3) = #{p ≤ x : p prime, p ≡ 3
(mod 4)}`.  The enumeration `p3` transfers the value bound into a count bound: the
`k+1` distinct primes `p3 0, …, p3 k` all lie below `x` as soon as `p3 k ≤ x`, so

    p3 k ≤ x  ⟹  k + 1 ≤ π(x; 4, 3).

Feeding the certified closed-form value bound `p3 k ≤ 4^(2^k)` (`p3_le_doubly_exp`)
gives an *explicit* certified lower bound on the counting function:

    π(4^(2^k); 4, 3) ≥ k + 1,   i.e.   π(x; 4, 3) ≥ k + 1  whenever  x ≥ 4^(2^k).

Since `4^(2^k)` is doubly exponential in `k`, the certified count grows only like
an *iterated logarithm* of `x` (`π(x; 4, 3) ⪆ log₂ log₄ x`).  The genuine
asymptotic is `π(x; 4, 3) ∼ x / (2 ln x)` (PNT for arithmetic progressions), so —
exactly as on the value side — the elementary Euclid certificate is astronomically
weaker than the truth, and this makes the gap precise on the counting side too.
Everything here is `native_decide`/`ofReduceBool`-free. -/

/-- The counting function `π(x; 4, 3)`: the number of primes `p ≤ x` with
`p ≡ 3 (mod 4)`. -/
def primesCount3 (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % 4 = 3)).card

/-- **Value bound ⟹ count bound.**  If the `k`-th prime `≡ 3 (mod 4)` satisfies
`p3 k ≤ x`, then there are at least `k + 1` primes `≡ 3 (mod 4)` below `x`:
`k + 1 ≤ π(x; 4, 3)`.  The `k + 1` witnesses are the distinct enumerated primes
`p3 0, …, p3 k`, all `≤ p3 k ≤ x`, all prime `≡ 3 (mod 4)`. -/
theorem card_le_primesCount3 {k x : ℕ} (hk : p3 k ≤ x) : k + 1 ≤ primesCount3 x := by
  have hsub : (Finset.range (k + 1)).image p3 ⊆
      (Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p % 4 = 3) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hle : p3 i ≤ p3 k := p3_strictMono.monotone (by omega)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, p3_prime i, p3_mod i⟩
  have hcard : ((Finset.range (k + 1)).image p3).card = k + 1 := by
    rw [Finset.card_image_of_injective _ p3_strictMono.injective, Finset.card_range]
  calc k + 1 = ((Finset.range (k + 1)).image p3).card := hcard.symm
    _ ≤ primesCount3 x := Finset.card_le_card hsub

/-- The counting function is monotone: `π(·; 4, 3)` never decreases. -/
theorem primesCount3_mono : Monotone primesCount3 := by
  intro a b hab
  simp only [primesCount3]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- **Certified lower bound at the tower points.**  At `x = 4^(2^k)` there are at
least `k + 1` primes `≡ 3 (mod 4)`: `k + 1 ≤ π(4^(2^k); 4, 3)`.  Immediate from the
value bound `p3 k ≤ 4^(2^k)` (`p3_le_doubly_exp`) via `card_le_primesCount3`. -/
theorem primesCount3_ge_of_doubly_exp (k : ℕ) : k + 1 ≤ primesCount3 (4 ^ (2 ^ k)) :=
  card_le_primesCount3 (p3_le_doubly_exp k)

/-- **Certified counting-function lower bound.**  For every `k`, once `x ≥ 4^(2^k)`
there are at least `k + 1` primes `≡ 3 (mod 4)` up to `x`:
`k + 1 ≤ π(x; 4, 3)`.  Since `4^(2^k)` is doubly exponential in `k`, the certified
count grows only like an iterated logarithm of `x` — vastly weaker than the true
`π(x; 4, 3) ∼ x/(2 ln x)`, quantifying the elementary gap on the counting side. -/
theorem primesCount3_ge (k x : ℕ) (hx : 4 ^ (2 ^ k) ≤ x) : k + 1 ≤ primesCount3 x :=
  le_trans (primesCount3_ge_of_doubly_exp k) (primesCount3_mono hx)

/-- **The count is unbounded (infinitude, counting form).**  For every target `m`
there is a threshold `x` beyond which `π(x; 4, 3) ≥ m`: taking `x = 4^(2^m)` gives
`m ≤ m + 1 ≤ π(x; 4, 3)`.  This is the counting-function restatement of "there are
infinitely many primes `≡ 3 (mod 4)`", now with an explicit certified threshold. -/
theorem primesCount3_unbounded (m : ℕ) : ∃ x, m ≤ primesCount3 x :=
  ⟨4 ^ (2 ^ m), le_trans (Nat.le_succ m) (primesCount3_ge_of_doubly_exp m)⟩

/-! ## Step 13: `B` dominates **every fixed power** of `C` — `(C k)^p ≤ B k`

Step 10 proved the factorial tower `B` eventually dominates the *square* of the
primorial tower, `(C k)² ≤ B k`, hence `B / C → ∞`.  The tetration lower bound
`2 ↑↑ k ≤ B k` (Step 11) makes a far stronger statement transparent: `B`
eventually dominates **any fixed power** `(C k)^p`, and even `m·(C k)^p` for any
fixed multiplier `m`.  So `B / C^p → ∞` for *every* exponent `p`, i.e. `B`
outgrows every polynomial in the primorial certificate `C`.

The mechanism is the closed-form sandwich: on the `C` side
`(C k)^p ≤ (4^(2^k))^p = 2^(2^(k+1)·p)` (`C_le_doubly_exp`), while on the `B` side
`B k ≥ 2 ↑↑ k = 2^(2 ↑↑ (k−1))` (`tower2_le_B`).  It therefore suffices to
compare the *exponents*: `2^(k+1)·p ≤ 2 ↑↑ (k−1)`, and the tetration term
eventually dwarfs the doubly-exponential one.  Certified, `native_decide`-free —
the only quantitative inputs are `n < 2^n` and the linear tetration bound
`2^(k+2) ≤ 2 ↑↑ k` of Step 11. -/

/-- Tetration beats a fixed doubly-exponential with a doubled exponent:
`2^(2k+2) ≤ 2 ↑↑ k` for `k ≥ 5`.  Writing `k = i+1`, the claim
`2^(2i+4) ≤ 2^(2 ↑↑ i)` reduces to `2i+4 ≤ 2 ↑↑ i`, which follows from
`2^(i+2) ≤ 2 ↑↑ i` (`two_pow_le_tower2`, `i ≥ 4`) together with the elementary
`2·(i+2) ≤ 2^(i+2)` (from `i+1 < 2^(i+1)`).  This is the exponent-level engine
behind the power-domination result. -/
theorem two_pow_two_mul_le_tower2 {j : ℕ} (hj : 5 ≤ j) : 2 ^ (2 * j + 2) ≤ tower2 j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [tower2_succ]
  apply Nat.pow_le_pow_right (by norm_num)
  have hi4 : 4 ≤ i := by omega
  have h := two_pow_le_tower2 hi4
  have hb : i + 1 < 2 ^ (i + 1) := lt_two_pow_aux (i + 1)
  have heq : (2 : ℕ) ^ (i + 2) = 2 * 2 ^ (i + 1) := by rw [pow_succ]; ring
  omega

/-- **`B` dominates every fixed power of `C`:** for each `p` there is a threshold
`K` (here `K = p + 6`) with `(C k)^p ≤ B k` for all `k ≥ K`.  Generalises
`C_sq_le_B` (the `p = 2` case) to arbitrary exponents, using the tetration lower
bound on `B` rather than the ad-hoc quartic estimate.  Proof: bound the `C` side
by `2^(2^(k+1)·p)` via `C_le_doubly_exp`, bound `B` below by
`2^(2 ↑↑ (k−1)) = 2 ↑↑ k` via `tower2_le_B`, and compare exponents through
`2^(k+1)·p ≤ 2^(2k')·… ≤ 2 ↑↑ (k−1)` (`two_pow_two_mul_le_tower2`, absorbing the
multiplier `p ≤ 2^{k−1}`). Certified, `native_decide`-free. -/
theorem C_pow_le_B_eventually (p : ℕ) : ∃ K, ∀ k, K ≤ k → (C k) ^ p ≤ B k := by
  refine ⟨p + 6, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj5 : 5 ≤ j := by omega
  have hjp : p ≤ j := by omega
  -- `C` side: `(C (j+1))^p ≤ 2^(2^(j+2)·p)`.
  have hC2 : (C (j + 1)) ^ p ≤ 2 ^ (2 ^ (j + 2) * p) := by
    calc (C (j + 1)) ^ p ≤ (4 ^ (2 ^ (j + 1))) ^ p :=
          Nat.pow_le_pow_left (C_le_doubly_exp (j + 1)) p
      _ = 2 ^ (2 ^ (j + 2) * p) := by
          rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          congr 1
          have h42 : (2 : ℕ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
          rw [h42]; ring
  -- exponent comparison: `2^(j+2)·p ≤ 2 ↑↑ j`.
  have hp2 : p ≤ 2 ^ j :=
    le_trans (le_of_lt (lt_two_pow_aux p)) (Nat.pow_le_pow_right (by norm_num) hjp)
  have hexp : 2 ^ (j + 2) * p ≤ tower2 j := by
    calc 2 ^ (j + 2) * p ≤ 2 ^ (j + 2) * 2 ^ j := Nat.mul_le_mul (le_refl _) hp2
      _ = 2 ^ (2 * j + 2) := by rw [← pow_add]; congr 1; ring
      _ ≤ tower2 j := two_pow_two_mul_le_tower2 hj5
  -- `B` side: `2^(2^(j+2)·p) ≤ 2^(2 ↑↑ j) = 2 ↑↑ (j+1) ≤ B (j+1)`.
  have hB2 : 2 ^ (2 ^ (j + 2) * p) ≤ B (j + 1) := by
    calc 2 ^ (2 ^ (j + 2) * p) ≤ 2 ^ tower2 j := Nat.pow_le_pow_right (by norm_num) hexp
      _ = tower2 (j + 1) := (tower2_succ j).symm
      _ ≤ B (j + 1) := tower2_le_B (j + 1)
  exact le_trans hC2 hB2

/-- **`B / C^p → ∞` for every fixed `p` (division-free form):**
`∀ p m, ∃ K, ∀ k ≥ K, m·(C k)^p ≤ B k`.  Generalises `B_div_C_diverges` (the
`p = 1` case) to arbitrary powers: the factorial certificate `B` outgrows every
fixed *polynomial* in the primorial certificate `C`, with any constant.  Proof:
absorb the multiplier as an extra factor, `m·(C k)^p ≤ (C k)^(p+1)` once
`m ≤ C k` (true for `k ≥ m` since `C k ≥ k+3`), then apply
`C_pow_le_B_eventually (p+1)`. -/
theorem B_div_C_pow_diverges (p m : ℕ) : ∃ K, ∀ k, K ≤ k → m * (C k) ^ p ≤ B k := by
  obtain ⟨K0, hK0⟩ := C_pow_le_B_eventually (p + 1)
  refine ⟨max K0 m, fun k hk => ?_⟩
  have hkK0 : K0 ≤ k := le_trans (le_max_left _ _) hk
  have hkm : m ≤ k := le_trans (le_max_right _ _) hk
  have hmC : m ≤ C k := le_trans hkm (by have := C_ge_add k; omega)
  calc m * (C k) ^ p ≤ C k * (C k) ^ p := Nat.mul_le_mul_right _ hmC
    _ = (C k) ^ (p + 1) := by rw [pow_succ]; ring
    _ ≤ B k := hK0 k hkK0

/-- **Filter-level packaging: `B k / (C k)^p → ∞` for every fixed power `p`.**
The division-free eventual bounds `C_pow_le_B_eventually` / `B_div_C_pow_diverges`
say only that `m·(C k)^p ≤ B k` eventually, for each constant `m`.  Repackaged as a
single `Filter.Tendsto … atTop atTop` statement, this is the honest analytic assertion
that the factorial certificate `B` dominates *every* fixed polynomial power of the
primorial certificate `C` — the real-valued ratio genuinely diverges to `+∞`.
Proof: `Tendsto … atTop` unfolds to `∀ M, eventually M ≤ B k / (C k)^p`; take the
constant `m = ⌈M⌉₊` in `B_div_C_pow_diverges`, then clear the (positive) denominator. -/
theorem tendsto_B_div_C_pow_atTop (p : ℕ) :
    Filter.Tendsto (fun k => (B k : ℝ) / (C k : ℝ) ^ p) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨K, hK⟩ := B_div_C_pow_diverges p ⌈M⌉₊
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  have hCpos : (0 : ℝ) < (C k : ℝ) ^ p := by
    have hC0 : 0 < C k := by have := C_ge_add k; omega
    have : (0 : ℝ) < (C k : ℝ) := by exact_mod_cast hC0
    positivity
  have hcast : (⌈M⌉₊ : ℝ) * (C k : ℝ) ^ p ≤ (B k : ℝ) := by exact_mod_cast hK k hk
  rw [le_div_iff₀ hCpos]
  calc M * (C k : ℝ) ^ p
      ≤ (⌈M⌉₊ : ℝ) * (C k : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil M) hCpos.le
    _ ≤ (B k : ℝ) := hcast

/-- **The classical ratio `B k / C k → ∞`** (the `p = 1` instance of
`tendsto_B_div_C_pow_atTop`): the factorial certificate outgrows the primorial
certificate itself, not merely additively but with unbounded ratio. -/
theorem tendsto_B_div_C_atTop :
    Filter.Tendsto (fun k => (B k : ℝ) / (C k : ℝ)) Filter.atTop Filter.atTop := by
  simpa using tendsto_B_div_C_pow_atTop 1

end DirichletsTheoremOQ02OQ03
