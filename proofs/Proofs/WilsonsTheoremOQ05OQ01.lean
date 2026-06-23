import Mathlib

/-
# Erdős-adjacent — Wilson's theorem OQ-05 → OQ-01: the complete ℕ remainder trichotomy

## Open question

The sibling entry `wilsons-theorem-oq-05` states Wilson's theorem in the classical,
`ZMod`-free congruence form — for `n ≥ 2`, `n` is prime iff `(n-1)! % n = n - 1`
(the natural number `n - 1` playing the role of `-1 mod n`) — but it only pins
down the **prime** value of `(n-1)! % n`.  The companion `wilsons-theorem-oq-01`
classifies the residue completely, *but in `ZMod n`* and with the `n = 4` anomaly
discharged by `native_decide` (so its classification is not axiom-free).

OQ-05's first follow-up question asks to **assemble the complete trichotomy of
`(n-1)! mod n` as a single classification theorem** — and, in keeping with OQ-05's
philosophy, to state it as an honest congruence/remainder between natural numbers,
with no `ZMod` and no `native_decide`.

## What this file proves (0 axioms, 0 sorries)

The headline is the **exact closed form of the remainder** as one `if`-expression:

* `factorial_pred_mod` :  for `2 ≤ n`,
  `(n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0`.

Every classical fact about `(n-1)! mod n` is then a corollary, all in pure `ℕ`:

* `factorial_pred_mod_trichotomy` : the disjunctive form — exactly one of
  `(n prime, % = n-1)`, `(n = 4, % = 2)`, `(n composite ≠ 4, % = 0)` holds.
* `dvd_factorial_pred_iff` : `n ∣ (n-1)!  ↔  ¬n.Prime ∧ n ≠ 4` — the divisibility
  characterisation of when the factorial vanishes (the `4` is the unique anomaly).
* `factorial_pred_mod_eq_zero_iff` : its remainder form, `(n-1)! % n = 0 ↔
  ¬n.Prime ∧ n ≠ 4`.
* `prime_iff_factorial_pred_mod` : OQ-05's primality criterion `n.Prime ↔
  (n-1)! % n = n - 1`, here re-obtained as a slice of the full classification.

## Method

The prime value is the OQ-05 bridge: Mathlib's `Nat.prime_iff_fac_equiv_neg_one`
gives `((n-1)! : ZMod n) = -1`, and `natCast_pred_eq_neg_one` identifies the
natural number `n - 1` with `-1`, so `ZMod.natCast_eq_natCast_iff` transports the
statement to `(n-1)! % n = n - 1`.  The composite value is genuine divisibility:
for composite `n ≠ 4`, writing `n = p·q` with `p = minFac n ≤ q`, either `p ≠ q`
(two distinct factors `p, q ≤ n-1`) or `n = p²` with `p ≥ 3` (the distinct factors
`p` and `2p ≤ n-1`); in both cases two distinct elements of `{1,…,n-1}` multiply to
a multiple of `n`, so `n ∣ (n-1)!` via `distinct_factors_dvd_factorial`.  The lone
exception `n = 4` (`3! = 6 ≡ 2`) is settled by `decide` — kernel computation, not
`native_decide`, so the whole development is axiom-free.

## Significance relative to the gallery

This is the `ZMod`-free counterpart of `wilsons-theorem-oq-01`'s classification and
the completion of `wilsons-theorem-oq-05`: together they give the remainder
`(n-1)! % n` an explicit, computable closed form valid for every `n ≥ 2`, proved
without axioms (no `native_decide`).

## Tags

wilson, number-theory, factorial, primality, classification, modular-arithmetic,
divisibility, elementary
-/


namespace WilsonsTheoremOQ05OQ01

open Nat
open scoped Nat

/-- The natural number `n - 1` reduces to `-1` in `ZMod n` (for `n ≥ 1`).  This is
the hinge that turns Mathlib's `ZMod`-valued Wilson statement into a congruence of
naturals. -/
theorem natCast_pred_eq_neg_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have h : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [h, ZMod.natCast_self, zero_sub]

/-- **Prime value.**  For a prime `n`, `(n-1)!` leaves remainder `n - 1` on division
by `n` — the forward half of Wilson's theorem in classical ℕ form. -/
theorem factorial_pred_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 1)! % n = n - 1 := by
  have hp2 : 2 ≤ n := hp.two_le
  have hn1 : n ≠ 1 := hp.one_lt.ne'
  have key : ((n - 1)! : ZMod n) = -1 := (Nat.prime_iff_fac_equiv_neg_one hn1).mp hp
  have h2 : ((n - 1)! : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [key, natCast_pred_eq_neg_one (by omega)]
  have hmod : (n - 1)! ≡ (n - 1) [MOD n] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  rw [Nat.ModEq] at hmod
  rwa [Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hmod

/-- `n!` expressed as the product over `{1, …, n}`. -/
theorem factorial_eq_Icc_prod (n : ℕ) : n ! = (Finset.Icc 1 n).prod id := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial_succ, ih]
    have hmem : n + 1 ∉ Finset.Icc 1 n := by simp
    have hinsert : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hinsert, Finset.prod_insert hmem, id, mul_comm]

/-- If `a ≠ b` are both in `{1, …, n}`, then `a · b ∣ n!`. -/
theorem distinct_factors_dvd_factorial {a b n : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ n) (hb : 1 ≤ b) (hb' : b ≤ n) (hab : a ≠ b) :
    a * b ∣ n ! := by
  rw [factorial_eq_Icc_prod]
  have hpair : ({a, b} : Finset ℕ).prod id = a * b := by
    rw [Finset.prod_pair hab]; rfl
  rw [← hpair]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.mem_Icc]
  rcases hx with rfl | rfl <;> omega

/-- **Composite divisibility.**  For composite `n` other than `4`, `n ∣ (n-1)!`.
The number `4` is the unique exception: `3! = 6` is not a multiple of `4`. -/
theorem composite_dvd_factorial_pred {n : ℕ}
    (hcomp : ¬ Nat.Prime n) (hn4 : n ≠ 4) (hn2 : 2 ≤ n) :
    n ∣ (n - 1)! := by
  -- composite and ≥ 2 and ≠ 4 forces n > 4
  have hn_gt : 4 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    · exact hcomp Nat.prime_two
    · exact hcomp Nat.prime_three
    · exact hn4 rfl
  have hn_pos : 0 < n := by omega
  have hn_ne_one : n ≠ 1 := by omega
  set p := n.minFac with hp_def
  have hp_prime : Nat.Prime p := Nat.minFac_prime hn_ne_one
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_gt_one : 1 < p := hp_prime.one_lt
  set q := n / p with hq_def
  have hpq : p * q = n := Nat.mul_div_cancel' hp_dvd
  have hp_sq_le : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn_pos hcomp
  have hq_ge_p : p ≤ q := by
    by_contra h
    push_neg at h
    have h1 : p * q < p * p := by nlinarith
    nlinarith
  have hq_gt_one : 1 < q := by linarith
  have hp_lt_n : p < n := by nlinarith
  have hq_lt_n : q < n := by nlinarith
  by_cases hpq_eq : p = q
  · -- Case n = p² (p = q), forcing p ≥ 3
    have hn_eq : n = p * p := by rw [← hpq, hpq_eq]
    have hp_ge_3 : p ≥ 3 := by
      by_contra h
      push_neg at h
      have hp2 : p = 2 := by omega
      rw [hp2] at hn_eq; omega
    have h2p_lt : 2 * p < p * p := by nlinarith
    have h2p_le : 2 * p ≤ n - 1 := by omega
    have hp_ne_2p : p ≠ 2 * p := by omega
    have h_prod_dvd : p * (2 * p) ∣ (n - 1)! :=
      distinct_factors_dvd_factorial (by omega) (by omega) (by omega) h2p_le hp_ne_2p
    have h_pp_dvd : p * p ∣ p * (2 * p) := ⟨2, by ring⟩
    have h_goal : p * p ∣ (n - 1)! := dvd_trans h_pp_dvd h_prod_dvd
    exact hn_eq ▸ h_goal
  · -- Case p ≠ q: two distinct factors in {1, …, n-1}
    rw [← hpq]
    exact distinct_factors_dvd_factorial (by omega) (by omega) (by omega) (by omega) hpq_eq

/-- **Wilson's theorem, complete remainder classification (ℕ form).**  For every
`n ≥ 2`, the remainder of `(n-1)!` modulo `n` is given by the explicit closed form

`(n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0`.

No `ZMod`, no `native_decide`: a computable closed form for the Wilson residue. -/
theorem factorial_pred_mod (n : ℕ) (hn : 2 ≤ n) :
    (n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0 := by
  by_cases hp : Nat.Prime n
  · rw [if_pos hp]; exact factorial_pred_mod_of_prime hp
  · rw [if_neg hp]
    by_cases h4 : n = 4
    · rw [if_pos h4]; subst h4; decide
    · rw [if_neg h4]
      have hdvd : n ∣ (n - 1)! := composite_dvd_factorial_pred hp h4 hn
      have hz : (n - 1)! ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      simpa [Nat.ModEq] using hz

/-- **Disjunctive trichotomy.**  Exactly one of three mutually exclusive cases holds
for `n ≥ 2`, each fixing the value of `(n-1)! % n`. -/
theorem factorial_pred_mod_trichotomy (n : ℕ) (hn : 2 ≤ n) :
    (Nat.Prime n ∧ (n - 1)! % n = n - 1) ∨
    (n = 4 ∧ (n - 1)! % n = 2) ∨
    (¬ Nat.Prime n ∧ n ≠ 4 ∧ (n - 1)! % n = 0) := by
  by_cases hp : Nat.Prime n
  · exact Or.inl ⟨hp, factorial_pred_mod_of_prime hp⟩
  · by_cases h4 : n = 4
    · exact Or.inr (Or.inl ⟨h4, by subst h4; decide⟩)
    · refine Or.inr (Or.inr ⟨hp, h4, ?_⟩)
      have hdvd : n ∣ (n - 1)! := composite_dvd_factorial_pred hp h4 hn
      have hz : (n - 1)! ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      simpa [Nat.ModEq] using hz

/-- **Divisibility characterisation.**  For `n ≥ 2`, `n` divides `(n-1)!` iff `n` is
composite and not `4`.  The factorial fails to be divisible exactly at the primes
(Wilson) and at the single anomaly `4`. -/
theorem dvd_factorial_pred_iff {n : ℕ} (hn : 2 ≤ n) :
    n ∣ (n - 1)! ↔ ¬ Nat.Prime n ∧ n ≠ 4 := by
  constructor
  · intro hdvd
    refine ⟨?_, ?_⟩
    · intro hp
      have hval : (n - 1)! % n = n - 1 := factorial_pred_mod_of_prime hp
      have h0 : (n - 1)! % n = 0 := by
        have hz : (n - 1)! ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr hdvd
        simpa [Nat.ModEq] using hz
      omega
    · intro h4
      subst h4
      revert hdvd
      decide
  · rintro ⟨hp, h4⟩
    exact composite_dvd_factorial_pred hp h4 hn

/-- Remainder form of the divisibility characterisation: `(n-1)! % n = 0` exactly
when `n` is composite and not `4`. -/
theorem factorial_pred_mod_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) :
    (n - 1)! % n = 0 ↔ ¬ Nat.Prime n ∧ n ≠ 4 := by
  have e : ((n - 1)! % n = 0) ↔ ((n - 1)! ≡ 0 [MOD n]) := by
    simp [Nat.ModEq]
  rw [e, Nat.modEq_zero_iff_dvd, dvd_factorial_pred_iff hn]

/-- **Wilson's primality criterion (ℕ form), recovered.**  For `n ≥ 2`, `n` is prime
iff `(n-1)! % n = n - 1` — the OQ-05 criterion, here a slice of the full
classification. -/
theorem prime_iff_factorial_pred_mod {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 1)! % n = n - 1 := by
  constructor
  · exact factorial_pred_mod_of_prime
  · intro h
    by_contra hp
    have key := factorial_pred_mod n hn
    rw [if_neg hp, h] at key
    by_cases h4 : n = 4
    · rw [if_pos h4] at key; subst h4; omega
    · rw [if_neg h4] at key; omega

end WilsonsTheoremOQ05OQ01
