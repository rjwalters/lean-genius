import Mathlib

/-
# The `(n-2)! mod n` companion, a ZMod-free Wilson primality test, and Kempner's bound

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-01`)**: the parent entry
`wilsons-theorem-oq-05-oq-01` established the complete trichotomy of the
classical Wilson remainder `(n - 1)! % n` (prime ⟹ `n-1`, `n = 4` ⟹ `2`,
composite `≠ 4` ⟹ `0`).  Its registered open questions ask, first, to turn that
classification into a genuine ZMod-free primality *criterion*, and more broadly
to study the neighbouring factorial residues.  This entry does both, and in the
process proves a result strictly stronger than the parent's composite branch.

## The sharpening: one factorial step earlier

The parent's composite content is `n ∣ (n-1)!` for composite `n ≠ 4`.  In fact
the divisibility already holds at `(n-2)!`:

  `dvd_factorial_sub_two_of_not_prime`: `2 ≤ n → ¬ n.Prime → n ≠ 4 → n ∣ (n-2)!`.

The proof is the parent's engine `mul_dvd_factorial` (two *distinct* factors
below `m` multiply into `m!`) applied with `m = n - 2`: writing `n = p·q` with
`p = minFac n`, both factors stay `≤ n - 2` once `n ≥ 6` (the lone exception
`n = 4 = 2²` is exactly where `2` and `2·2` first fail to fit below `n - 2`).
The parent's `n ∣ (n-1)!` then follows for free, since `(n-2)! ∣ (n-1)!`.

This yields the **companion trichotomy** of the *previous* factorial:

  `(n - 2)! % n =  1`   if `n` is prime         (the Wilson companion residue),
  `(n - 2)! % n =  2`   if `n = 4`,
  `(n - 2)! % n =  0`   if `n` is composite and `n ≠ 4`.

The prime value `1` is exactly `((n-1)! / (n-1)) mod n`: Wilson gives
`(n-1)! ≡ -1` and `n - 1 ≡ -1`, so the cofactor `(n-2)! ≡ 1`.

## A ZMod-free Wilson primality test

Combining the prime branch with the (now strictly stronger) composite branch
gives decidable, `ZMod`-free biconditionals:

  `prime_iff_factorial_pred_mod`     : `2 ≤ n → (n.Prime ↔ (n-1)! % n = n - 1)`,
  `prime_iff_factorial_sub_two_mod`  : `2 ≤ n → (n.Prime ↔ (n-2)! % n = 1)`.

## Kempner / Smarandache threshold

The composite divisibility, paired with `Nat.Prime.dvd_factorial`, pins down
exactly when *some* factorial below `n` is already a multiple of `n` — i.e. when
the Kempner–Smarandache function `S(n) = min {m : n ∣ m!}` drops below `n`:

  `exists_lt_dvd_factorial_iff`: `2 ≤ n → ((∃ m < n, n ∣ m!) ↔ (¬ n.Prime ∧ n ≠ 4))`.

So `S(n) < n` precisely for composite `n ≠ 4`; for primes and for `4` the first
factorial divisible by `n` is `n!` itself.

Fully machine-checked: `0` sorries, `0` axioms beyond `propext`,
`Classical.choice`, `Quot.sound` (the `n = 4` values are closed by kernel
`decide`, never `native_decide`).  The prime branch is transported from
Mathlib's `ZMod.wilsons_lemma`.
-/

namespace WilsonsTheoremOQ05OQ01OQ01

open Nat
open scoped Nat

set_option linter.unusedSectionVars false

/-! ## Part 0: the divisibility engine (parent's `mul_dvd_factorial`) -/

/-- Two *distinct* positive factors below `m` multiply into `m!`: if
`0 < a < b ≤ m` then `a * b ∣ m !`.  Proof: `a ∣ (b-1)!` (as `a ≤ b-1`), so
`a * b ∣ b * (b-1)! = b!`, and `b! ∣ m!` since `b ≤ m`. -/
theorem mul_dvd_factorial {a b m : ℕ} (ha : 0 < a) (hab : a < b) (hbm : b ≤ m) :
    a * b ∣ m ! := by
  have hbfac : b ! = b * (b - 1)! := by
    cases b with
    | zero => exact absurd hab (Nat.not_lt_zero a)
    | succ k => simp [Nat.factorial_succ]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial ha (show a ≤ b - 1 by omega)
  have hab_dvd : a * b ∣ b ! := ⟨c, by rw [hbfac, hc]; ring⟩
  exact dvd_trans hab_dvd (Nat.factorial_dvd_factorial hbm)

/-! ## Part I: the sharper composite divisibility `n ∣ (n-2)!` -/

/-- **The sharpening.**  For a composite `n ≥ 2` with `n ≠ 4`, the modulus
divides the factorial of `n - 2` (one step earlier than the parent's `(n-1)!`).
Writing `n = p·q` with `p = minFac n`: if `p < q` the two distinct factors
`p, q` both lie `≤ n - 2`; if `p = q` then `n = p²` with `p ≥ 3`, and the
distinct factors `p, 2p` lie `≤ n - 2`.  The boundary `n = 4 = 2²` is precisely
where `2` and `2·2 = 4` no longer fit below `n - 2`. -/
theorem dvd_factorial_sub_two_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n)
    (h4 : n ≠ 4) : n ∣ (n - 2)! := by
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  obtain ⟨q, hq⟩ := Nat.minFac_dvd n
  set p := n.minFac with hp_def
  have hp2 : 2 ≤ p := hp.two_le
  have hp_lt : p < n := by
    rcases (Nat.minFac_le (show 0 < n by omega)).lt_or_eq with h | h
    · exact h
    · exact absurd (Nat.prime_def_minFac.mpr ⟨h2, h⟩) hnp
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exfalso; interval_cases q <;> omega
    · exact h
  have hq_dvd : q ∣ n := ⟨p, by rw [hq, mul_comm]⟩
  have hpq_le : p ≤ q := by
    have := Nat.minFac_le_of_dvd hq2 hq_dvd; rwa [← hp_def] at this
  rcases hpq_le.lt_or_eq with hlt | heq
  · -- distinct factors `p < q`, both `≤ n - 2`: `n = p*q ∣ (n-2)!`.
    have hq3 : 3 ≤ q := by omega
    have h2q : 2 * q ≤ n := by rw [hq]; exact Nat.mul_le_mul hp2 (le_refl q)
    have hqn2 : q ≤ n - 2 := by omega
    have hdvd := mul_dvd_factorial (show 0 < p by omega) hlt hqn2
    rwa [← hq] at hdvd
  · -- `n = p²`, and `p ≥ 3` since `n ≠ 4`: use the distinct factors `p < 2p`.
    have hn_sq : n = p * p := by rw [hq, heq]
    have hp3 : 3 ≤ p := by
      by_contra h; push_neg at h
      have hp_eq : p = 2 := by omega
      rw [hp_eq] at hn_sq; omega
    have h3p : 3 * p ≤ p * p := Nat.mul_le_mul hp3 (le_refl p)
    have h2pn2 : 2 * p ≤ n - 2 := by omega
    have hdvd := mul_dvd_factorial (show 0 < p by omega)
      (show p < 2 * p by omega) h2pn2
    exact dvd_trans ⟨2, by rw [hn_sq]; ring⟩ hdvd

/-- The parent's composite branch `n ∣ (n-1)!` now follows for free, since
`(n - 2)! ∣ (n - 1)!`.  This documents that the `(n-2)!` divisibility is
*strictly stronger* than the parent's `(n-1)!` divisibility. -/
theorem dvd_factorial_pred_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n)
    (h4 : n ≠ 4) : n ∣ (n - 1)! :=
  dvd_trans (dvd_factorial_sub_two_of_not_prime h2 hnp h4)
    (Nat.factorial_dvd_factorial (by omega))

/-! ## Part II: the prime branches via `ZMod.wilsons_lemma` -/

/-- **The Wilson companion residue.**  For a prime `n`, `(n - 2)! % n = 1`.
In `ZMod n`, Wilson gives `(n-1)! = -1` and `n - 1 = -1`; since
`(n-1)! = (n-1)·(n-2)!` we get `-1 = (-1)·(n-2)!`, hence `(n-2)! = 1`. -/
theorem factorial_sub_two_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 2)! % n = 1 := by
  haveI : Fact n.Prime := ⟨hp⟩
  have h2 : 2 ≤ n := hp.two_le
  have hn1 : (1 : ℕ) ≤ n := hp.one_lt.le
  -- `(n-1)! = (n-1) * (n-2)!`
  have hsplit : (n - 1)! = (n - 1) * (n - 2)! := by
    have h : n - 1 = (n - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
  -- casts into `ZMod n`
  have ecast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have ewil : ((n - 1)! : ZMod n) = -1 := ZMod.wilsons_lemma n
  have eprod : ((n - 1)! : ZMod n)
      = ((n - 1 : ℕ) : ZMod n) * ((n - 2)! : ZMod n) := by
    rw [hsplit, Nat.cast_mul]
  rw [ewil, ecast, neg_one_mul] at eprod
  -- `eprod : -1 = -((n-2)! : ZMod n)`
  have hx : ((n - 2)! : ZMod n) = 1 := (neg_inj.mp eprod).symm
  have hmod : (n - 2)! ≡ 1 [MOD n] := by
    have hcast : ((n - 2)! : ZMod n) = ((1 : ℕ) : ZMod n) := by rw [hx, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have h1 : (1 : ℕ) % n = 1 := Nat.mod_eq_of_lt (by omega)
  rwa [Nat.ModEq, h1] at hmod

/-- Re-derivation of the parent's prime branch (`wilsons-theorem-oq-05`):
for a prime `n`, `(n - 1)! % n = n - 1`.  Transported from `ZMod.wilsons_lemma`
via `((n-1 : ℕ) : ZMod n) = -1`. -/
theorem factorial_pred_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 1)! % n = n - 1 := by
  haveI : Fact n.Prime := ⟨hp⟩
  have hn1 : (1 : ℕ) ≤ n := hp.one_lt.le
  have ecast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hmod : (n - 1)! ≡ n - 1 [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff, ecast]; exact ZMod.wilsons_lemma n
  rwa [Nat.ModEq, Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hmod

/-! ## Part III: the companion trichotomy of `(n-2)!` -/

/-- **The companion trichotomy of `(n - 2)! mod n`.**  For every `n ≥ 2`:

* `1` when `n` is prime (the Wilson companion residue),
* `2` at the single exception `n = 4`,
* `0` for every other (composite) `n`.

A classification of the factorial one step below the classical Wilson factorial,
sharper than the parent on the composite side. -/
theorem factorial_sub_two_mod {n : ℕ} (hn : 2 ≤ n) :
    (n - 2)! % n = if n.Prime then 1 else if n = 4 then 2 else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]; exact factorial_sub_two_mod_of_prime hp
  · rw [if_neg hp]
    by_cases h4 : n = 4
    · subst h4; rw [if_pos rfl]; decide
    · rw [if_neg h4]
      exact Nat.dvd_iff_mod_eq_zero.mp (dvd_factorial_sub_two_of_not_prime hn hp h4)

/-! ## Part IV: ZMod-free Wilson primality criteria -/

/-- **ZMod-free Wilson primality test.**  For `n ≥ 2`, `n` is prime iff the
classical Wilson remainder hits its maximal value: `(n - 1)! % n = n - 1`.
A decidable primality criterion using only natural-number factorial arithmetic.
(Forward: Wilson.  Backward: for `n = 4` the residue is `2 ≠ 3`, and for
composite `n ≠ 4` it is `0 ≠ n - 1`.) -/
theorem prime_iff_factorial_pred_mod {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 1)! % n = n - 1 := by
  constructor
  · intro hp; exact factorial_pred_mod_of_prime hp
  · intro h
    by_contra hnp
    by_cases h4 : n = 4
    · subst h4; revert h; decide
    · have : (n - 1)! % n = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp (dvd_factorial_pred_of_not_prime hn hnp h4)
      omega

/-- **ZMod-free Wilson companion primality test.**  For `n ≥ 2`, `n` is prime
iff `(n - 2)! % n = 1`.  (Forward: the companion residue.  Backward: for
`n = 4` the residue is `2`, and for composite `n ≠ 4` it is `0`.) -/
theorem prime_iff_factorial_sub_two_mod {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 2)! % n = 1 := by
  constructor
  · intro hp; exact factorial_sub_two_mod_of_prime hp
  · intro h
    by_contra hnp
    by_cases h4 : n = 4
    · subst h4; revert h; decide
    · have : (n - 2)! % n = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp (dvd_factorial_sub_two_of_not_prime hn hnp h4)
      omega

/-! ## Part V: the Kempner–Smarandache threshold -/

/-- **Kempner / Smarandache threshold.**  For `n ≥ 2`, some factorial *strictly
below* `n` is already divisible by `n` iff `n` is composite and `n ≠ 4`:

  `(∃ m < n, n ∣ m!) ↔ (¬ n.Prime ∧ n ≠ 4)`.

Equivalently, the Kempner–Smarandache function `S(n) = min {m : n ∣ m!}`
satisfies `S(n) < n` exactly for composite `n ≠ 4`; for primes and for `4`,
the first factorial divisible by `n` is `n!` itself.

Witness for the composite side: `m = n - 2` via `dvd_factorial_sub_two_of_not_prime`.
Necessity: a prime `n` divides `m!` only when `n ≤ m` (`Nat.Prime.dvd_factorial`),
contradicting `m < n`; and for `n = 4` no `m < 4` has `4 ∣ m!`. -/
theorem exists_lt_dvd_factorial_iff {n : ℕ} (hn : 2 ≤ n) :
    (∃ m < n, n ∣ m !) ↔ (¬ Nat.Prime n ∧ n ≠ 4) := by
  constructor
  · rintro ⟨m, hmn, hdvd⟩
    refine ⟨fun hp => ?_, fun h4 => ?_⟩
    · -- a prime divides `m!` only if `n ≤ m`
      have : n ≤ m := (Nat.Prime.dvd_factorial hp).mp hdvd
      omega
    · -- `n = 4`: check `m < 4` exhaustively
      subst h4
      interval_cases m <;> revert hdvd <;> decide
  · rintro ⟨hnp, h4⟩
    exact ⟨n - 2, by omega, dvd_factorial_sub_two_of_not_prime hn hnp h4⟩

end WilsonsTheoremOQ05OQ01OQ01
