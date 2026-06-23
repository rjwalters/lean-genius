import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# The complete trichotomy of `(n-1)! mod n`

**Open Question (`wilsons-theorem-oq-05-oq-01`)**: assemble the *complete*
classification of the residue `(n - 1)! mod n` for every `n ≥ 2`, in the
classical natural-number form (no `ZMod`).  The parent entry
`wilsons-theorem-oq-05` supplied the prime branch — Wilson's theorem as the
remainder identity `(n - 1)! % n = n - 1 ⟺ n` prime.  What remains is the
*composite* side, which Wilson's theorem leaves open, and which turns out to be
governed by a single exception:

  `(n - 1)! % n =  n - 1`   if `n` is prime,
  `(n - 1)! % n =  2`       if `n = 4`,
  `(n - 1)! % n =  0`       if `n` is composite and `n ≠ 4`.

The mathematical content of the new (composite) case is the divisibility
`n ∣ (n - 1)!` for composite `n ≠ 4`.  Writing `n = p·q` with `p = minFac n`
its least prime factor and `q = n / p`:

* if `p < q`, then `p` and `q` are *distinct* factors below `n`, so
  `n = p·q ∣ (n-1)!`;
* if `p = q`, then `n = p²` with `p ≥ 3` (the case `p = 2`, i.e. `n = 4`, is the
  lone exception), and now `p` and `2p` are distinct factors below `n`, giving
  `2n = p·(2p) ∣ (n-1)!`, hence `n ∣ (n-1)!`.

The engine for "two distinct factors below `m` multiply into `m!`" is the small
lemma `mul_dvd_factorial` (`0 < a → a < b → b ≤ m → a*b ∣ m!`), proved from
`Nat.dvd_factorial` and `Nat.factorial_dvd_factorial`.

Main results (all `ZMod`-free):

* `mul_dvd_factorial` — distinct factors below `m` divide `m!`.
* `dvd_factorial_pred_of_not_prime` — `2 ≤ n → ¬n.Prime → n ≠ 4 → n ∣ (n-1)!`.
* `factorial_pred_mod_of_not_prime` — the composite residue is `0`.
* `factorial_pred_mod` — **the trichotomy**, a single classification theorem.
* `factorial_pred_mod_eq_zero_iff` — `(n-1)! % n = 0 ⟺ ¬n.Prime ∧ n ≠ 4`
  (for `n ≥ 2`): the residue `0` detects "composite and not `4`" exactly.

Fully machine-checked: `0` sorries, `0` axioms (the `n = 4` value is closed by
`decide`, which is kernel-checked and does **not** invoke `native_decide`).
-/

namespace WilsonsTheoremOQ05OQ01

open Nat
open scoped Nat

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

/-- **Composite divisibility (the new content).**  For a composite `n ≥ 2` with
`n ≠ 4`, the modulus divides the factorial: `n ∣ (n - 1)!`.  Equivalently, the
classical Wilson remainder `(n-1)! % n` vanishes off the single exception
`n = 4`. -/
theorem dvd_factorial_pred_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n)
    (h4 : n ≠ 4) : n ∣ (n - 1)! := by
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  obtain ⟨q, hq⟩ := Nat.minFac_dvd n
  set p := n.minFac with hp_def
  have hp2 : 2 ≤ p := hp.two_le
  -- `p = minFac n < n` because `n` is not prime.
  have hp_lt : p < n := by
    rcases (Nat.minFac_le (show 0 < n by omega)).lt_or_eq with h | h
    · exact h
    · exact absurd (Nat.prime_def_minFac.mpr ⟨h2, h⟩) hnp
  -- the cofactor `q` is ≥ 2 (else `n` would be `0` or prime).
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exfalso; interval_cases q <;> omega
    · exact h
  have hq_dvd : q ∣ n := ⟨p, by rw [hq, mul_comm]⟩
  -- `p` is the *least* prime factor, so `p ≤ q`.
  have hpq_le : p ≤ q := by
    have := Nat.minFac_le_of_dvd hq2 hq_dvd; rwa [← hp_def] at this
  have hqn : q < n := by nlinarith [hq, hp2, hq2]
  rcases hpq_le.lt_or_eq with hlt | heq
  · -- distinct factors `p < q`, both `≤ n - 1`: `n = p*q ∣ (n-1)!`.
    have hdvd := mul_dvd_factorial (show 0 < p by omega) hlt (show q ≤ n - 1 by omega)
    rwa [← hq] at hdvd
  · -- `n = p²`, and `p ≥ 3` since `n ≠ 4`: use the distinct factors `p < 2p`.
    have hn_sq : n = p * p := by rw [hq, heq]
    have hp3 : 3 ≤ p := by
      by_contra h; push_neg at h
      have hp_eq : p = 2 := by omega
      rw [hp_eq] at hn_sq; omega
    have h2p1 : 2 * p + 1 ≤ n := by nlinarith [hn_sq, hp3]
    have hdvd := mul_dvd_factorial (show 0 < p by omega)
      (show p < 2 * p by omega) (show 2 * p ≤ n - 1 by omega)
    exact dvd_trans ⟨2, by rw [hn_sq]; ring⟩ hdvd

/-- The composite branch as a remainder identity: for composite `n ≥ 2` with
`n ≠ 4`, `(n - 1)! % n = 0`.  This is the `ZMod`-free counterpart, on the
compositeness side, of the parent entry's prime remainder identity. -/
theorem factorial_pred_mod_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬ Nat.Prime n)
    (h4 : n ≠ 4) : (n - 1)! % n = 0 :=
  Nat.dvd_iff_mod_eq_zero.mp (dvd_factorial_pred_of_not_prime h2 hnp h4)

/-- Re-derivation of the prime branch (parent `wilsons-theorem-oq-05`), kept
self-contained here: for a prime `n`, `(n - 1)! % n = n - 1`.  Transported from
Mathlib's `ZMod`-valued Wilson biconditional via the identity
`((n - 1 : ℕ) : ZMod n) = -1`. -/
theorem factorial_pred_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 1)! % n = n - 1 := by
  have hn1 : (1 : ℕ) ≤ n := hp.one_lt.le
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hmod : (n - 1)! ≡ n - 1 [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff, hcast]
    exact (Nat.prime_iff_fac_equiv_neg_one hp.ne_one).mp hp
  rwa [Nat.ModEq, Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hmod

/-- **The complete trichotomy of `(n - 1)! mod n`.**  For every `n ≥ 2`, the
classical Wilson remainder is determined by the arithmetic type of `n`:

* `n - 1` when `n` is prime (Wilson's theorem),
* `2` at the single exception `n = 4`,
* `0` for every other (composite) `n`.

A single classification theorem combining the prime branch (parent
`wilsons-theorem-oq-05`) with the composite branch proved here. -/
theorem factorial_pred_mod {n : ℕ} (hn : 2 ≤ n) :
    (n - 1)! % n = if n.Prime then n - 1 else if n = 4 then 2 else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]; exact factorial_pred_mod_of_prime hp
  · rw [if_neg hp]
    by_cases h4 : n = 4
    · subst h4; rw [if_pos rfl]; decide
    · rw [if_neg h4]; exact factorial_pred_mod_of_not_prime hn hp h4

/-- The residue `0` characterizes "composite and not `4`" exactly: for `n ≥ 2`,
`(n - 1)! % n = 0 ⟺ ¬ n.Prime ∧ n ≠ 4`.  (For a prime the residue is `n - 1 ≥ 1`,
and for `n = 4` it is `2`; both are nonzero.) -/
theorem factorial_pred_mod_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) :
    (n - 1)! % n = 0 ↔ ¬ Nat.Prime n ∧ n ≠ 4 := by
  constructor
  · intro h
    refine ⟨fun hp => ?_, fun h4 => ?_⟩
    · rw [factorial_pred_mod_of_prime hp] at h; omega
    · subst h4; revert h; decide
  · rintro ⟨hnp, h4⟩; exact factorial_pred_mod_of_not_prime hn hnp h4

/-- The lone exceptional value, recorded explicitly: `(4 - 1)! % 4 = 2`.  This is
the unique `n` at which the composite residue fails to vanish, because `4 = 2²`
is too small for `2` and `2·2` to be *distinct* factors below `4`. -/
theorem four_factorial_pred_mod : (4 - 1)! % 4 = 2 := by decide

end WilsonsTheoremOQ05OQ01
