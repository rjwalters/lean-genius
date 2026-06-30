import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# Wilson's theorem in classical congruence form, and an elementary primality test

**Open Question (`wilsons-theorem-oq-05`)**: state Wilson's theorem as the
two-sided primality criterion — `n` is prime iff `(n-1)! ≡ -1 (mod n)`.

Mathlib's `Nat.prime_iff_fac_equiv_neg_one` and the parent gallery entry
`Proofs/WilsonsTheorem.lean` both phrase this with the residue living in `ZMod n`:
`((n-1)! : ZMod n) = -1`.  That is the algebraically convenient form, but it is
*not* the shape in which Wilson's theorem is classically stated and used in
elementary number theory, namely as a congruence between natural numbers:

  `(n - 1)! ≡ n - 1   [MOD n]`,

equivalently the bare remainder identity `(n - 1)! % n = n - 1` (here `n - 1`
plays the role of `-1 mod n`).  This file supplies exactly that bridge, none of
whose statements mention `ZMod`:

* `prime_iff_factorial_modEq` : `2 ≤ n → (n.Prime ↔ (n-1)! ≡ n-1 [MOD n])`.
* `prime_iff_factorial_mod`   : `2 ≤ n → (n.Prime ↔ (n-1)! % n = n - 1)`, an
  elementary, `ZMod`-free primality criterion.
* `factorial_pred_mod_of_prime` : the forward remainder identity
  `n.Prime → (n-1)! % n = n - 1`.
* `not_prime_of_factorial_mod_ne` : its contrapositive, a compositeness witness.

The single technical lemma is `natCast_pred_eq_neg_one`
(`((n-1 : ℕ) : ZMod n) = -1` for `n ≥ 1`), which identifies the natural number
`n - 1` with the `ZMod n` element `-1` and lets `ZMod.natCast_eq_natCast_iff`
transport Mathlib's statement to a `Nat.ModEq`.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace WilsonsTheoremOQ05

open Nat
open scoped Nat

/-- The natural number `n - 1` reduces to `-1` in `ZMod n` (for `n ≥ 1`):
`((n - 1 : ℕ) : ZMod n) = -1`.  This is the arithmetic content of "`-1 mod n` is
`n - 1`", and the hinge that turns Mathlib's `ZMod`-valued Wilson statement into
a congruence of naturals. -/
theorem natCast_pred_eq_neg_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have h : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [h, ZMod.natCast_self, zero_sub]

/-- **Wilson's theorem, classical congruence form.**  For `n ≥ 2`, `n` is prime
if and only if `(n - 1)! ≡ n - 1 (mod n)` — the elementary statement, with the
residue expressed as the natural number `n - 1` (`= -1 mod n`) rather than an
element of `ZMod n`. -/
theorem prime_iff_factorial_modEq {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 1)! ≡ n - 1 [MOD n] := by
  have hn1 : n ≠ 1 := by omega
  rw [Nat.prime_iff_fac_equiv_neg_one hn1,
    ← natCast_pred_eq_neg_one (show 1 ≤ n by omega), ZMod.natCast_eq_natCast_iff]

/-- **Elementary primality criterion (Wilson).**  For `n ≥ 2`, `n` is prime if
and only if the remainder of `(n - 1)!` on division by `n` equals `n - 1`.  No
`ZMod` appears: this is a decision procedure phrased purely in `ℕ`. -/
theorem prime_iff_factorial_mod {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 1)! % n = n - 1 := by
  rw [prime_iff_factorial_modEq hn, Nat.ModEq, Nat.mod_eq_of_lt (show n - 1 < n by omega)]

/-- Forward direction as a remainder identity: for a prime `n`, `(n-1)!` leaves
remainder `n - 1` on division by `n`. -/
theorem factorial_pred_mod_of_prime {n : ℕ} (hp : Nat.Prime n) :
    (n - 1)! % n = n - 1 :=
  (prime_iff_factorial_mod hp.two_le).1 hp

/-- Contrapositive compositeness witness: if `(n-1)! % n ≠ n - 1` (and `n ≥ 2`),
then `n` is not prime. -/
theorem not_prime_of_factorial_mod_ne {n : ℕ}
    (h : (n - 1)! % n ≠ n - 1) : ¬ Nat.Prime n :=
  fun hp => h (factorial_pred_mod_of_prime hp)

end WilsonsTheoremOQ05
