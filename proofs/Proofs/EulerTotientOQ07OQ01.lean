import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The exact shared power of two in `gcd(φ m, φ n)`

**Open Question (`euler-totient-oq-07-oq-01`)**: sharpen the parent lower bound
`2 ∣ gcd(φ m, φ n)` (for `m, n ≥ 3`) — when is the gcd *exactly* `2`, and when is
it larger?  The seeker phrased a candidate strengthening:

> is `gcd(φ m, φ n) ≥ 4` unless one of the arguments has totient exactly `2`
> (i.e. lies in `{3, 4, 6}`)?

This file settles the question.  The clean structural fact is that, once both
totients are even, **the single factor of `2` splits off exactly**:

  `gcd(φ m, φ n) = 2 · gcd(φ m / 2, φ n / 2)`   for `m, n ≥ 3`.

Everything else is a one-line corollary of this identity together with `omega`:

* the gcd equals `2` **iff** the halves `φ m / 2` and `φ n / 2` are coprime;
* the gcd is `≥ 4` **iff** the halves share a common factor;
* dividing the gcd by `2` gives the gcd of the halves on the nose.

Crucially, the identity **refutes the seeker's candidate conjecture.**  Coprimality
of the *halves* — not "one totient equals `2`" — is what controls equality.  The
explicit witness `m = 5, n = 7` has `gcd(φ 5, φ 7) = gcd(4, 6) = 2` with **both**
totients `≥ 4`, so neither argument lies in `{3, 4, 6}`.  The naive strengthening
is false; the correct dividing line is the coprimality of the halved totients.

The only Mathlib inputs are `Nat.totient_even` (`φ k` is even for `k > 2`) and
`Nat.gcd_mul_left` (`gcd (k·a) (k·b) = k · gcd a b`).

## Contents

* `gcd_totient_eq_two_mul_gcd_half`    — the exact factorisation `= 2 · gcd(halves)`.
* `gcd_totient_div_two`                — `gcd(φ m, φ n) / 2 = gcd(φ m / 2, φ n / 2)`.
* `gcd_totient_eq_two_iff`             — `gcd = 2 ↔` the halves are coprime.
* `four_le_gcd_totient_iff`            — `gcd ≥ 4 ↔` the halves share a factor.
* `exists_gcd_two_with_large_totients` — the counterexample refuting the conjecture.

Fully machine-checked: `0` sorries, `0` axioms (the `decide` calls are kernel
reductions over concrete small naturals, not `native_decide`).
-/

namespace EulerTotientOQ07OQ01

open Nat

/-- **The exact factorisation.**  For `m, n ≥ 3` both totients are even, so the
common factor of `2` splits off *cleanly*:
`gcd(φ m, φ n) = 2 · gcd(φ m / 2, φ n / 2)`.

This is the structural heart of the entry: it reduces every question about the
shared factor `2` in `gcd(φ m, φ n)` to a question about the *halved* totients,
where the parity obstruction has been removed. -/
theorem gcd_totient_eq_two_mul_gcd_half {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Nat.gcd (φ m) (φ n) = 2 * Nat.gcd (φ m / 2) (φ n / 2) := by
  have em : 2 ∣ φ m := Even.two_dvd (totient_even (by omega))
  have en : 2 ∣ φ n := Even.two_dvd (totient_even (by omega))
  have key : Nat.gcd (φ m) (φ n)
      = Nat.gcd (2 * (φ m / 2)) (2 * (φ n / 2)) := by
    rw [Nat.mul_div_cancel' em, Nat.mul_div_cancel' en]
  rw [key, Nat.gcd_mul_left]

/-- Dividing the gcd of the totients by `2` recovers the gcd of the halves
exactly (no rounding): `gcd(φ m, φ n) / 2 = gcd(φ m / 2, φ n / 2)`. -/
theorem gcd_totient_div_two {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Nat.gcd (φ m) (φ n) / 2 = Nat.gcd (φ m / 2) (φ n / 2) := by
  rw [gcd_totient_eq_two_mul_gcd_half hm hn]; omega

/-- **Characterisation of equality `gcd = 2`.**  For `m, n ≥ 3`,
`gcd(φ m, φ n) = 2` holds *iff* the halved totients `φ m / 2` and `φ n / 2` are
coprime.  This is the correct dividing line for the sharp lower bound — not the
seeker's "one totient equals `2`" guess. -/
theorem gcd_totient_eq_two_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Nat.gcd (φ m) (φ n) = 2 ↔ Nat.gcd (φ m / 2) (φ n / 2) = 1 := by
  rw [gcd_totient_eq_two_mul_gcd_half hm hn]; omega

/-- **Characterisation of `gcd ≥ 4`.**  For `m, n ≥ 3` the gcd exceeds the
universal bound `2` (in fact reaches `≥ 4`) *iff* the halved totients share a
common factor `≥ 2`. -/
theorem four_le_gcd_totient_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    4 ≤ Nat.gcd (φ m) (φ n) ↔ 2 ≤ Nat.gcd (φ m / 2) (φ n / 2) := by
  rw [gcd_totient_eq_two_mul_gcd_half hm hn]; omega

/-- **Refutation of the seeker's candidate conjecture.**  One might guess that
`gcd(φ m, φ n) = 2` forces one of the totients to equal `2` (equivalently
`m` or `n ∈ {3, 4, 6}`).  This is **false**: the pair `m = 5, n = 7` gives
`gcd(φ 5, φ 7) = gcd(4, 6) = 2` while *both* totients are `≥ 4`.  What actually
controls equality is the coprimality of the halves (`4/2 = 2` and `6/2 = 3` are
coprime), exactly as `gcd_totient_eq_two_iff` predicts. -/
theorem exists_gcd_two_with_large_totients :
    ∃ m n : ℕ, 3 ≤ m ∧ 3 ≤ n ∧ Nat.gcd (φ m) (φ n) = 2 ∧ 4 ≤ φ m ∧ 4 ≤ φ n :=
  ⟨5, 7, by norm_num, by norm_num, by decide, by decide, by decide⟩

/-! ### Worked examples

The factorisation `gcd(φ m, φ n) = 2 · gcd(φ m / 2, φ n / 2)` in action. -/

-- Equality case, small: `φ 3 = φ 4 = 2`, halves `1, 1` coprime ⇒ `gcd = 2`.
example : Nat.gcd (φ 3) (φ 4) = 2 := by decide
example : Nat.gcd (φ 3 / 2) (φ 4 / 2) = 1 := by decide

-- The refuting witness: `φ 5 = 4`, `φ 7 = 6`, halves `2, 3` coprime ⇒ `gcd = 2`.
example : φ 5 = 4 := by decide
example : φ 7 = 6 := by decide
example : Nat.gcd (φ 5) (φ 7) = 2 := by decide

-- Larger gcd, `= 4`: `φ 5 = φ 5 = 4`, halves `2, 2` share `2` ⇒ `gcd = 2·2 = 4`.
example : Nat.gcd (φ 5) (φ 5) = 2 * Nat.gcd (φ 5 / 2) (φ 5 / 2) := by decide

-- Larger gcd, `= 6`: `φ 7 = φ 9 = 6`, halves `3, 3` share `3` ⇒ `gcd = 2·3 = 6`.
example : Nat.gcd (φ 7) (φ 9) = 6 := by decide
example : Nat.gcd (φ 7) (φ 9) = 2 * Nat.gcd (φ 7 / 2) (φ 9 / 2) := by decide

end EulerTotientOQ07OQ01
