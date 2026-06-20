/-
# Euler's Theorem: a^φ(n) ≡ 1 (mod n) for gcd(a, n) = 1

## What This Proves
The **Fermat–Euler theorem** in its classical totient form: for coprime `a` and
`n`,
    a ^ φ(n) ≡ 1  (mod n),
together with the **exponent-reduction corollary** that powers of a coprime base
depend only on the exponent modulo `φ(n)`:
    a ^ k ≡ a ^ (k mod φ(n))  (mod n),       and more generally
    k ≡ j (mod φ(n))  ⟹  a ^ k ≡ a ^ j  (mod n).

We also recover **Fermat's little theorem** (`a^(p-1) ≡ 1 mod p` for prime `p`)
as the special case `φ(p) = p - 1`, and exhibit the equivalent statement in the
unit group `(ZMod n)ˣ`, `u ^ φ(n) = 1`, tying the number-theoretic `ModEq` form
to the Lagrange/`pow_card` group form.

## Why It Is Distinct
The gallery's `euler-totient-oq-01` formalizes the *finer* Carmichael statement
`a^λ(n) ≡ 1`, and `lagrange-theorem-oq-07` derives Euler/Fermat abstractly from a
finite-group exponent. This entry is framed directly through Euler's totient `φ`
and foregrounds the **exponent-reduction corollary** — the arithmetic engine
behind modular exponentiation and RSA — which neither sibling states.

## Approach
Everything reduces to two Mathlib facts and elementary `ModEq` bookkeeping:
- `Nat.ModEq.pow_totient`  : `a.Coprime n → a ^ φ n ≡ 1 [MOD n]`.
- `Nat.pow_totient_mod`    : `a ^ k % n = a ^ (k % φ n) % n` (i.e. the `ModEq`
  reduction, unfolded), and the units form `ZMod.pow_totient`.

## Mathlib Dependencies
- `Nat.totient`, `Nat.Coprime`, `Nat.ModEq`
- `Nat.ModEq.pow_totient`, `Nat.pow_totient_mod`, `Nat.totient_prime`
- `ZMod.pow_totient`, `ZMod.unitOfCoprime`

Sorry-free and axiom-free.
-/
import Mathlib

open Nat

namespace EulerTotientOQ05

/-! ### Euler's theorem (ModEq form) -/

/-- **Euler's theorem.** If `a` is coprime to `n`, then `a ^ φ(n) ≡ 1 (mod n)`.
This is the totient generalization of Fermat's little theorem. -/
theorem euler_theorem {a n : ℕ} (h : a.Coprime n) : a ^ φ n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-! ### The exponent-reduction corollary -/

/-- **Exponent reduction.** For a base coprime to `n > 1`, a power depends only on
the exponent modulo `φ(n)`: `a ^ k ≡ a ^ (k mod φ(n)) (mod n)`. This is the
identity that makes modular exponentiation (and RSA decryption) work. -/
theorem pow_mod_totient {a n k : ℕ} (hn : 1 < n) (h : a.Coprime n) :
    a ^ k ≡ a ^ (k % φ n) [MOD n] :=
  Nat.pow_totient_mod hn h

/-- **Exponent congruence.** Coprime powers agree whenever the exponents agree
modulo `φ(n)`: if `k ≡ j (mod φ(n))` then `a ^ k ≡ a ^ j (mod n)`. -/
theorem pow_congr_of_modEq_totient {a n k j : ℕ} (hn : 1 < n) (h : a.Coprime n)
    (hkj : k ≡ j [MOD φ n]) : a ^ k ≡ a ^ j [MOD n] := by
  have hmod : k % φ n = j % φ n := hkj
  calc a ^ k ≡ a ^ (k % φ n) [MOD n] := pow_mod_totient hn h
    _ = a ^ (j % φ n) := by rw [hmod]
    _ ≡ a ^ j [MOD n] := (pow_mod_totient hn h).symm

/-- A `k + φ(n)` step in the exponent is invisible mod `n` for a coprime base:
`a ^ (k + φ(n)) ≡ a ^ k (mod n)`. The period of `k ↦ a^k mod n` divides `φ(n)`. -/
theorem pow_add_totient {a n k : ℕ} (hn : 1 < n) (h : a.Coprime n) :
    a ^ (k + φ n) ≡ a ^ k [MOD n] :=
  Nat.pow_add_totient_mod_eq hn h

/-! ### Fermat's little theorem as the prime case -/

/-- **Fermat's little theorem** recovered as the `φ(p) = p - 1` instance of
Euler's theorem: for prime `p` and `a` coprime to `p`, `a ^ (p-1) ≡ 1 (mod p)`. -/
theorem fermat_little {a p : ℕ} (hp : p.Prime) (h : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← Nat.totient_prime hp]
  exact euler_theorem h

/-! ### The unit-group form and its agreement with the `ModEq` form -/

/-- **Euler's theorem, unit-group form.** Every unit of `ZMod n` is killed by the
`φ(n)`-th power: `u ^ φ(n) = 1`. This is the Lagrange/`pow_card` statement, since
`|(ZMod n)ˣ| = φ(n)`. -/
theorem euler_units {n : ℕ} (u : (ZMod n)ˣ) : u ^ φ n = 1 :=
  ZMod.pow_totient u

/-- The `ModEq` and unit-group forms are the same theorem: pushing the coprime
base `a` into the unit group `(ZMod n)ˣ` via `ZMod.unitOfCoprime` and applying
`euler_units` reproduces `a ^ φ(n) ≡ 1 (mod n)`. -/
theorem euler_theorem_via_units {a n : ℕ} (h : a.Coprime n) :
    a ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one,
    ← ZMod.coe_unitOfCoprime a h, ← Units.val_pow_eq_pow_val,
    euler_units (ZMod.unitOfCoprime a h), Units.val_one]

/-! ### Concrete sanity checks (axiom-free `decide`) -/

/-- `3 ^ φ(10) = 3^4 = 81 ≡ 1 (mod 10)`. -/
example : 3 ^ φ 10 ≡ 1 [MOD 10] := by decide

/-- `2 ^ φ(9) = 2^6 = 64 ≡ 1 (mod 9)`. -/
example : 2 ^ φ 9 ≡ 1 [MOD 9] := by decide

/-- Exponent reduction in action: `7 ^ 100 ≡ 7 ^ (100 mod φ(12)) = 7 ^ 0 = 1 (mod 12)`
(here `φ(12) = 4` and `100 mod 4 = 0`). -/
example : 7 ^ 100 ≡ 7 ^ (100 % φ 12) [MOD 12] := pow_mod_totient (by norm_num) (by decide)

end EulerTotientOQ05
