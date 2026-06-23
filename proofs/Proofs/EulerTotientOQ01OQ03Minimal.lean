/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.EulerTotientOQ01

/-
# Euler Totient OQ-01-OQ-03: minimality / sharpness of the RSA exponent λ(n)

The companion file `EulerTotientOQ01OQ03.lean` proves the *sufficiency* side of RSA
decryption: if `λ(n) ∣ m` then `a^(m+1) = a` for every `a : ZMod n` (the Carmichael
exponent works as a universal decryption exponent). This file proves the matching
*converse* — that `λ(n)` is the **minimal** such exponent.

Restricting to the units `(ZMod n)ˣ` is essential: the non-unit residues carry no
information about the exponent (`0^(m+1) = 0` for every `m`), so the round-trip holds
for non-units regardless of `m`. Over the units the identity is sharp:

    carmichael n ∣ m ↔ ∀ a : (ZMod n)ˣ, a ^ (m + 1) = a

The forward direction repackages `carmichael_pow_eq_one`; the reverse is the sharp
content, via the parent's `carmichael_minimal` (`Monoid.exponent` is the least common
exponent of the unit group). Together with the gallery's forward RSA correctness this
pins `λ(n)` as the exact threshold — no smaller universal exponent succeeds for every
message coprime to `n`.
-/

namespace EulerTotientOQ01OQ03Minimal

open CarmichaelFunction

/-- **Minimality of the Carmichael exponent for the RSA round-trip.** If the RSA
identity `a^(m+1) = a` holds for *every* unit `a : (ZMod n)ˣ`, then `λ(n) ∣ m`.
The non-unit case carries no information (`0^(m+1) = 0` always), so units are the
right test set. -/
theorem carmichael_dvd_of_unit_rsa {n : ℕ} [NeZero n] {m : ℕ}
    (h : ∀ a : (ZMod n)ˣ, a ^ (m + 1) = a) : carmichael n ∣ m := by
  apply carmichael_minimal n m
  intro a
  have ha : a * a ^ m = a := by rw [← pow_succ']; exact h a
  exact mul_left_cancel (ha.trans (mul_one a).symm)

/-- **Sharp characterisation of the universal RSA decryption exponent.** For every
modulus `n`, the round-trip `a^(m+1) = a` holds for all units `a : (ZMod n)ˣ` **iff**
the Carmichael exponent `λ(n)` divides `m`. So `λ(n)` is the minimal universal RSA
exponent — the open question's "minimal exponent" claim made precise. -/
theorem carmichael_dvd_iff_unit_rsa {n : ℕ} [NeZero n] {m : ℕ} :
    carmichael n ∣ m ↔ ∀ a : (ZMod n)ˣ, a ^ (m + 1) = a := by
  refine ⟨fun hdvd a => ?_, carmichael_dvd_of_unit_rsa⟩
  obtain ⟨k, rfl⟩ := hdvd
  rw [pow_succ', pow_mul, carmichael_pow_eq_one, one_pow, mul_one]

end EulerTotientOQ01OQ03Minimal
