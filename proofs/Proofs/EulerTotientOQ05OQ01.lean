import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Full RSA Correctness Without Coprimality, via CRT over `n = p · q`

## What This Proves

The parent entry `euler-totient-oq-05` proves RSA correctness
`(m ^ e) ^ d ≡ m [MOD n]` **only under the hypothesis `Nat.Coprime m n`**
(its `rsa_correctness`). That hypothesis is mathematically unnecessary: real RSA
moduli are products of two distinct primes `n = p · q`, and on such a modulus
decryption recovers **every** message `m`, including the measure-zero but
cryptographically real cases where `p ∣ m` or `q ∣ m` (so `m` is *not* a unit).

This entry answers the parent's first open question verbatim — *"Prove RSA
correctness without the coprimality hypothesis on `m`, via CRT over the prime
factorization `n = pq` (the full RSA correctness theorem)"* — by the standard
prime-by-prime / Chinese-Remainder argument:

1. `pow_modEq_self_of_prime` : for a prime `p`, if `k ≡ 1 [MOD p-1]` and `0 < k`,
   then `m ^ k ≡ m [MOD p]` for **all** `m`. This is the per-prime fixed-point
   form of Fermat's little theorem (`x ↦ x ^ k` fixes every residue mod `p`),
   handling `p ∣ m` (both sides `≡ 0`) and `p ∤ m` (Fermat) uniformly.
2. `rsa_correctness_full` : with `p ≠ q` prime and the Carmichael key condition
   `e * d ≡ 1 [MOD lcm (p-1) (q-1)]`, `(m ^ e) ^ d ≡ m [MOD p * q]` for all `m`.
3. `rsa_correctness_full_phi` : the same with the classical Euler condition
   `e * d ≡ 1 [MOD (p-1) * (q-1)]` (a multiple of `lcm`, hence weaker).
4. `rsa_correctness_full_totient` : restated with `Nat.totient (p * q)` in the key
   condition, the exact strengthening of the parent's `rsa_correctness` from
   "`m` coprime to `n`" to "all `m`".

## Distinctness

The parent `rsa_correctness` requires `Nat.Coprime m n` and applies Euler's
theorem to a single modulus. The theorem here drops that hypothesis entirely and
is *strictly stronger* on `n = p · q`: it covers the non-unit messages on which
the parent statement is silent. The engine is the CRT splitting
`a ≡ b [MOD p*q] ↔ a ≡ b [MOD p] ∧ a ≡ b [MOD q]` together with the all-`m`
fixed-point lemma `pow_modEq_self_of_prime`, neither of which appears upstream.

## Mathlib foundation

`ZMod.pow_card_sub_one_eq_one`, `ZMod.natCast_eq_natCast_iff`,
`Nat.modEq_and_modEq_iff_modEq_mul`, `Nat.ModEq.of_dvd`, `Nat.modEq_iff_dvd'`,
`Nat.coprime_primes`, `Nat.totient_mul`, `Nat.totient_prime`.
-/

namespace EulerTotientOQ05OQ01

open Nat

/-! ## The all-`m` fixed-point form of Fermat's little theorem -/

/-- **Per-prime fixed point.** For a prime `p`, if the exponent `k` is `≡ 1`
modulo `p - 1` and positive, then `m ^ k ≡ m [MOD p]` for **every** natural
number `m` — no coprimality assumption.

This is the uniform version of Fermat's little theorem: the map `x ↦ x ^ k` fixes
every residue class mod `p`. When `p ∤ m`, `m ^ (p-1) ≡ 1` (Fermat) collapses the
surplus exponent; when `p ∣ m`, both `m ^ k` (since `k ≥ 1`) and `m` are `≡ 0`. -/
theorem pow_modEq_self_of_prime {p k m : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hkmod : k ≡ 1 [MOD p - 1]) : m ^ k ≡ m [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p - 1 ∣ k - 1`, so `k = (p-1) * t + 1` for some `t`.
  obtain ⟨t, ht⟩ : (p - 1) ∣ (k - 1) := (Nat.modEq_iff_dvd' hk).mp hkmod.symm
  have hk_eq : k = (p - 1) * t + 1 := by omega
  -- Transport the goal into the field `ZMod p`.
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [hk_eq, pow_add, pow_mul, pow_one]
  rcases eq_or_ne (m : ZMod p) 0 with h | h
  · -- `p ∣ m`: the left factor is killed by the trailing `* m = * 0`.
    rw [h, mul_zero]
  · -- `p ∤ m`: Fermat gives `m ^ (p-1) = 1`, so the surplus power vanishes.
    rw [ZMod.pow_card_sub_one_eq_one h, one_pow, one_mul]

/-! ## Full RSA correctness on `n = p · q` -/

/-- **Full RSA correctness (Carmichael key condition).** Let `p ≠ q` be primes,
`e, d > 0`, and suppose the RSA key relation `e * d ≡ 1 [MOD lcm (p-1) (q-1)]`
holds. Then decryption recovers **every** message: `(m ^ e) ^ d ≡ m [MOD p * q]`
for all `m`, with no coprimality hypothesis on `m`.

`lcm (p-1) (q-1)` is Carmichael's `λ(p·q)`; the relation forces `e * d ≡ 1`
modulo each of `p-1` and `q-1`, and the two per-prime congruences glue by CRT. -/
theorem rsa_correctness_full {p q e d m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hd : 0 < d)
    (hed : e * d ≡ 1 [MOD Nat.lcm (p - 1) (q - 1)]) :
    (m ^ e) ^ d ≡ m [MOD p * q] := by
  rw [← pow_mul]
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  -- CRT: a congruence mod `p*q` splits as the pair of congruences mod `p`, `q`.
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  have hed_pos : 0 < e * d := Nat.mul_pos he hd
  refine ⟨?_, ?_⟩
  · exact pow_modEq_self_of_prime hp hed_pos (hed.of_dvd (Nat.dvd_lcm_left _ _))
  · exact pow_modEq_self_of_prime hq hed_pos (hed.of_dvd (Nat.dvd_lcm_right _ _))

/-- **Full RSA correctness (classical Euler key condition).** The same conclusion
under the textbook relation `e * d ≡ 1 [MOD (p-1) * (q-1)]`. Since
`lcm (p-1) (q-1) ∣ (p-1) * (q-1)`, this hypothesis is *weaker* (the modulus is a
multiple of Carmichael's `λ`), yet still recovers every message. -/
theorem rsa_correctness_full_phi {p q e d m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hd : 0 < d)
    (hed : e * d ≡ 1 [MOD (p - 1) * (q - 1)]) :
    (m ^ e) ^ d ≡ m [MOD p * q] := by
  refine rsa_correctness_full hp hq hpq he hd ?_
  exact hed.of_dvd (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))

/-- **Full RSA correctness, `φ`-phrased.** Exactly the parent's `rsa_correctness`
key condition `e * d ≡ 1 [MOD φ(n)]`, with `n = p * q`, but now with the
coprimality hypothesis on `m` **removed**. This is the precise statement of how
the open question strengthens the parent: same hypotheses on the key, conclusion
for *all* messages. -/
theorem rsa_correctness_full_totient {p q e d m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hd : 0 < d)
    (hed : e * d ≡ 1 [MOD Nat.totient (p * q)]) :
    (m ^ e) ^ d ≡ m [MOD p * q] := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hφ : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  rw [hφ] at hed
  exact rsa_correctness_full_phi hp hq hpq he hd hed

/-! ## Worked examples

Concrete RSA round-trips on `n = p·q`, including the non-coprime message that the
parent's `rsa_correctness` cannot reach. -/

/-- The standard textbook RSA: `p = 3`, `q = 11`, `n = 33`, `φ(33) = 20`, public
`e = 7`, private `d = 3` (since `7 * 3 = 21 ≡ 1 mod 20`). Message `m = 5` is
recovered. -/
example : (5 ^ 7) ^ 3 ≡ 5 [MOD 3 * 11] := by
  refine rsa_correctness_full_totient (p := 3) (q := 11) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- The case the parent **cannot** handle: a message divisible by a prime factor.
Here `m = 6` is divisible by `p = 3`, so `Nat.Coprime 6 33` fails — yet full RSA
correctness still recovers it. -/
example : (6 ^ 7) ^ 3 ≡ 6 [MOD 3 * 11] := by
  refine rsa_correctness_full_totient (p := 3) (q := 11) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- And the message `m = 0`, the extreme non-unit, is recovered too. -/
example : (0 ^ 7) ^ 3 ≡ 0 [MOD 3 * 11] := by
  refine rsa_correctness_full_totient (p := 3) (q := 11) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

#check @pow_modEq_self_of_prime
#check @rsa_correctness_full
#check @rsa_correctness_full_phi
#check @rsa_correctness_full_totient

end EulerTotientOQ05OQ01
