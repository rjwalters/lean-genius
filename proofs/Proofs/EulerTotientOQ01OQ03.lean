/-
  OQ-01-OQ-03: Verified RSA correctness with the Carmichael function λ(n)
  (euler-totient-oq-01-oq-03)

  Open question #2 of the parent gallery entry `euler-totient-oq-01`
  ("Carmichael's Function: λ(n) and the Minimal Universal Exponent"):

    Can Carmichael's function be used to define a Lean-verified implementation of
    RSA with the correct modular exponent? A formally verified RSA needs the
    decryption-correctness theorem `m^(e·d) ≡ m (mod n)` for the *minimal*
    universal exponent `λ(n)` (rather than Euler's `φ(n)`).

  ── The mathematics ───────────────────────────────────────────────────────────

  RSA uses `n = p·q` (distinct primes), a public exponent `e` with
  `gcd(e, λ(n)) = 1`, and the private exponent `d ≡ e⁻¹ (mod λ(n))`, where
  `λ(n) = lcm(p-1, q-1)` is Carmichael's function (the parent file defines
  `λ(n) = Monoid.exponent (ZMod n)ˣ`).  Then `e·d = 1 + k·λ(n)` for some `k`, and
  decryption recovers the message:

        m^(e·d) = m^(1 + k·λ(n)) ≡ m   (mod n)   for ALL m.                  (RSA)

  The crucial point — and the reason `λ(n)` is the *right* exponent — is that
  (RSA) holds for **every** `m`, including those sharing a factor with `n`, not
  just the units.  This is what makes textbook RSA correct.

  **Proof skeleton (this file).**  By CRT `ZMod (p·q) ≃+* ZMod p × ZMod q`, it
  suffices to prove the per-prime fixed point `a^(m+1) = a` in `ZMod p` whenever
  `(p-1) ∣ m`.  That is `zmod_pow_eq_self` below:
    - `a = 0`: both sides vanish (`m+1 ≥ 1`);
    - `a ≠ 0`: `a` is a unit, Fermat gives `a^(p-1) = 1`, so
      `a^(m+1) = (a^(p-1))^t · a = a`.
  Since `(p-1) ∣ λ(n)` and `(q-1) ∣ λ(n)`, taking `m = k·λ(n)` discharges both
  components, and CRT reassembles them.

  **Squarefree is necessary.**  The all-`a` fixed point can FAIL for
  non-squarefree `n` (e.g. `n = p²`, any `a` divisible by `p`): `a^j` stays `≡ 0
  (mod p)` but need not return to `a (mod p²)`.  RSA moduli `n = p·q` are
  squarefree, so (RSA) is safe.  See
  `research/problems/euler-totient-oq-01-oq-03/verify_rsa_lambda.py` (stdlib,
  ALL PASS): correctness for all `m` over 55 moduli, `λ < φ` strictly in all of
  them, and the explicit `p²` failure set.

  ── Lean scope ────────────────────────────────────────────────────────────────

  • `zmod_pow_eq_self` — the per-prime fixed point (the proven core; Fermat +
    case split).
  • `rsa_correct` — RSA decryption correctness for `n = p·q` via CRT, stated for
    any exponent `m` with `(p-1) ∣ m` and `(q-1) ∣ m` (i.e. any multiple of
    `λ(p·q) = lcm(p-1, q-1)`).
  • `rsa_decrypt_correct` — the textbook phrasing `m^(e·d) ≡ m` once
    `e·d = 1 + k·λ`.

  Status: 0 axioms, 0 sorries.  Registered in `Proofs/Proofs.lean`.
  Machine-verified via docker-build on 2026-06-15 (the dependency
  `EulerTotientOQ01.lean` required seven Mathlib-API fixes to the Carmichael
  infrastructure first).  `ZMod.pow_card_sub_one_eq_one` takes `{a}` IMPLICITLY
  (FieldTheory/Finite/Basic.lean:605); `ZMod.chineseRemainder` confirmed
  (Data/ZMod/Basic.lean:873); the CRT componentwise step (`Prod.ext_iff` +
  `simpa` on the projection-of-power simp lemmas) typechecks.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
import Proofs.EulerTotientOQ01

open scoped Classical

namespace EulerTotientOQ01OQ03

open CarmichaelFunction

/-- **Per-prime fixed point (Fermat).** In `ZMod p` with `p` prime, if `(p-1) ∣ m`
    then `a^(m+1) = a` for *every* `a` (units and `0` alike).  This is the
    arithmetic heart of RSA decryption correctness. -/
theorem zmod_pow_eq_self {p : ℕ} [Fact p.Prime] (a : ZMod p) {m : ℕ}
    (hm : (p - 1) ∣ m) : a ^ (m + 1) = a := by
  obtain ⟨t, rfl⟩ := hm
  rcases eq_or_ne a 0 with h | h
  · subst h
    rw [zero_pow (Nat.succ_ne_zero _)]
  · rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one h, one_pow, one_mul]

/-- **RSA correctness for `n = p·q`.**  For distinct primes `p, q` and any
    exponent `m` divisible by both `p-1` and `q-1` (equivalently, any multiple of
    `λ(n) = lcm(p-1, q-1)`), the map `a ↦ a^(m+1)` is the identity on `ZMod (p·q)`:
        `a^(m+1) = a`   for ALL `a`.
    Proved componentwise through the CRT isomorphism. -/
theorem rsa_correct {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hcop : Nat.Coprime p q)
    (a : ZMod (p * q)) {m : ℕ} (hp : (p - 1) ∣ m) (hq : (q - 1) ∣ m) :
    a ^ (m + 1) = a := by
  have e := ZMod.chineseRemainder hcop
  apply e.injective
  rw [map_pow]
  have hx : (e a).1 ^ (m + 1) = (e a).1 := zmod_pow_eq_self _ hp
  have hy : (e a).2 ^ (m + 1) = (e a).2 := zmod_pow_eq_self _ hq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · simpa using hx
  · simpa using hy

/-- **Textbook RSA decryption.**  If the public/private exponents satisfy
    `e·d = 1 + k·λ` where `λ` is a common multiple of `p-1` and `q-1`
    (the Carmichael exponent of `n = p·q`), then `a^(e·d) = a` for all `a`. -/
theorem rsa_decrypt_correct {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (a : ZMod (p * q)) {e d k lam : ℕ}
    (hp : (p - 1) ∣ lam) (hq : (q - 1) ∣ lam) (hed : e * d = 1 + k * lam) :
    a ^ (e * d) = a := by
  have hp' : (p - 1) ∣ k * lam := hp.mul_left k
  have hq' : (q - 1) ∣ k * lam := hq.mul_left k
  have hexp : e * d = k * lam + 1 := by rw [hed]; ring
  rw [hexp]
  exact rsa_correct hcop a hp' hq'

/-! ### Bridge to the Carmichael function λ(n)

The results above are stated for an exponent `m` divisible by both `p-1` and
`q-1`.  The parent file (`EulerTotientOQ01.lean`) defines
`carmichael n = Monoid.exponent (ZMod n)ˣ`.  Here we identify
`λ(p·q) = lcm(λ(p), λ(q)) = lcm(p-1, q-1)` for coprime factors, so that RSA
decryption correctness can be stated directly against `carmichael (p·q)` — the
*minimal* universal exponent the open question asks about. -/

/-- **Carmichael's function is "multiplicative" on coprime factors:**
    `λ(p·q) = lcm(λ(p), λ(q))` for `Nat.Coprime p q`.

    Proof: the CRT ring iso `ZMod (p·q) ≃+* ZMod p × ZMod q` induces a group iso
    on units `(ZMod (p·q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ` (via `Units.mapEquiv` and
    `MulEquiv.prodUnits`).  The exponent is invariant under group iso
    (`Monoid.exponent_eq_of_mulEquiv`) and `Monoid.exponent_prod` evaluates the
    exponent of a product as the `lcm` of the factor exponents. -/
theorem carmichael_mul_coprime {p q : ℕ} (hcop : Nat.Coprime p q) :
    carmichael (p * q) = Nat.lcm (carmichael p) (carmichael q) := by
  have e : (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  unfold carmichael
  rw [Monoid.exponent_eq_of_mulEquiv e, Monoid.exponent_prod]
  rfl

/-- `(p-1) ∣ λ(p·q)` for distinct primes: `p-1 = λ(p)` divides `lcm(λ(p), λ(q))`. -/
theorem sub_one_dvd_carmichael_mul_left {p q : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime p q) : (p - 1) ∣ carmichael (p * q) := by
  have hp : p.Prime := Fact.out
  rw [← carmichael_prime hp, carmichael_mul_coprime hcop]
  exact Nat.dvd_lcm_left _ _

/-- `(q-1) ∣ λ(p·q)` for distinct primes: `q-1 = λ(q)` divides `lcm(λ(p), λ(q))`. -/
theorem sub_one_dvd_carmichael_mul_right {p q : ℕ} [Fact q.Prime]
    (hcop : Nat.Coprime p q) : (q - 1) ∣ carmichael (p * q) := by
  have hq : q.Prime := Fact.out
  rw [← carmichael_prime hq, carmichael_mul_coprime hcop]
  exact Nat.dvd_lcm_right _ _

/-- **RSA decryption correctness against the Carmichael exponent λ(n).**
    For `n = p·q` (distinct primes), if the exponent `m` is a multiple of
    `λ(n) = carmichael (p·q)`, then `a^(m+1) = a` for *every* `a : ZMod n`.

    This is the open question's target statement: RSA is correct with the
    minimal universal exponent `λ(n)`, not merely Euler's `φ(n)`.  Since
    `λ(n) ∣ φ(n)`, this gives a no-larger private exponent. -/
theorem rsa_correct_carmichael {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (a : ZMod (p * q)) {m : ℕ}
    (hm : carmichael (p * q) ∣ m) : a ^ (m + 1) = a :=
  rsa_correct hcop a
    ((sub_one_dvd_carmichael_mul_left hcop).trans hm)
    ((sub_one_dvd_carmichael_mul_right hcop).trans hm)

/-- RSA **encryption** with public exponent `e`: the message `a` is sent to
    `aᵉ` in `ZMod n`. -/
def rsaEncrypt {n : ℕ} (e : ℕ) (a : ZMod n) : ZMod n := a ^ e

/-- RSA **decryption** with private exponent `d`: the ciphertext `c` is sent to
    `cᵈ` in `ZMod n`. -/
def rsaDecrypt {n : ℕ} (d : ℕ) (c : ZMod n) : ZMod n := c ^ d

/-- **RSA round-trip (verified end to end).**

    Let `n = p·q` for distinct primes, and let `(e, d)` be a key pair satisfying
    the key-generation congruence `e·d ≡ 1 (mod λ(n))`, written here as
    `e·d = 1 + k·λ(n)`. Then decrypting an encrypted message recovers it for
    *every* `a : ZMod n`:
    `rsaDecrypt d (rsaEncrypt e a) = a`.

    This is the headline RSA correctness statement — encryption and decryption
    are mutual inverses — phrased directly against the minimal universal
    exponent `λ(n)`. It follows from `rsa_correct_carmichael` because
    `(aᵉ)ᵈ = a^(e·d) = a^(k·λ(n) + 1)` and `λ(n) ∣ k·λ(n)`. -/
theorem rsa_decrypt_encrypt {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (a : ZMod (p * q)) {e d k : ℕ}
    (hed : e * d = 1 + k * carmichael (p * q)) :
    rsaDecrypt d (rsaEncrypt e a) = a := by
  unfold rsaEncrypt rsaDecrypt
  rw [← pow_mul, hed, Nat.add_comm 1 (k * carmichael (p * q))]
  exact rsa_correct_carmichael hcop a (dvd_mul_left _ k)

/-! ### Key generation: discharging the congruence `e·d ≡ 1 (mod λ(n))`

The round-trip `rsa_decrypt_encrypt` above *assumes* a private exponent `d`
satisfying `e·d = 1 + k·λ(n)`.  RSA key generation must produce such a `d` from
the public exponent `e`, and it can do so precisely when `gcd(e, λ(n)) = 1`.
We discharge this hypothesis **constructively**: by Euler's theorem
`e^φ(λ) ≡ 1 (mod λ)`, so the explicit exponent `d = e^(φ(λ) − 1)` satisfies
`e·d = e^φ(λ) ≡ 1 (mod λ)`, i.e. `e·d = 1 + k·λ`.  This turns the conditional
round-trip into an unconditional *existence of a working key pair*. -/

/-- **Existence of a private exponent (modular inverse).**  If `gcd(e, λ) = 1`
    (with `e ≥ 1` and `λ ≥ 1`) then there are `d, k` with `e·d = 1 + k·λ` — i.e.
    `e` is invertible modulo `λ`, with inverse `d` realised explicitly as
    `e^(φ(λ) − 1)` via Euler's theorem.  This is the number-theoretic core of RSA
    key generation. -/
theorem exists_inverse_exponent {e lam : ℕ} (he : 1 ≤ e) (hlam : 1 ≤ lam)
    (hcop : Nat.Coprime e lam) : ∃ d k : ℕ, e * d = 1 + k * lam := by
  have htot : 1 ≤ Nat.totient lam := Nat.totient_pos.mpr hlam
  have hed : e * e ^ (Nat.totient lam - 1) = e ^ Nat.totient lam := by
    rw [← pow_succ']; congr 1; omega
  have hmod : e * e ^ (Nat.totient lam - 1) ≡ 1 [MOD lam] := by
    rw [hed]; exact Nat.ModEq.pow_totient hcop
  have hge : 1 ≤ e * e ^ (Nat.totient lam - 1) := by
    rw [hed]; exact Nat.one_le_pow _ _ he
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hge).mp hmod.symm
  exact ⟨e ^ (Nat.totient lam - 1), k, by rw [Nat.mul_comm k lam]; omega⟩

/-- **RSA key generation works (unconditional round-trip).**  For `n = p·q`
    (distinct primes) and a public exponent `e ≥ 1` coprime to `λ(n)`, there
    *exists* a private exponent `d` for which decryption inverts encryption on
    every message `a : ZMod n`:
        `rsaDecrypt d (rsaEncrypt e a) = a`   for all `a`.
    The congruence hypothesis of `rsa_decrypt_encrypt` is discharged by
    `exists_inverse_exponent`, so a usable RSA key pair always exists once
    `gcd(e, λ(n)) = 1`. -/
theorem exists_rsa_keypair {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (e : ℕ) (he : 1 ≤ e)
    (hlam : 1 ≤ carmichael (p * q))
    (hecop : Nat.Coprime e (carmichael (p * q))) :
    ∃ d : ℕ, ∀ a : ZMod (p * q), rsaDecrypt d (rsaEncrypt e a) = a := by
  obtain ⟨d, k, hed⟩ := exists_inverse_exponent he hlam hecop
  exact ⟨d, fun a => rsa_decrypt_encrypt hcop a hed⟩

end EulerTotientOQ01OQ03
