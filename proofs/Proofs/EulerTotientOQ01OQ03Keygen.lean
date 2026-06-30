/-
  OQ-01-OQ-03 (key generation): existence of the RSA private exponent
  (euler-totient-oq-01-oq-03)

  The parent file `EulerTotientOQ01OQ03.lean` proves RSA *decryption correctness*:
  for `n = p·q` and exponents with `e·d = 1 + k·λ(n)`, decryption recovers every
  message (`a^(e·d) = a` for all `a : ZMod n`).  That theorem takes the private
  exponent `d` (and the witness `k`) as a *hypothesis*.

  The remaining leg named in the open question is **key generation**: a valid
  private exponent must *exist* from the public data alone.  RSA key generation
  picks the public exponent `e` coprime to `λ(n)` and sets `d ≡ e⁻¹ (mod λ(n))`.
  This file supplies the existence statement and threads it into decryption:

  • `exists_private_exponent` — from `gcd(e, λ) = 1` (and `λ > 1`, which holds for
    every RSA modulus since `λ(p·q) = lcm(p-1, q-1) ≥ 2`), there exist `d, k` with
    `e·d = 1 + k·λ`.  This is the modular inverse of `e` in `(ZMod λ)ˣ`, lifted to
    a natural-number witness.
  • `rsa_keygen_decrypt` — combining the two, from `gcd(e, λ) = 1` alone (no
    hand-supplied `d`/`k`) there exists a private exponent `d` for which
    decryption recovers every message.  This is the full "key generation +
    decryption" round trip for `λ`-based RSA.

  Status: 0 axioms, 0 sorries.  Builds on `Proofs.EulerTotientOQ01OQ03`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Proofs.EulerTotientOQ01OQ03

namespace EulerTotientOQ01OQ03

/-- **RSA key generation (existence of the private exponent).**  If the public
    exponent `e` is coprime to the universal exponent `lam` (with `lam > 1`, as
    holds for every RSA modulus), then there exist a private exponent `d` and a
    witness `k` with `e·d = 1 + k·lam`.  Concretely `d` is the modular inverse of
    `e` in `(ZMod lam)ˣ`, lifted to `ℕ`. -/
theorem exists_private_exponent {lam e : ℕ} (hlam : 1 < lam)
    (he : Nat.Coprime e lam) : ∃ d k : ℕ, e * d = 1 + k * lam := by
  haveI : NeZero lam := ⟨by omega⟩
  -- `e` is a unit in `ZMod lam`; take `d` to be a natural representative of `e⁻¹`.
  let u : (ZMod lam)ˣ := ZMod.unitOfCoprime e he
  refine ⟨((↑u⁻¹ : ZMod lam)).val, ?_⟩
  set d : ℕ := ((↑u⁻¹ : ZMod lam)).val with hd
  -- `e * d ≡ 1` in `ZMod lam`.
  have hcast : (e : ZMod lam) * (d : ZMod lam) = 1 := by
    have h1 : (e : ZMod lam) = (↑u : ZMod lam) := (ZMod.coe_unitOfCoprime e he).symm
    have h2 : (d : ZMod lam) = (↑u⁻¹ : ZMod lam) := by
      rw [hd]; exact ZMod.natCast_zmod_val _
    rw [h1, h2]; exact Units.mul_inv u
  -- Reflect back to a congruence in `ℕ`.
  have hmod : e * d ≡ 1 [MOD lam] := by
    have hc : ((e * d : ℕ) : ZMod lam) = ((1 : ℕ) : ZMod lam) := by push_cast; rw [hcast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  -- `e * d ≥ 1`, hence we may subtract and read off `k`.
  have hone : (1 : ℕ) % lam = 1 := Nat.one_mod_eq_one.mpr (by omega)
  have hmod' : e * d % lam = 1 := by
    have := hmod; rw [Nat.ModEq] at this; rw [this, hone]
  have hge : 1 ≤ e * d := le_trans (by rw [hmod']) (Nat.mod_le _ _)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hge).mp hmod.symm
  exact ⟨k, by rw [Nat.mul_comm k lam]; omega⟩

/-- **RSA: key generation + decryption.**  For `n = p·q` (distinct primes) and a
    universal exponent `lam > 1` divisible by both `p-1` and `q-1` (e.g.
    `lam = λ(n) = lcm(p-1, q-1)`), any public exponent `e` coprime to `lam`
    admits a private exponent `d` for which decryption recovers every message:
    `a^(e·d) = a` for all `a : ZMod (p·q)`.  No `d`/`k` is supplied by hand — its
    existence follows from `gcd(e, lam) = 1`. -/
theorem rsa_keygen_decrypt {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hcop : Nat.Coprime p q) (a : ZMod (p * q)) {lam e : ℕ}
    (hlam : 1 < lam) (hp : (p - 1) ∣ lam) (hq : (q - 1) ∣ lam)
    (he : Nat.Coprime e lam) :
    ∃ d : ℕ, a ^ (e * d) = a := by
  obtain ⟨d, k, hed⟩ := exists_private_exponent hlam he
  exact ⟨d, rsa_decrypt_correct hcop a hp hq hed⟩

end EulerTotientOQ01OQ03
