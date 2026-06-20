import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-
# Euler's Theorem in `Nat.ModEq` Form and the Exponent-Reduction Corollary

## What This Proves

The gallery's base `euler-totient` entry proves Euler's theorem as the *group*
statement `a ^ φ(n) = 1` for units `a : (ZMod n)ˣ`. This entry develops the
*computational* / *number-theoretic* face of the same theorem, working directly
with natural-number congruences `[MOD n]`:

1. `euler_theorem`        : `a ^ φ(n) ≡ 1 [MOD n]` for `Nat.Coprime a n`.
2. `euler_pow_mod_one`    : `a ^ φ(n) % n = 1` for `1 < n` and coprime `a`.
3. `exp_reduction`        : `a ^ k ≡ a ^ (k % φ(n)) [MOD n]` — **exponents may be
                            reduced modulo `φ(n)`**, the workhorse of fast modular
                            exponentiation and of RSA.
4. `exp_reduction_mod`    : the same fact in `%`-normal form.
5. `fermat_little`        : Fermat's little theorem `a ^ (p-1) ≡ 1 [MOD p]` as the
                            `n = p` prime specialization.
6. `fermat_little_full`   : `a ^ p ≡ a [MOD p]`, valid even when `p ∣ a`.
7. `orderOf_dvd_totient`  : the multiplicative order of any unit divides `φ(n)`.
8. `rsa_correctness`      : if `e * d ≡ 1 [MOD φ(n)]` then `(m ^ e) ^ d ≡ m [MOD n]`
                            for `m` coprime to `n` — the correctness of RSA
                            encryption/decryption, derived from Euler's theorem.

## Distinctness

This is deliberately disjoint from:
- the base `euler-totient` entry (units form `a ^ φ(n) = 1` in `(ZMod n)ˣ`), and
- `euler-totient-oq-01` (Carmichael's λ, the *minimal* universal exponent).

The content here is the `[MOD n]` reformulation together with exponent reduction
`a ^ k ≡ a ^ (k % φ(n))` and its cryptographic consequence (RSA correctness),
none of which appear in those entries.

## Mathlib foundation

`Nat.ModEq.pow_totient`, `Nat.pow_totient_mod`, `Nat.pow_totient_mod_eq_one`
(file `Mathlib/NumberTheory/PowModTotient.lean`), `ZMod.card_units_eq_totient`,
`orderOf_dvd_card`.
-/

namespace EulerTotientOQ05

open Nat

/-! ## Euler's theorem, congruence form -/

/-- **Euler's theorem (`Nat.ModEq` form).** For `a` coprime to `n`,
`a ^ φ(n) ≡ 1 (mod n)`. This is the number-theoretic statement underlying the
group-theoretic `a ^ φ(n) = 1` proved in the base entry. -/
theorem euler_theorem {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-- The `%`-normal form of Euler's theorem: for `1 < n` and `a` coprime to `n`,
`a ^ φ(n)` leaves remainder `1` on division by `n`. -/
theorem euler_pow_mod_one {a n : ℕ} (hn : 1 < n) (h : Nat.Coprime a n) :
    a ^ Nat.totient n % n = 1 :=
  Nat.pow_totient_mod_eq_one hn h

/-! ## Exponent reduction

The practically decisive corollary: when the base is coprime to the modulus, the
*exponent* of a modular power may be reduced modulo `φ(n)`. This is what lets one
evaluate astronomically large modular powers, and is the algebraic heart of RSA. -/

/-- **Exponent reduction.** For `1 < n` and `a` coprime to `n`,
`a ^ k ≡ a ^ (k % φ(n)) (mod n)` for every exponent `k`. -/
theorem exp_reduction {a n : ℕ} (hn : 1 < n) (h : Nat.Coprime a n) (k : ℕ) :
    a ^ k ≡ a ^ (k % Nat.totient n) [MOD n] :=
  Nat.pow_totient_mod hn h

/-- Exponent reduction in `%`-normal form: `a ^ k % n = a ^ (k % φ(n)) % n`. -/
theorem exp_reduction_mod {a n : ℕ} (hn : 1 < n) (h : Nat.Coprime a n) (k : ℕ) :
    a ^ k % n = a ^ (k % Nat.totient n) % n :=
  Nat.pow_totient_mod hn h

/-! ## Fermat's little theorem as the prime case

When `n = p` is prime, `φ(p) = p - 1`, so Euler's theorem specializes to Fermat. -/

/-- **Fermat's little theorem (`Nat.ModEq` form).** For prime `p` and `a` not
divisible by `p`, `a ^ (p-1) ≡ 1 (mod p)`. -/
theorem fermat_little {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have hco : Nat.Coprime a p := (hp.coprime_iff_not_dvd.mpr ha).symm
  have h := euler_theorem (n := p) hco
  rwa [Nat.totient_prime hp] at h

/-- **Fermat's little theorem, full form.** `a ^ p ≡ a (mod p)` for *every* `a`,
including the case `p ∣ a` where both sides vanish mod `p`. -/
theorem fermat_little_full {p : ℕ} (hp : p.Prime) (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact ZMod.pow_card (a : ZMod p)

/-! ## Order divides the totient -/

/-- The multiplicative order of any unit of `ZMod n` divides `φ(n)`. Equivalently,
`φ(n)` is a *universal* exponent for `(ZMod n)ˣ`; Carmichael's λ (oq-01) is the
*least* such exponent. -/
theorem orderOf_dvd_totient (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    orderOf u ∣ Nat.totient n := by
  rw [← ZMod.card_units_eq_totient n]
  exact orderOf_dvd_card

/-! ## RSA correctness

The capstone application. RSA picks a modulus `n` and exponents `e` (public) and
`d` (private) with `e * d ≡ 1 (mod φ(n))`. Encryption is `m ↦ m ^ e (mod n)` and
decryption `c ↦ c ^ d (mod n)`; correctness `(m ^ e) ^ d ≡ m (mod n)` is exactly
Euler's theorem applied to the surplus exponent `e * d - 1`, a multiple of `φ(n)`. -/

/-- **RSA correctness.** If `1 < n`, `1 < φ(n)`, `m` is coprime to `n`, and the
RSA key condition `e * d ≡ 1 (mod φ(n))` holds, then decrypting an encrypted
message recovers it: `(m ^ e) ^ d ≡ m (mod n)`. -/
theorem rsa_correctness {m n e d : ℕ} (hφ : 1 < Nat.totient n)
    (hm : Nat.Coprime m n) (hed : e * d ≡ 1 [MOD Nat.totient n]) :
    (m ^ e) ^ d ≡ m [MOD n] := by
  -- `e * d` leaves remainder `1` modulo `φ(n)`.
  have hmod : e * d % Nat.totient n = 1 := by
    have h1 : (1 : ℕ) % Nat.totient n = 1 := Nat.mod_eq_of_lt hφ
    have := hed
    simp only [Nat.ModEq, h1] at this
    exact this
  -- hence `e * d = φ(n) * q + 1` for `q = (e*d) / φ(n)`.
  have hsplit : e * d = Nat.totient n * (e * d / Nat.totient n) + 1 := by
    conv_lhs => rw [← Nat.div_add_mod (e * d) (Nat.totient n)]
    rw [hmod]
  rw [← pow_mul, hsplit, pow_add, pow_mul, pow_one]
  -- `(m ^ φ(n)) ^ q * m ≡ 1 ^ q * m = m  (mod n)`.
  calc (m ^ Nat.totient n) ^ (e * d / Nat.totient n) * m
      ≡ 1 ^ (e * d / Nat.totient n) * m [MOD n] :=
        ((euler_theorem hm).pow _).mul_right m
    _ = m := by rw [one_pow, one_mul]

/-! ## Worked examples (axiom-free `decide`)

Exponent reduction lets us settle large modular powers *without* evaluating them.
The example below proves `3 ^ 100 ≡ 1 (mod 10)` by collapsing the exponent to
`100 % φ(10) = 100 % 4 = 0`, never forming the 48-digit number `3 ^ 100`. -/

/-- `φ(10) = 4`. -/
example : Nat.totient 10 = 4 := by decide

/-- `3 ^ 100 ≡ 1 (mod 10)` by exponent reduction: `3 ^ 100 ≡ 3 ^ 0 = 1`. -/
example : 3 ^ 100 % 10 = 1 := by
  have h : Nat.Coprime 3 10 := by decide
  rw [exp_reduction_mod (by norm_num) h]
  norm_num [show Nat.totient 10 = 4 from by decide]

/-- `7 ^ 222 ≡ 9 (mod 10)`: reduce `222 % φ(10) = 222 % 4 = 2`, then `7 ^ 2 = 49 ≡ 9`. -/
example : 7 ^ 222 % 10 = 9 := by
  have h : Nat.Coprime 7 10 := by decide
  rw [exp_reduction_mod (by norm_num) h]
  norm_num [show Nat.totient 10 = 4 from by decide]

/-- A small RSA round-trip: `n = 15`, `φ(15) = 8`, public `e = 3`, private `d = 3`
(since `3 * 3 = 9 ≡ 1 mod 8`); message `m = 2` is recovered: `(2 ^ 3) ^ 3 ≡ 2 (mod 15)`. -/
example : (2 ^ 3) ^ 3 ≡ 2 [MOD 15] := by
  have hm : Nat.Coprime 2 15 := by decide
  have hφ : 1 < Nat.totient 15 := by decide
  have hed : 3 * 3 ≡ 1 [MOD Nat.totient 15] := by decide
  exact rsa_correctness hφ hm hed

#check @euler_theorem
#check @exp_reduction
#check @fermat_little
#check @rsa_correctness

end EulerTotientOQ05
