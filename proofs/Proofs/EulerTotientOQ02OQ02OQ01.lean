/-
# The Carmichael Function λ(n) is the TRUE Universal Exponent of (ℤ/nℤ)ˣ  (OQ02-OQ02-OQ01)

The parent entry `euler-totient-oq-02-oq-02` proves that **`φ(n)` is a universal
exponent**: the multiplicative order of every unit of `ℤ/nℤ` divides `φ(n)`, so
`a^φ(n) ≡ 1 (mod n)` for every `a` coprime to `n` (`orderOf_unit_dvd_totient`).
But `φ(n)` is *not* the smallest such exponent in general. The genuinely minimal
universal exponent is the **Carmichael function** (reduced totient)

    λ(n) := exponent of the group (ℤ/nℤ)ˣ,

which Mathlib packages as `ArithmeticFunction.Carmichael`. Mathlib develops λ
purely group-theoretically (a formula through the prime factorisation). This file
supplies the piece the parent's number-theoretic world needs: the **arithmetic
`ModEq` characterisation of λ as the least universal exponent**, and the sharp
**λ = φ ⟺ (ℤ/nℤ)ˣ cyclic** boundary that separates the Carmichael function from
Euler's totient.

## Main results

1. `carmichael_modEq` — λ(n) *is* a universal exponent, in `ℕ`/`ModEq` form:
   `a^λ(n) ≡ 1 (mod n)` for every `a` coprime to `n`. (The arithmetic shadow of
   Mathlib's group statement `pow_carmichael`.)
2. `carmichael_dvd_iff` — the **exact characterisation**: `λ(n) ∣ m` **iff** `m`
   is a universal exponent (`∀ a coprime, a^m ≡ 1 (mod n)`). This says λ(n) is
   the generator of the ideal of all universal exponents.
3. `carmichael_isLeast_universal` — packaged conclusion: λ(n) is the **least**
   positive universal exponent. This is precisely "λ(n) is the *true* universal
   exponent", the content the parent's `φ(n)` only approximates.
4. `orderOf_unit_dvd_totient_via_carmichael` — the parent's main theorem
   re-derived *through* the sharper λ: `orderOf a ∣ λ(n) ∣ φ(n)`.
5. `pow_mod_carmichael_modEq` — exponents reduce modulo λ(n) (not just φ(n)):
   `a^k ≡ a^(k % λ(n)) (mod n)`. The sharpest form of fast modular exponentiation.
6. `carmichael_eq_totient_iff_isCyclic` — the **boundary phenomenon**:
   `λ(n) = φ(n)` **iff** `(ℤ/nℤ)ˣ` is cyclic (iff `n` has a primitive root).
7. `carmichael_lt_totient_of_not_isCyclic` — hence λ is *strictly* smaller than φ
   exactly when the unit group is non-cyclic.
8. `carmichael_prime` / `carmichael_eight_lt_totient` — the sharp examples:
   λ(p) = φ(p) at every prime, but λ(8) = 2 < 4 = φ(8).

Only the foundational axioms `propext`, `Classical.choice`, `Quot.sound` are
used; confirmed via `#print axioms`. No `sorryAx`, no `Lean.ofReduceBool`.
-/

import Mathlib

namespace EulerTotientOQ02OQ02OQ01

open Nat Monoid ArithmeticFunction

variable {n : ℕ}

-- ============================================================
-- SECTION I: The arithmetic ⇄ group dictionary
-- ============================================================

/-- **The `ModEq`/`ZMod` bridge.** A power congruence `a^m ≡ 1 (mod n)` is the
same data as the equation `(a : ℤ/nℤ)^m = 1`. Every arithmetic statement below
is routed through this lemma. -/
theorem modEq_one_iff_cast_pow {a m : ℕ} :
    a ^ m ≡ 1 [MOD n] ↔ (a : ZMod n) ^ m = 1 := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]

-- ============================================================
-- SECTION II: λ(n) is a universal exponent (arithmetic form)
-- ============================================================

/-- **λ(n) is a universal exponent.** For `a` coprime to `n`, `a^λ(n) ≡ 1 (mod n)`.
This is the number-theoretic shadow of Mathlib's group-level `pow_carmichael`:
a coprime residue is a unit, and every unit is killed by the group exponent λ(n). -/
theorem carmichael_modEq {a : ℕ} (h : Nat.Coprime a n) :
    a ^ Carmichael n ≡ 1 [MOD n] := by
  rw [modEq_one_iff_cast_pow]
  have hu : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr h
  rw [← hu.unit_spec, ← Units.val_pow_eq_pow_val, pow_carmichael, Units.val_one]

/-- **λ(n) is nonzero** (for `n ≠ 0`): the unit group is finite, so its exponent
is positive. -/
theorem carmichael_ne_zero [NeZero n] : Carmichael n ≠ 0 := by
  rw [carmichael_eq_exponent']
  exact Monoid.exponent_ne_zero_of_finite

/-- **λ(n) is positive** (for `n ≠ 0`). -/
theorem carmichael_pos [NeZero n] : 0 < Carmichael n :=
  Nat.pos_of_ne_zero carmichael_ne_zero

-- ============================================================
-- SECTION III: λ(n) is the *least* universal exponent
-- ============================================================

/-- **The exact characterisation of λ(n).** `λ(n) ∣ m` **iff** `m` is a universal
exponent, i.e. `a^m ≡ 1 (mod n)` for every `a` coprime to `n`. In other words the
universal exponents are exactly the multiples of `λ(n)`; `λ(n)` generates them.

This is the sharp upgrade of the parent entry, where `φ(n)` is shown to be *one*
universal exponent. Here every universal exponent — `φ(n)` included — is forced
to be a multiple of `λ(n)`. -/
theorem carmichael_dvd_iff [NeZero n] {m : ℕ} :
    Carmichael n ∣ m ↔ ∀ a : ℕ, Nat.Coprime a n → a ^ m ≡ 1 [MOD n] := by
  rw [carmichael_eq_exponent']
  constructor
  · -- Multiples of the exponent kill every unit, hence every coprime residue.
    intro hdvd a ha
    rw [modEq_one_iff_cast_pow]
    have hu : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr ha
    have hpow : hu.unit ^ m = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdvd hu.unit
    rw [← hu.unit_spec, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  · -- If every coprime residue is killed by `m`, so is every unit, forcing
    -- `exponent ∣ m`.  Each unit `u` is realised by the coprime natural `u.val`.
    intro huniv
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro u
    have hmod := huniv (u : ZMod n).val (ZMod.val_coe_unit_coprime u)
    rw [modEq_one_iff_cast_pow, ZMod.natCast_zmod_val] at hmod
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hmod

/-- **Minimality.** Any *positive* universal exponent is `≥ λ(n)`. -/
theorem carmichael_le_of_universal [NeZero n] {m : ℕ} (hm : 0 < m)
    (h : ∀ a : ℕ, Nat.Coprime a n → a ^ m ≡ 1 [MOD n]) : Carmichael n ≤ m :=
  Nat.le_of_dvd hm (carmichael_dvd_iff.mpr h)

/-- **λ(n) is the TRUE universal exponent.** It is the *least* element of the set
of positive universal exponents: it is itself universal (`carmichael_modEq`) and
divides — hence is `≤` — every other one (`carmichael_le_of_universal`). This is
the precise sense in which λ(n), not φ(n), is the canonical exponent of `ℤ/nℤ`. -/
theorem carmichael_isLeast_universal [NeZero n] :
    IsLeast {m : ℕ | 0 < m ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ m ≡ 1 [MOD n]}
      (Carmichael n) := by
  refine ⟨⟨carmichael_pos, fun a ha => carmichael_modEq ha⟩, ?_⟩
  rintro m ⟨hm, h⟩
  exact carmichael_le_of_universal hm h

-- ============================================================
-- SECTION IV: λ refines the parent's φ (universal-exponent chain)
-- ============================================================

/-- **The order of a unit divides λ(n)** — the group-level refinement, sharper
than the parent's `orderOf a ∣ φ(n)` because `λ(n) ∣ φ(n)`. -/
theorem orderOf_unit_dvd_carmichael [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ∣ Carmichael n := by
  rw [carmichael_eq_exponent']
  exact Monoid.order_dvd_exponent a

/-- **The parent's theorem, re-derived through λ.** `orderOf a ∣ φ(n)` factors as
`orderOf a ∣ λ(n) ∣ φ(n)`, exhibiting λ(n) as the true bottleneck between an
element's order and `φ(n)`. -/
theorem orderOf_unit_dvd_totient_via_carmichael [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ∣ n.totient :=
  (orderOf_unit_dvd_carmichael a).trans (ArithmeticFunction.carmichael_dvd_totient n)

/-- **Exponents reduce modulo λ(n).** For `a` coprime to `n`,
`a^k ≡ a^(k % λ(n)) (mod n)`. This is strictly sharper than the parent's
reduction modulo `φ(n)`, since `λ(n) ∣ φ(n)`: it is the *smallest* period of the
sequence `k ↦ a^k (mod n)` guaranteed uniformly over all coprime bases. -/
theorem pow_mod_carmichael_modEq {a : ℕ} (h : Nat.Coprime a n) (k : ℕ) :
    a ^ k ≡ a ^ (k % Carmichael n) [MOD n] := by
  conv_lhs => rw [← Nat.mod_add_div k (Carmichael n)]
  calc a ^ (k % Carmichael n + Carmichael n * (k / Carmichael n))
      = a ^ (k % Carmichael n) * (a ^ Carmichael n) ^ (k / Carmichael n) := by
        rw [pow_add, pow_mul]
    _ ≡ a ^ (k % Carmichael n) * 1 ^ (k / Carmichael n) [MOD n] :=
        (Nat.ModEq.refl _).mul ((carmichael_modEq h).pow _)
    _ = a ^ (k % Carmichael n) := by rw [one_pow, mul_one]

-- ============================================================
-- SECTION V: The sharp boundary  λ(n) = φ(n) ⟺ (ℤ/nℤ)ˣ cyclic
-- ============================================================

/-- **The Carmichael–Euler boundary.** `λ(n) = φ(n)` **iff** `(ℤ/nℤ)ˣ` is cyclic
(equivalently, iff `n` admits a primitive root). Cyclic groups are exactly those
whose exponent equals their order, so the Carmichael function collapses onto
Euler's totient precisely on the moduli with primitive roots. -/
theorem carmichael_eq_totient_iff_isCyclic [NeZero n] :
    Carmichael n = n.totient ↔ IsCyclic (ZMod n)ˣ := by
  rw [carmichael_eq_exponent',
    show n.totient = Nat.card (ZMod n)ˣ from by
      rw [← ZMod.card_units_eq_totient, Fintype.card_eq_nat_card]]
  exact IsCyclic.iff_exponent_eq_card.symm

/-- **Strictness off the cyclic locus.** When `(ℤ/nℤ)ˣ` is non-cyclic, the
Carmichael function is *strictly* smaller than Euler's totient: `λ(n) < φ(n)`.
This is why λ, not φ, is the sharp universal exponent — φ is genuinely wasteful
whenever `n` has no primitive root. -/
theorem carmichael_lt_totient_of_not_isCyclic [NeZero n]
    (h : ¬ IsCyclic (ZMod n)ˣ) : Carmichael n < n.totient := by
  have hne : Carmichael n ≠ n.totient := fun heq =>
    h (carmichael_eq_totient_iff_isCyclic.mp heq)
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  exact lt_of_le_of_ne
    (Nat.le_of_dvd hpos (ArithmeticFunction.carmichael_dvd_totient n)) hne

-- ============================================================
-- SECTION VI: Sharp examples — equality at primes, strict at n = 8
-- ============================================================

/-- **λ(p) = φ(p) at every prime.** The unit group of a prime field is cyclic, so
the Carmichael function agrees with Euler's totient on primes: `λ(p) = φ(p)`. -/
theorem carmichael_prime {p : ℕ} (hp : p.Prime) : Carmichael p = p.totient := by
  rcases eq_or_ne p 2 with rfl | h2
  · simpa using carmichael_two_pow_of_le_two_eq_totient (n := 1) (by norm_num)
  · simpa using carmichael_pow_of_prime_ne_two 1 hp h2

/-- Explicit prime value: `λ(p) = p - 1`. -/
theorem carmichael_prime_eq_sub_one {p : ℕ} (hp : p.Prime) :
    Carmichael p = p - 1 := by
  rw [carmichael_prime hp, Nat.totient_prime hp]

/-- **λ(8) = 2** — strictly below `φ(8) = 4`. The group `(ℤ/8ℤ)ˣ ≅ ℤ/2 × ℤ/2`
is non-cyclic (`8` has no primitive root), so every unit already squares to `1`. -/
theorem carmichael_eight : Carmichael 8 = 2 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, carmichael_two_pow_of_ne_two (by norm_num)]
  norm_num

/-- **The witness of strictness.** `λ(8) = 2 < 4 = φ(8)`: the Carmichael function
genuinely improves on Euler's exponent, obtained here from the abstract
`carmichael_lt_totient_of_not_isCyclic` and the non-cyclicity of `(ℤ/8ℤ)ˣ`. -/
theorem carmichael_eight_lt_totient : Carmichael 8 < Nat.totient 8 :=
  carmichael_lt_totient_of_not_isCyclic ZMod.not_isCyclic_units_eight

end EulerTotientOQ02OQ02OQ01
