import Mathlib
import Proofs.EulerTotientOQ01OQ01

/-
# Euler's Totient — OQ-01-OQ-01-OQ-02: Carmichael's theorem and the sharp universal exponent

## Research Problem: euler-totient-oq-01-oq-01-oq-02

The parent `euler-totient-oq-01-oq-01` introduced Carmichael's function
λ(n) = exponent of the unit group (ℤ/nℤ)* and proved its **multiplicativity**
λ(m·n) = lcm(λ(m), λ(n)) for coprime m, n.  The sibling
`euler-totient-oq-01-oq-01-oq-01` derived the **explicit value**
λ(n) = lcm_p p^(k−1)(p−1).  This leaf supplies the missing *operational content*:
the theorem that gives λ its name and its meaning as a refinement of Euler's
totient theorem.

**Carmichael's theorem.**  For every unit `a` of ℤ/nℤ,

    a ^ λ(n) = 1.

Moreover λ(n) is the *sharp* universal exponent:

* **Minimality.**  Any `k` with `a^k = 1` for all units `a` is a multiple of λ(n).
* **Attainment.**  There is a unit of order exactly λ(n) (so the bound is met).
* **Refinement of Euler.**  λ(n) ∣ φ(n), and feeding this back recovers the
  Fermat–Euler theorem `a ^ φ(n) = 1` — with λ(n), generally smaller than φ(n),
  as the true period.

We reuse the parent's definition `carmichael n = Monoid.exponent (ZMod n)ˣ`, so
each statement is a clean specialisation of Mathlib's monoid-exponent API to the
unit group, with the totient bridge `ZMod.card_units_eq_totient`.  Verified,
0 axioms.

Tags: number-theory, carmichael-function, euler-totient, exponent, units, fermat-euler
-/

namespace EulerTotientOQ01OQ01OQ02

open CarmichaelMultiplicative

/-- **Carmichael's theorem.**  Every unit of `ℤ/nℤ` is killed by λ(n):
`a ^ λ(n) = 1`.  This is the universal-exponent statement underlying
Carmichael's function (a sharpening of Euler's `a ^ φ(n) = 1`). -/
theorem unit_pow_carmichael (n : ℕ) (a : (ZMod n)ˣ) :
    a ^ carmichael n = 1 := by
  unfold carmichael
  exact Monoid.pow_exponent_eq_one a

/-- **Minimality of λ(n).**  Any common exponent `k` of the unit group — i.e. any
`k` with `a ^ k = 1` for every unit `a` — is a multiple of λ(n).  Together with
`unit_pow_carmichael` this says λ(n) is the *least* positive universal exponent. -/
theorem carmichael_dvd_of_forall_pow_eq_one (n : ℕ) {k : ℕ}
    (hk : ∀ a : (ZMod n)ˣ, a ^ k = 1) : carmichael n ∣ k := by
  unfold carmichael
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hk

/-- **Attainment / sharpness.**  For `n ≥ 1` there is a unit of `ℤ/nℤ` whose order
is exactly λ(n) (a "λ-primitive" element).  Hence the universal-exponent bound
`a ^ λ(n) = 1` is met by some element and cannot be lowered. -/
theorem exists_unit_orderOf_eq_carmichael (n : ℕ) [NeZero n] :
    ∃ a : (ZMod n)ˣ, orderOf a = carmichael n := by
  unfold carmichael
  exact Monoid.exists_orderOf_eq_exponent Monoid.ExponentExists.of_finite

/-- **λ refines φ:** Carmichael's function divides Euler's totient,
`λ(n) ∣ φ(n)`.  The exponent of a finite group divides its order, and the unit
group of `ℤ/nℤ` has order φ(n). -/
theorem carmichael_dvd_totient (n : ℕ) [NeZero n] :
    carmichael n ∣ n.totient := by
  unfold carmichael
  rw [← ZMod.card_units_eq_totient n, ← Nat.card_eq_fintype_card]
  exact Group.exponent_dvd_nat_card

/-- **Euler's theorem recovered from Carmichael.**  Since λ(n) ∣ φ(n) and
`a ^ λ(n) = 1`, every unit satisfies `a ^ φ(n) = 1` — the Fermat–Euler theorem,
now seen as a corollary of the sharper Carmichael period λ(n). -/
theorem unit_pow_totient (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    a ^ n.totient = 1 := by
  obtain ⟨m, hm⟩ := carmichael_dvd_totient n
  rw [hm, pow_mul, unit_pow_carmichael, one_pow]

end EulerTotientOQ01OQ01OQ02
