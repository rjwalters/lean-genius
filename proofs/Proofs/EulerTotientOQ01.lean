import Mathlib

/-
# Carmichael's Function: a^λ(n) ≡ 1 (mod n)

## The Open Question

Carmichael's function λ(n) is the smallest positive integer e such that
a^e ≡ 1 (mod n) for ALL a coprime to n. It satisfies λ(n) | φ(n),
with equality when n is 1, 2, 4, p^k, or 2p^k (odd prime p).

## What This Proves

1. λ(n) defined as the exponent of the multiplicative group (ℤ/nℤ)*
2. a^λ(n) ≡ 1 (mod n) for all a coprime to n
3. λ(n) | φ(n) (Carmichael divides Euler's totient)
4. λ(n) is the minimal universal exponent

## Key Insight

Carmichael's function is exactly the **exponent** of the group (ℤ/nℤ)*
in the group theory sense: the LCM of all element orders.
Mathlib's `Monoid.exponent` provides this directly.
-/

namespace CarmichaelFunction

open ZMod

/-- Carmichael's function λ(n): the exponent of the multiplicative
    group (ℤ/nℤ)*, i.e., the smallest e > 0 with a^e = 1 for all units a. -/
noncomputable def carmichael (n : ℕ) : ℕ :=
  Monoid.exponent (ZMod n)ˣ

/-- **Carmichael's Theorem**: For any a coprime to n, a^λ(n) ≡ 1 (mod n).
    This follows from the definition of group exponent. -/
theorem carmichael_pow_eq_one (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    a ^ carmichael n = 1 :=
  Monoid.pow_exponent_eq_one a

/-- λ(n) divides φ(n): Carmichael's function divides Euler's totient.
    This is because φ(n) = |(ℤ/nℤ)*| and the exponent divides the group order
    (by Lagrange's theorem). -/
theorem carmichael_dvd_totient (n : ℕ) [NeZero n] :
    carmichael n ∣ Nat.totient n := by
  unfold carmichael
  rw [show Nat.totient n = Fintype.card (ZMod n)ˣ from
    (ZMod.card_units_eq_totient n).symm]
  exact Monoid.exponent_dvd_card

/-- λ(n) is the minimal universal exponent: if a^e = 1 for all units a,
    then λ(n) | e. -/
theorem carmichael_minimal (n : ℕ) [NeZero n] (e : ℕ)
    (he : ∀ a : (ZMod n)ˣ, a ^ e = 1) :
    carmichael n ∣ e := by
  unfold carmichael
  exact Monoid.exponent_dvd_of_forall_pow_eq_one _ e he

/-- For prime p, λ(p) = p - 1 = φ(p).
    The group (ℤ/pℤ)* is cyclic of order p-1. -/
theorem carmichael_prime {p : ℕ} (hp : Nat.Prime p) :
    carmichael p = p - 1 := by
  unfold carmichael
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- (ℤ/pℤ)* is cyclic of order p-1, so its exponent is p-1
  rw [Monoid.exponent_eq_iSup_orderOf]
  -- For cyclic groups, the exponent equals the order
  rw [show Fintype.card (ZMod p)ˣ = p - 1 from by
    rw [ZMod.card_units_eq_totient]; exact Nat.totient_prime hp]
  -- In a cyclic group of order n, the exponent is n
  sorry

/-- λ(1) = 1: the trivial group has exponent 1. -/
theorem carmichael_one : carmichael 1 = 1 := by
  unfold carmichael
  exact Monoid.exponent_eq_one_of_subsingleton

/-- λ(2) = 1: the group (ℤ/2ℤ)* = {1} has exponent 1. -/
theorem carmichael_two : carmichael 2 = 1 := by
  unfold carmichael
  have h : Fintype.card (ZMod 2)ˣ = 1 := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_prime (by norm_num)
  exact Monoid.exponent_eq_one_iff.mpr
    (Fintype.card_le_one_iff_subsingleton.mp (h ▸ le_refl 1))

end CarmichaelFunction
