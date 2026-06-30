import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-!
# Euler totient OQ-01 → OQ-02 → OQ-01: the Carmichael function on *odd* prime powers

The parent (`euler-totient-oq-01-oq-02`, verified) packages the Carmichael function `λ`
on prime powers, including the headline non-cyclic case `λ(2ᵏ) = 2ᵏ⁻²`. For odd primes it
records only the *coincidence* `λ(pᵏ) = φ(pᵏ)`. This sibling supplies what that coincidence
was hiding: the **explicit closed form**

> `λ(pᵏ) = pᵏ⁻¹ · (p − 1)`  for an odd prime `p` and `k ≥ 1`,

together with the structural *reason* it holds — the unit group `(ℤ/pᵏℤ)ˣ` is cyclic, so its
exponent (which is exactly `λ`) equals its order (which is exactly `φ`). We make every link of

> `(ℤ/pᵏℤ)ˣ` cyclic  ⟹  exponent = order  ⟹  `λ(pᵏ) = φ(pᵏ) = pᵏ⁻¹(p − 1)`

explicit, and exhibit a **primitive root**: a unit of order exactly `pᵏ⁻¹(p − 1)`.

This is the genuinely new content relative to the parent. Where the parent stops at
`λ(pᵏ) = φ(pᵏ)` (a value left implicit), here `λ(pᵏ)` is an honest polynomial in `p` and `k`,
the existence of a generator is proved, and the contrast with the `2`-power case (where the
group is *not* cyclic and `λ = φ/2`) is sharp.

## Main results

* `carmichael_odd_prime_pow` : `λ(pᵏ) = pᵏ⁻¹(p − 1)` for odd primes `p`, `k ≥ 1` (the OQ target).
* `carmichael_odd_prime` : `λ(p) = p − 1` (the `k = 1` specialisation).
* `isCyclic_units_odd_prime_pow` : `(ℤ/pᵏℤ)ˣ` is cyclic (the mechanism).
* `exponent_units_odd_prime_pow` : exponent `(ℤ/pᵏℤ)ˣ = #(ℤ/pᵏℤ)ˣ` (cyclic ⟹ exponent = order).
* `exists_primitiveRoot_odd_prime_pow` : a unit of order exactly `pᵏ⁻¹(p − 1)` exists.
* `carmichael_eq_totient` : `λ(pᵏ) = φ(pᵏ)` (the parent's coincidence, restated).
* `carmichael_nine`, `carmichael_twentyseven`, `carmichael_twentyfive`,
  `carmichael_seven`, `carmichael_fortynine` : concrete values `λ(9)=6`, `λ(27)=18`,
  `λ(25)=20`, `λ(7)=6`, `λ(49)=42`.
-/

namespace EulerTotientOQ01OQ02OQ01

open ArithmeticFunction Nat

/-- **The unit group of an odd prime power is cyclic.** This is the structural fact that powers
    everything below: a cyclic group has a single generator, so its exponent (the smallest `k`
    with `aᵏ = 1` for all `a`) is forced up to the full order. (Mathlib:
    `ZMod.isCyclic_units_of_prime_pow`.) -/
theorem isCyclic_units_odd_prime_pow {p : ℕ} (k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    IsCyclic (ZMod (p ^ k))ˣ :=
  ZMod.isCyclic_units_of_prime_pow p hp hodd k

/-- **Exponent = order, for the odd prime-power unit group.** In a finite cyclic group the
    exponent equals the cardinality. Since `λ(pᵏ)` is by definition the exponent of `(ℤ/pᵏℤ)ˣ`
    and `φ(pᵏ)` its cardinality, this single equality is the engine behind `λ(pᵏ) = φ(pᵏ)`. -/
theorem exponent_units_odd_prime_pow {p : ℕ} (k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Monoid.exponent (ZMod (p ^ k))ˣ = Nat.card (ZMod (p ^ k))ˣ :=
  IsCyclic.iff_exponent_eq_card.mp (isCyclic_units_odd_prime_pow k hp hodd)

/-- **`λ(pᵏ) = φ(pᵏ)` for an odd prime `p`.** The cyclic coincidence: exponent equals order,
    so the Carmichael and totient functions agree on odd prime powers — in sharp contrast with
    `λ(2ᵏ) = φ(2ᵏ)/2` for `k ≥ 3`. (Restates the parent's `carmichael_pow_of_prime_ne_two`.) -/
theorem carmichael_eq_totient {p : ℕ} (k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Carmichael (p ^ k) = (p ^ k).totient :=
  carmichael_pow_of_prime_ne_two k hp hodd

/-- **`λ(pᵏ) = pᵏ⁻¹(p − 1)` for an odd prime `p` and `k ≥ 1`** — the open question's target.
    Combine the cyclic coincidence `λ(pᵏ) = φ(pᵏ)` with the totient prime-power formula
    `φ(pᵏ) = pᵏ⁻¹(p − 1)`. The parent left `λ(pᵏ)` as the implicit value `φ(pᵏ)`; here it is an
    explicit polynomial in `p` and `k`. -/
theorem carmichael_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k) :
    Carmichael (p ^ k) = p ^ (k - 1) * (p - 1) := by
  rw [carmichael_pow_of_prime_ne_two k hp hodd, Nat.totient_prime_pow hp hk]

/-- **`λ(p) = p − 1` for an odd prime `p`** (the `k = 1` case): the full multiplicative group
    `(ℤ/pℤ)ˣ` is cyclic of order `p − 1`, so its universal exponent is `p − 1`. -/
theorem carmichael_odd_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    Carmichael p = p - 1 := by
  have h := carmichael_odd_prime_pow hp hodd (k := 1) one_pos
  simpa using h

/-- **A primitive root exists.** Cyclicity is not just an abstract exponent statement: there is
    an actual unit `g` of order exactly `pᵏ⁻¹(p − 1) = φ(pᵏ)` — a primitive root modulo `pᵏ`,
    whose powers run through every unit. -/
theorem exists_primitiveRoot_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hk : 0 < k) :
    ∃ g : (ZMod (p ^ k))ˣ, orderOf g = p ^ (k - 1) * (p - 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  haveI := isCyclic_units_odd_prime_pow k hp hodd
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (p ^ k))ˣ)
  refine ⟨g, ?_⟩
  rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]

/-- `λ(9) = 6`. -/
theorem carmichael_nine : Carmichael 9 = 6 := by
  have h := carmichael_odd_prime_pow (p := 3) (k := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `λ(27) = 18`. -/
theorem carmichael_twentyseven : Carmichael 27 = 18 := by
  have h := carmichael_odd_prime_pow (p := 3) (k := 3) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `λ(25) = 20`. -/
theorem carmichael_twentyfive : Carmichael 25 = 20 := by
  have h := carmichael_odd_prime_pow (p := 5) (k := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `λ(7) = 6`. -/
theorem carmichael_seven : Carmichael 7 = 6 := by
  have h := carmichael_odd_prime (p := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `λ(49) = 42`. -/
theorem carmichael_fortynine : Carmichael 49 = 42 := by
  have h := carmichael_odd_prime_pow (p := 7) (k := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end EulerTotientOQ01OQ02OQ01
