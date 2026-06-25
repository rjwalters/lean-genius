import Mathlib

/-!
# Pinning the location of prime factors in primitive Pythagorean triples

A **Pythagorean triple** is `(x, y, z)` with `x² + y² = z²`, and it is **primitive** when the
two legs are coprime (`IsCoprime x y`).  The parent entry
`pythagorean-triples-oq-06-oq-01-oq-01` (`PythagoreanTriples60`) proves the divisibility
*package* `60 ∣ x·y·z`: each of the primes `3`, `5` and the factor `4` divides *some* side.  Its
recorded open question `pythagorean-triples-oq-06-oq-01-oq-01-oq-01` asks to *pin the location*
of these factors for primitive triples:

> *Prove that `3` and `5` never divide the hypotenuse `z` (so the obstruction always falls on a
> leg), and that the even leg is divisible by `4`.*

## Honest correction to the open question

The claim is **only half true**, and this file proves the correct sharp statement together with
the counterexample to the false half:

* **`3` never divides `z`** (`three_not_dvd_hyp`) — TRUE. Hence `3` always lands on a leg
  (`three_dvd_leg`).
* **The even leg is divisible by `4`** (`four_dvd_even_leg`) — TRUE.
* **`5` *can* divide `z`** (`five_can_divide_hyp`) — the symmetric claim for `5` is FALSE:
  `(3, 4, 5)` is a primitive triple with `5 ∣ z`. So `5` is **not** pinned to a leg.

This `3`-versus-`5` asymmetry is not an accident: a prime `p` can be a hypotenuse exactly when
`p` is a sum of two squares, i.e. `p ≡ 1 (mod 4)`.  Here `5 = 1² + 2²` is the hypotenuse of
`(3,4,5)`, whereas `3 ≡ 3 (mod 4)` is not a sum of two squares and so can never be a hypotenuse.
The naive expectation behind the open question — that "an odd prime divisor of `xyz` is forced
onto a leg" — holds for `3` but fails for `5`.

## Method

`3 ∤ z`: if `3 ∣ z` then over `ZMod 3` the relation reads `x² + y² = 0`, and a finite check
(`decide`) shows this forces `x ≡ y ≡ 0`, so `3 ∣ x` and `3 ∣ y`, contradicting coprimality
(`IsCoprime.isUnit_of_dvd'`, since `3` is not a unit).

`4 ∣ even leg`: if a leg `x` is even then the other leg `y` and the hypotenuse `z` are odd.
Odd squares are `1 (mod 8)`, so `x² = z² − y² ≡ 0 (mod 8)`; a finite check over `ZMod 8`
(carrying the two oddness conditions as residues mod `2`) certifies `x ≡ 0 (mod 4)`.

Everything is `0`-axiom: `decide` over small `ZMod`s plus elementary divisibility.
-/

namespace PythagoreanPrimeLocation

/-- Transport an integer Pythagorean relation `x²+y²=z²` to `ZMod n`. -/
theorem zmod_rel (n : ℕ) {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (x : ZMod n) ^ 2 + (y : ZMod n) ^ 2 = (z : ZMod n) ^ 2 := by
  exact_mod_cast congrArg (fun t : ℤ => (t : ZMod n)) h

/-! ### `3` is pinned to a leg -/

/-- **`3` never divides the hypotenuse of a primitive triple.**  If `3 ∣ z` then `x²+y²≡0`
modulo `3`, forcing `3 ∣ x` and `3 ∣ y`, contradicting `IsCoprime x y`. -/
theorem three_not_dvd_hyp {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hcop : IsCoprime x y) :
    ¬ (3 : ℤ) ∣ z := by
  intro hz
  -- Over `ZMod 3`, the relation collapses to `x² + y² = 0`, whence `x ≡ y ≡ 0`.
  have hz0 : (z : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hz
  have hrel := zmod_rel 3 h
  rw [hz0] at hrel
  -- finite check: in `ZMod 3`, `a²+b²=0 → a=0 ∧ b=0`.
  have key : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨hx0, hy0⟩ := key _ _ (by rw [hrel]; ring)
  have hdx : (3 : ℤ) ∣ x := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).1 hx0
  have hdy : (3 : ℤ) ∣ y := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).1 hy0
  -- `3` divides both coprime legs, so `3` is a unit — false.
  have : IsUnit (3 : ℤ) := hcop.isUnit_of_dvd' hdx hdy
  rw [Int.isUnit_iff] at this
  omega

/-- **`3` divides one of the legs.**  Combining `3 ∣ xyz` (the parent obstruction) with
`3 ∤ z`, primality of `3` forces `3` onto a leg. -/
theorem three_dvd_leg {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hcop : IsCoprime x y) :
    (3 : ℤ) ∣ x ∨ (3 : ℤ) ∣ y := by
  -- `3 ∣ xyz` via the same `ZMod 3` obstruction as the parent entry.
  have hprod : (3 : ℤ) ∣ x * y * z := by
    have hzero : ((x * y * z : ℤ) : ZMod 3) = 0 := by
      have key : ∀ a b c : ZMod 3, a ^ 2 + b ^ 2 = c ^ 2 → a * b * c = 0 := by decide
      push_cast; exact key _ _ _ (zmod_rel 3 h)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hzero
  have hp : Prime (3 : ℤ) := by norm_num
  have hnz : ¬ (3 : ℤ) ∣ z := three_not_dvd_hyp h hcop
  -- `3 ∣ x*y*z`, `3 ∤ z`, so `3 ∣ x*y`, so `3 ∣ x` or `3 ∣ y`.
  rcases (hp.dvd_mul.mp hprod) with hxy | hz
  · exact hp.dvd_mul.mp hxy
  · exact absurd hz hnz

/-! ### The even leg is divisible by `4` -/

/-- Finite certificate over `ZMod 8`: for any solution of `a²+b²=c²` with `b` and `c` odd
(non-zero modulo `2`), the leg `a` reduces to `0` modulo `4`. -/
theorem four_dvd_even_leg_aux : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 = c ^ 2 →
    (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)) b ≠ 0 →
    (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)) c ≠ 0 →
    (ZMod.castHom (show (4 : ℕ) ∣ 8 by norm_num) (ZMod 4)) a = 0 := by decide

/-- **The even leg is divisible by `4`.**  In a primitive triple, if a leg `x` is even then the
other leg and the hypotenuse are odd; odd squares are `1 (mod 8)`, forcing `x ≡ 0 (mod 4)`. -/
theorem four_dvd_even_leg {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) (hcop : IsCoprime x y)
    (hx : (2 : ℤ) ∣ x) : (4 : ℤ) ∣ x := by
  -- The other leg `y` is odd: otherwise `2 ∣ x` and `2 ∣ y` make `2` a unit.
  have hy : ¬ (2 : ℤ) ∣ y := by
    intro hy
    have : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' hx hy
    rw [Int.isUnit_iff] at this; omega
  -- The hypotenuse `z` is odd: `2 ∣ z → 2 ∣ z² = x²+y² → 2 ∣ y²` (as `2 ∣ x²`) → `2 ∣ y`.
  have hz : ¬ (2 : ℤ) ∣ z := by
    intro hz
    apply hy
    have h2z : (2 : ℤ) ∣ z ^ 2 := Dvd.dvd.pow hz (by norm_num)
    have h2x : (2 : ℤ) ∣ x ^ 2 := Dvd.dvd.pow hx (by norm_num)
    have h2y2 : (2 : ℤ) ∣ y ^ 2 := by
      have : y ^ 2 = z ^ 2 - x ^ 2 := by linarith
      rw [this]; exact dvd_sub h2z h2x
    exact (Prime.dvd_of_dvd_pow Int.prime_two h2y2)
  -- Push the two oddness facts into `ZMod 2` residues of the `ZMod 8` casts.
  have cast2 : ∀ w : ℤ, (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)) (w : ZMod 8)
      = (w : ZMod 2) := fun w => map_intCast _ w
  have hb : (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)) (y : ZMod 8) ≠ 0 := by
    rw [cast2]; rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hy
  have hc : (ZMod.castHom (show (2 : ℕ) ∣ 8 by norm_num) (ZMod 2)) (z : ZMod 8) ≠ 0 := by
    rw [cast2]; rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hz
  -- The certificate gives `x ≡ 0 (mod 4)`.
  have h8 := four_dvd_even_leg_aux _ _ _ (zmod_rel 8 h) hb hc
  rw [map_intCast] at h8
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h8

/-! ### The `5`-asymmetry: the false half of the open question, with counterexample -/

/-- **`5` can divide the hypotenuse.**  The primitive triple `(3, 4, 5)` has `5 ∣ z`, so unlike
`3`, the prime `5` is *not* pinned to a leg.  This refutes the symmetric form of the open
question.  Structurally, `5 ≡ 1 (mod 4)` is a sum of two squares (`5 = 1²+2²`) and hence can be a
hypotenuse, whereas `3 ≡ 3 (mod 4)` cannot. -/
theorem five_can_divide_hyp :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 = z ^ 2 ∧ IsCoprime x y ∧ (5 : ℤ) ∣ z :=
  ⟨3, 4, 5, by norm_num, by rw [Int.isCoprime_iff_gcd_eq_one]; decide, by norm_num⟩

/-- For contrast, `5` still divides *some* side of every triple (the parent obstruction),
but as `five_can_divide_hyp` shows that side may be the hypotenuse. -/
theorem five_dvd_prod {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) : (5 : ℤ) ∣ x * y * z := by
  have hzero : ((x * y * z : ℤ) : ZMod 5) = 0 := by
    have key : ∀ a b c : ZMod 5, a ^ 2 + b ^ 2 = c ^ 2 → a * b * c = 0 := by decide
    push_cast; exact key _ _ _ (zmod_rel 5 h)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 hzero

/-! ### Concrete instances -/

/-- `(3,4,5)` is primitive, `3 ∤ 5`, the even leg `4` is divisible by `4`, and `5 ∣ 5`. -/
theorem example_3_4_5 :
    ¬ (3 : ℤ) ∣ 5 ∧ (4 : ℤ) ∣ 4 ∧ (5 : ℤ) ∣ 5 := by
  refine ⟨?_, ?_, ?_⟩
  · exact three_not_dvd_hyp (x := 3) (y := 4) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  · exact four_dvd_even_leg (x := 4) (y := 3) (z := 5) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num)
  · norm_num

/-- `(5,12,13)`: here `5` lands on a *leg* and `3 ∤ 13`, with even leg `12` divisible by `4`. -/
theorem example_5_12_13 : ¬ (3 : ℤ) ∣ 13 ∧ (4 : ℤ) ∣ 12 := by
  refine ⟨?_, ?_⟩
  · exact three_not_dvd_hyp (x := 5) (y := 12) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  · exact four_dvd_even_leg (x := 12) (y := 5) (z := 13) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num)

/-- `(7,24,25)`: another primitive triple with `5 ∣ z` (`25`), reinforcing that `5` is not
pinned to a leg, while `3 ∤ 25` and `4 ∣ 24`. -/
theorem example_7_24_25 : (5 : ℤ) ∣ 25 ∧ ¬ (3 : ℤ) ∣ 25 ∧ (4 : ℤ) ∣ 24 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact three_not_dvd_hyp (x := 7) (y := 24) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  · exact four_dvd_even_leg (x := 24) (y := 7) (z := 25) (by norm_num)
      (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num)

end PythagoreanPrimeLocation
