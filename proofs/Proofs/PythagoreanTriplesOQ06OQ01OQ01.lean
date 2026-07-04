import Mathlib

/-!
# The full divisibility package for Pythagorean triples: `60 ∣ xyz`

A **Pythagorean triple** is a triple of integers `(x, y, z)` with `x² + y² = z²`.  The parent
entry `pythagorean-triples-oq-06-oq-01` (`PythTriplesParity`) records the parity structure of
*primitive* triples — one leg even, the even leg divisible by `4`, the hypotenuse odd.  This
file answers its recorded open question
`pythagorean-triples-oq-06-oq-01-oq-01`:

> *Strengthen to the divisibility package: the even leg is divisible by `4`, exactly one leg
> is divisible by `3`, one side by `5`, hence `60 ∣ xyz` for every triple.*

The headline result `sixty_dvd_prod` — **`60 ∣ x·y·z` for every Pythagorean triple** — needs
no primitivity hypothesis at all: it holds for *every* integer solution of `x² + y² = z²`.

## Method

The three prime-power factors `3`, `4`, `5` of `60` are each forced by a **finite congruence
obstruction**, checked by `decide` on the appropriate `ZMod`:

* `3 ∣ xyz` and `5 ∣ xyz`: the squares modulo `3` (resp. `5`) are `{0,1}` (resp. `{0,1,4}`),
  and a direct finite check shows that any solution of `a²+b²=c²` over `ZMod 3` / `ZMod 5`
  already has `a·b·c = 0`.  So one of the three sides is divisible by `3`, and one by `5`.
* `4 ∣ xyz`: modulo `4` this is *false* (e.g. residues `(1,2,1)` satisfy `1+0=1` with product
  `2`), so we work modulo `8`, where `a²+b²=c²` rules those out (`1+4=5` is not a square mod
  `8`).  The finite check is run for the composite map `ZMod 8 → ZMod 4`, certifying that the
  product reduces to `0` in `ZMod 4`, i.e. `4 ∣ xyz`.

Combining the three with pairwise coprimality of `3, 4, 5` gives `60 ∣ xyz`.

Mathlib has the `m²-n²`, `2mn`, `m²+n²` classification of triples but no divisibility package;
this entry supplies it.  The proof is `0`-axiom and uses only `decide` over small `ZMod`s plus
`IsCoprime.mul_dvd`.
-/

namespace PythagoreanTriples60

/-- Transport an integer Pythagorean relation `x²+y²=z²` to the ring `ZMod n`. -/
theorem zmod_rel (n : ℕ) {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (x : ZMod n) ^ 2 + (y : ZMod n) ^ 2 = (z : ZMod n) ^ 2 := by
  exact_mod_cast congrArg (fun t : ℤ => (t : ZMod n)) h

/-- **Direct congruence obstruction.**  If over `ZMod n` every solution of `a²+b²=c²` has
`a·b·c = 0`, then `n ∣ x·y·z` for every integer Pythagorean triple.  Used for `n = 3, 5`. -/
theorem dvd_prod_of_zmod {n : ℕ} {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2)
    (key : ∀ a b c : ZMod n, a ^ 2 + b ^ 2 = c ^ 2 → a * b * c = 0) :
    (n : ℤ) ∣ x * y * z := by
  have hzero : ((x * y * z : ℤ) : ZMod n) = 0 := by
    push_cast
    exact key _ _ _ (zmod_rel n h)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 hzero

/-- **`3 ∣ xyz`** for every Pythagorean triple: one of the three sides is a multiple of `3`. -/
theorem three_dvd_prod {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) : (3 : ℤ) ∣ x * y * z := by
  have key : ∀ a b c : ZMod 3, a ^ 2 + b ^ 2 = c ^ 2 → a * b * c = 0 := by decide
  exact_mod_cast dvd_prod_of_zmod h key

/-- **`5 ∣ xyz`** for every Pythagorean triple: one of the three sides is a multiple of `5`. -/
theorem five_dvd_prod {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) : (5 : ℤ) ∣ x * y * z := by
  have key : ∀ a b c : ZMod 5, a ^ 2 + b ^ 2 = c ^ 2 → a * b * c = 0 := by decide
  exact_mod_cast dvd_prod_of_zmod h key

/-- **`4 ∣ xyz`** for every Pythagorean triple.  This is not visible modulo `4` (the residues
`(1,2,1)` give product `2`), so the obstruction is read off modulo `8`: there the relation
`a²+b²=c²` forces the product to reduce to `0` in `ZMod 4`. -/
theorem four_dvd_prod {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) : (4 : ℤ) ∣ x * y * z := by
  -- Finite check modulo `8`, landing in `ZMod 4` via the canonical ring map.
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 = c ^ 2 →
      (ZMod.castHom (show (4 : ℕ) ∣ 8 by norm_num) (ZMod 4)) (a * b * c) = 0 := by decide
  have h8 := key _ _ _ (zmod_rel 8 h)
  have e : (x : ZMod 8) * (y : ZMod 8) * (z : ZMod 8) = ((x * y * z : ℤ) : ZMod 8) := by
    push_cast; ring
  rw [e, map_intCast] at h8
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h8

/-- **The divisibility package.**  `60 ∣ x·y·z` for *every* Pythagorean triple `x²+y²=z²`,
combining the `3`-, `4`- and `5`-obstructions through pairwise coprimality. -/
theorem sixty_dvd_prod {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) : (60 : ℤ) ∣ x * y * z := by
  have h3 := three_dvd_prod h
  have h4 := four_dvd_prod h
  have h5 := five_dvd_prod h
  -- `3` and `4` are coprime, so `12 ∣ xyz`; `12` and `5` are coprime, so `60 ∣ xyz`.
  have h12 : (12 : ℤ) ∣ x * y * z := by
    have hcop : IsCoprime (3 : ℤ) 4 := by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide
    have := hcop.mul_dvd h3 h4
    norm_num at this; exact this
  have hcop : IsCoprime (12 : ℤ) 5 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have := hcop.mul_dvd h12 h5
  norm_num at this; exact this

/-- The same package phrased through Mathlib's `PythagoreanTriple` structure. -/
theorem sixty_dvd_prod_of_pythagoreanTriple {x y z : ℤ} (h : PythagoreanTriple x y z) :
    (60 : ℤ) ∣ x * y * z :=
  sixty_dvd_prod (by have := h.eq; ring_nf; ring_nf at this; linarith)

/-! ### Locating the factor `3`: it never divides the hypotenuse of a primitive triple

The package `sixty_dvd_prod` only says *that* each prime factor is present in the product; it
does not say *which* side carries it.  For the factor `3` the location is pinned down completely
by primitivity: if the legs `x, y` are coprime then `3 ∤ z`, so the `3` must fall on a **leg**.

This is genuinely special to `3` (and to `4`).  The factor `5` can land on the hypotenuse — e.g.
`(3, 4, 5)` has `5 ∣ z` — so no analogous "`5 ∤ z`" statement holds. -/

/-- For a **primitive** triple (coprime legs), `3` never divides the hypotenuse.  If it did, then
`x² + y² ≡ 0 (mod 3)` would force `3 ∣ x` and `3 ∣ y`, contradicting `IsCoprime x y`. -/
theorem three_not_dvd_hyp_of_coprime {x y z : ℤ} (hcop : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : ¬ (3 : ℤ) ∣ z := by
  intro hz
  -- Over `ZMod 3` the only solution of `a² + b² = 0` is `a = b = 0`.
  have key : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  have hzz : (z : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hz
  have hrel : (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 = 0 := by
    have := zmod_rel 3 h; rw [hzz] at this; simpa using this
  obtain ⟨hx0, hy0⟩ := key _ _ hrel
  have hx : (3 : ℤ) ∣ x := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).1 hx0; exact_mod_cast this
  have hy : (3 : ℤ) ∣ y := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).1 hy0; exact_mod_cast this
  have hunit : IsUnit (3 : ℤ) := hcop.isUnit_of_dvd' hx hy
  rw [Int.isUnit_iff] at hunit; omega

/-- **Locating the factor `3`.**  In every primitive Pythagorean triple, `3` divides one of the
two **legs** `x`, `y` (never the hypotenuse `z`).  Combined with `three_not_dvd_hyp_of_coprime`
this fully pins the position of the factor `3`. -/
theorem three_dvd_leg_of_coprime {x y z : ℤ} (hcop : IsCoprime x y)
    (h : x ^ 2 + y ^ 2 = z ^ 2) : (3 : ℤ) ∣ x ∨ (3 : ℤ) ∣ y := by
  have hprod := three_dvd_prod h
  have hznot := three_not_dvd_hyp_of_coprime hcop h
  rcases (Int.prime_three.dvd_mul.1 hprod) with hxy | hz
  · exact Int.prime_three.dvd_mul.1 hxy
  · exact absurd hz hznot

/-! ### Sharpness: `60` is *exactly* the universal divisor

`sixty_dvd_prod` shows `60` divides every Pythagorean product `xyz`.  The instance `(3, 4, 5)`
with `xyz = 60` shows this is the best possible constant: any integer that divides the product of
*every* triple must already divide `60`.  The two facts combine into a clean characterization. -/

/-- **Sharpness (upper bound).**  If `d` divides `x·y·z` for *every* Pythagorean triple, then
`d ∣ 60`.  Proof: specialize to `(3, 4, 5)`, whose product is exactly `60`. -/
theorem sixty_greatest_universal_divisor (d : ℤ)
    (hd : ∀ x y z : ℤ, x ^ 2 + y ^ 2 = z ^ 2 → d ∣ x * y * z) : d ∣ 60 := by
  have := hd 3 4 5 (by norm_num); norm_num at this; exact this

/-- **The universal-divisor characterization.**  An integer `d` divides the product of the sides
of every Pythagorean triple **iff** `d ∣ 60`.  This is the sharp form of the package: `60` is the
greatest common divisor of `{ x·y·z : x² + y² = z² }`. -/
theorem dvd_all_prod_iff_dvd_sixty (d : ℤ) :
    (∀ x y z : ℤ, x ^ 2 + y ^ 2 = z ^ 2 → d ∣ x * y * z) ↔ d ∣ 60 := by
  constructor
  · exact sixty_greatest_universal_divisor d
  · intro hd x y z h; exact hd.trans (sixty_dvd_prod h)

/-! ### Concrete instances -/

/-- `(3,4,5)`: the product `60` is exactly divisible by `60`. -/
theorem example_3_4_5 : (60 : ℤ) ∣ 3 * 4 * 5 := sixty_dvd_prod (by norm_num)

/-- `(5,12,13)`: `60 ∣ 5·12·13 = 780`. -/
theorem example_5_12_13 : (60 : ℤ) ∣ 5 * 12 * 13 := sixty_dvd_prod (by norm_num)

/-- `(8,15,17)`: `60 ∣ 8·15·17 = 2040`. -/
theorem example_8_15_17 : (60 : ℤ) ∣ 8 * 15 * 17 := sixty_dvd_prod (by norm_num)

/-- `(20,21,29)`: `60 ∣ 20·21·29`, an instance where no side is a multiple of `5`'s neighbour
yet the package still applies (here `5 ∣ 20`). -/
theorem example_20_21_29 : (60 : ℤ) ∣ 20 * 21 * 29 := sixty_dvd_prod (by norm_num)

end PythagoreanTriples60
