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
