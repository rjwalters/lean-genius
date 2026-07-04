import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Proofs.Hilbert9CyclotomicReciprocity

/-!
# Hilbert's Ninth Problem: the quadratic subfield of `ℚ(ζ_p)` via the quadratic character

The gallery entry `Proofs.Hilbert9CyclotomicReciprocity` establishes the cyclotomic
reciprocity isomorphism

`galEquivUnits : Gal(ℚ(ζ_p)/ℚ) ≃* (ℤ/p)ˣ`,

the abelian, fully-verified instance of Artin reciprocity over `ℚ`.  This file makes precise
the classical statement that `ℚ(ζ_p)` contains a **unique quadratic subfield** `ℚ(√p*)`
(with `p* = (-1)^{(p-1)/2} p`), and that the Galois correspondence identifies it with the
subgroup of squares in `(ℤ/p)ˣ`.

The bridge is Mathlib's quadratic character `quadraticChar (ZMod p) : MulChar (ZMod p) ℤ`,
whose restriction to units is the Legendre symbol `a ↦ (a / p)`.  Composing it with
`galEquivUnits` gives the **quadratic-subfield sign** homomorphism

`quadraticSubfieldSign : Gal(ℚ(ζ_p)/ℚ) →* ℤˣ = {±1}`,

which records whether an automorphism `σ` fixes or swaps `±√p*`.

## Main results

* `quadraticSubfieldSign` — the sign homomorphism `Gal(ℚ(ζ_p)/ℚ) →* ℤˣ`.
* `coe_quadraticSubfieldSign` — its value is the quadratic character of `galEquivUnits σ`.
* `quadraticSubfieldSign_eq_one_iff` — `σ` lands in `+1` **iff** the corresponding residue
  `galEquivUnits σ` is a **square** mod `p` (i.e. `σ` fixes `√p*`).
* `quadraticSubfieldSign_eq_neg_one_iff` — `σ` lands in `-1` iff the residue is a
  **non-square** (i.e. `σ` swaps `±√p*`).
* `quadraticSubfieldSign_eq_legendreSym` — the sign is exactly the **Legendre symbol**
  `(a / p)` of any integer `a` representing the residue `galEquivUnits σ`.
* `quadraticSubfieldSign_surjective` — the sign hits both `±1`, so the image has order `2`.
* `ker_quadraticSubfieldSign_index` — the kernel (squares ↔ automorphisms fixing `√p*`) has
  **index exactly `2`**: the fixed subgroup of a genuine *quadratic* subfield.

## References

* K. Conrad, "Quadratic reciprocity and the quadratic subfield of `ℚ(ζ_p)`".
* Mathlib: `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic`,
  `Mathlib.NumberTheory.LegendreSymbol.Basic` (`legendreSym`).
-/

open Hilbert9CyclotomicReciprocity

namespace Hilbert9QuadraticSubfield

variable (p : ℕ) [Fact p.Prime] [NeZero p]

/-- **The quadratic-subfield sign homomorphism.**  Composing the reciprocity isomorphism
`galEquivUnits : Gal(ℚ(ζ_p)/ℚ) ≃* (ℤ/p)ˣ` with the quadratic character
`(ℤ/p)ˣ →* ℤˣ` yields a homomorphism to `{±1}` measuring whether an automorphism `σ` fixes
or swaps `±√p*` inside the unique quadratic subfield `ℚ(√p*) ⊆ ℚ(ζ_p)`. -/
noncomputable def quadraticSubfieldSign :
    (CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom.comp (galEquivUnits p).toMonoidHom

/-- The value of the sign is the quadratic character evaluated at the residue
`galEquivUnits σ ∈ (ℤ/p)ˣ`. -/
theorem coe_quadraticSubfieldSign
    (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) :
    ((quadraticSubfieldSign p σ : ℤ)) =
      quadraticChar (ZMod p) ((galEquivUnits p σ : (ZMod p)ˣ) : ZMod p) :=
  MulChar.coe_toUnitHom _ _

/-- **The identity automorphism has sign `+1`** — it fixes `√p*`. -/
@[simp] theorem quadraticSubfieldSign_one :
    quadraticSubfieldSign p 1 = 1 :=
  map_one _

/-- **Squares fix the quadratic subfield.**  The sign of `σ` is `+1` iff the corresponding
residue `galEquivUnits σ` is a square mod `p`.  This is the Galois-theoretic content of
"the quadratic subfield of `ℚ(ζ_p)` corresponds to the squares in `(ℤ/p)ˣ`". -/
theorem quadraticSubfieldSign_eq_one_iff
    (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) :
    quadraticSubfieldSign p σ = 1 ↔
      IsSquare ((galEquivUnits p σ : (ZMod p)ˣ) : ZMod p) := by
  rw [← Units.val_eq_one, coe_quadraticSubfieldSign]
  exact quadraticChar_one_iff_isSquare (Units.ne_zero _)

/-- **Non-squares swap `±√p*`.**  The sign of `σ` is `-1` iff the corresponding residue is a
non-square mod `p`. -/
theorem quadraticSubfieldSign_eq_neg_one_iff
    (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) :
    quadraticSubfieldSign p σ = -1 ↔
      ¬ IsSquare ((galEquivUnits p σ : (ZMod p)ˣ) : ZMod p) := by
  rw [Units.ext_iff, coe_quadraticSubfieldSign, Units.val_neg, Units.val_one]
  exact quadraticChar_neg_one_iff_not_isSquare

/-- **The sign is the Legendre symbol.**  For any integer `a` representing the residue
`galEquivUnits σ` mod `p`, the quadratic-subfield sign equals the Legendre symbol `(a / p)`.
This is the classical bridge between the abstract Galois action and the elementary symbol. -/
theorem quadraticSubfieldSign_eq_legendreSym
    (σ : CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) (a : ℤ)
    (ha : (a : ZMod p) = ((galEquivUnits p σ : (ZMod p)ˣ) : ZMod p)) :
    ((quadraticSubfieldSign p σ : ℤ)) = legendreSym p a := by
  rw [coe_quadraticSubfieldSign, ← ha]
  rfl

/-- **The sign takes both values `±1`.**  For an odd prime `p` there exist automorphisms of
`ℚ(ζ_p)` fixing `√p*` and automorphisms swapping `±√p*`, so the image of the sign is the full
order-`2` group `{±1}`. -/
theorem quadraticSubfieldSign_surjective (hp2 : p ≠ 2) :
    Function.Surjective (quadraticSubfieldSign p) := by
  intro y
  rcases Int.units_eq_one_or y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · obtain ⟨u, hu⟩ :=
      quadraticChar_exists_neg_one' (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    refine ⟨(galEquivUnits p).symm u, ?_⟩
    rw [Units.ext_iff, coe_quadraticSubfieldSign, MulEquiv.apply_symm_apply, hu,
      Units.val_neg, Units.val_one]

/-- **The quadratic subfield is genuinely quadratic.**  The kernel of the sign — the subgroup
of automorphisms fixing `√p*`, equivalently the squares in `(ℤ/p)ˣ` — has **index exactly
`2`**.  This certifies that `ℚ(ζ_p)` contains a unique quadratic subfield. -/
theorem ker_quadraticSubfieldSign_index (hp2 : p ≠ 2) :
    (quadraticSubfieldSign p).ker.index = 2 := by
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (quadraticSubfieldSign_surjective p hp2),
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

end Hilbert9QuadraticSubfield
