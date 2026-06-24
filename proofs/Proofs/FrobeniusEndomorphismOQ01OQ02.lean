/-
  The fixed field of the Frobenius endomorphism is the prime subfield.

  Parent (`FrobeniusEndomorphismOQ01`) established that over a commutative ring
  of prime characteristic `p` the Frobenius `x ↦ x ^ p` is a ring homomorphism,
  and that over `ZMod p` it is the identity (Fermat's little theorem).

  This file answers the open question: **which elements of a field `F` of
  characteristic `p` are fixed by the Frobenius?**  The answer is the cleanest
  possible: the fixed points are *exactly* the prime subfield `𝔽ₚ`.

      frobenius F p x = x   ⟺   x ∈ (⊥ : Subfield F)   ⟺   ∃ a : ZMod p, ↑a = x.

  Geometrically, `x ↦ x ^ p` fixes `x` iff `x` is a root of `Xᵖ - X`; this
  polynomial has degree `p` and the `p` elements of the prime subfield `𝔽ₚ` are
  `p` distinct roots (Fermat), so they exhaust the roots.  Mathlib packages this
  as `Subfield.mem_bot_iff_pow_eq_self`; here we recast it in terms of the
  Frobenius map itself, give the explicit `ZMod p` description of the fixed set,
  record that the fixed field has exactly `p` elements, and connect to perfect
  fields, where the Frobenius is bijective (an automorphism).

  In particular, on a *finite* field `𝔽_{pⁿ}` the Frobenius is an automorphism
  (perfect field) whose fixed field is the prime subfield `𝔽ₚ ⊊ 𝔽_{pⁿ}`
  whenever `n > 1` — the Frobenius is the identity iff the field *is* its prime
  subfield.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.  This is a synthesis
  of existing Mathlib results (`Subfield.mem_bot_iff_pow_eq_self`,
  `fieldRange_castHom_eq_bot`, `Subfield.card_bot`, `bijective_frobenius`)
  organised around the Frobenius fixed-field question.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ01OQ02

open Polynomial

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-! ### The fixed field is the prime subfield `⊥ = 𝔽ₚ` -/

/-- An element is fixed by the Frobenius iff it lies in the prime subfield
`⊥`.  This is the central characterization: the *fixed field* of the Frobenius
endomorphism of a field of characteristic `p` is the prime subfield. -/
theorem frobenius_fixed_iff_mem_bot {x : F} :
    frobenius F p x = x ↔ x ∈ (⊥ : Subfield F) := by
  rw [frobenius_def, Subfield.mem_bot_iff_pow_eq_self]

/-- The fixed point equation `xᵖ = x` (the defining equation of the fixed field)
holds iff `x` is in the prime subfield. -/
theorem pow_eq_self_iff_mem_bot {x : F} : x ^ p = x ↔ x ∈ (⊥ : Subfield F) :=
  (Subfield.mem_bot_iff_pow_eq_self F p).symm

/-- The fixed set of the Frobenius, as a `Set`, is exactly the prime subfield. -/
theorem fixedSet_frobenius_eq_bot :
    {x : F | frobenius F p x = x} = (⊥ : Subfield F) :=
  Set.ext fun _ => frobenius_fixed_iff_mem_bot p

/-! ### Explicit `ZMod p` description of the fixed field -/

/-- The fixed points of the Frobenius are exactly the image of the canonical
ring map `ZMod p → F`; i.e. they are the "integers mod `p`" sitting inside `F`.
This makes the prime subfield `𝔽ₚ` explicit. -/
theorem frobenius_fixed_iff_mem_primeField {x : F} :
    frobenius F p x = x ↔ ∃ a : ZMod p, ZMod.castHom (dvd_refl p) F a = x := by
  rw [frobenius_fixed_iff_mem_bot, ← ZMod.fieldRange_castHom_eq_bot p, RingHom.mem_fieldRange]

/-- The canonical map `ZMod p → F` (the prime subfield `𝔽ₚ`) is fixed pointwise
by the Frobenius: every element of `𝔽ₚ` satisfies `xᵖ = x` (Fermat). -/
theorem frobenius_fixes_primeField (a : ZMod p) :
    frobenius F p (ZMod.castHom (dvd_refl p) F a) = ZMod.castHom (dvd_refl p) F a :=
  (frobenius_fixed_iff_mem_primeField p).2 ⟨a, rfl⟩

/-! ### The fixed field has exactly `p` elements -/

/-- The fixed field of the Frobenius has exactly `p` elements — it is `𝔽ₚ`. -/
theorem card_fixedField_eq : Nat.card (⊥ : Subfield F) = p :=
  Subfield.card_bot F p

/-! ### Perfect fields: the Frobenius is an automorphism -/

/-- On a **perfect** field of characteristic `p`, the Frobenius is bijective —
an automorphism of `F`.  (Every finite field is perfect, so this applies to all
finite fields.) -/
theorem frobenius_bijective_of_perfectField [PerfectField F] :
    Function.Bijective (frobenius F p) :=
  bijective_frobenius F p

/-- The Frobenius is injective on any field of characteristic `p` (a field is a
domain, so `xᵖ = yᵖ → x = y`), and surjective exactly when the field is perfect.
Here we record surjectivity on a perfect field. -/
theorem frobenius_surjective_of_perfectField [PerfectField F] :
    Function.Surjective (frobenius F p) :=
  surjective_frobenius F p

/-! ### Synthesis on a finite field `𝔽_{pⁿ}` -/

variable (F) in
/-- On a finite field, the Frobenius is simultaneously an automorphism (perfect
field) and has fixed field equal to the prime subfield `𝔽ₚ`.  Thus the Frobenius
is the identity iff the field coincides with its prime subfield (`n = 1`). -/
theorem finiteField_frobenius_automorphism_with_primeField_fixed [Finite F] :
    Function.Bijective (frobenius F p) ∧
      ∀ x : F, frobenius F p x = x ↔ x ∈ (⊥ : Subfield F) :=
  ⟨bijective_frobenius F p, fun _ => frobenius_fixed_iff_mem_bot p⟩

/-! ### Concrete check -/

private instance fact_five_prime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- In `ZMod 5` (its own prime subfield) every element is fixed by the
Frobenius `x ↦ x⁵`: the fixed field is all of `ZMod 5`. -/
theorem frobenius_zmod_five_fixes_all : ∀ x : ZMod 5, frobenius (ZMod 5) 5 x = x := by
  decide

end FrobeniusEndomorphismOQ01OQ02
