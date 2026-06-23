/-
  Square of the quadratic Gauss sum.

  Target:  for an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum

      g = ∑ n, (quadraticChar (ZMod p) n) · ψ n

  satisfies  g² = (-1)^((p-1)/2) · p.

  The whole result reduces to Mathlib's generic `gaussSum_sq`, specialised to the
  ℂ-valued quadratic character of `ZMod p`, then evaluating the character at `-1`
  and the field cardinality.

  TYPING NOTE:
    `quadraticChar (ZMod p) : MulChar (ZMod p) ℤ`  is ℤ-VALUED.
    `gaussSum χ ψ` requires `χ : MulChar (ZMod p) F'` and `ψ : AddChar (ZMod p) F'`
    in the SAME codomain `F'`. With `ψ` valued in ℂ we transport the character
    along `ℤ → ℂ` via `MulChar.ringHomComp (Int.castRingHom ℂ)`.
-/
import Mathlib

open scoped BigOperators

namespace QuadraticGaussSumSquare

variable {p : ℕ} [Fact p.Prime]

/-- `ℂ`-valued quadratic character mod `p`, obtained from the integer-valued
`quadraticChar (ZMod p)` by composing with the ring hom `ℤ → ℂ`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- `chiC p` takes only the values `0, 1, -1` (it is a quadratic character). -/
theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- The quadratic character is nontrivial for an odd prime: `Int.castRingHom ℂ` is
injective (ℂ is `CharZero`), so `chiC p ≠ 1 ↔ quadraticChar (ZMod p) ≠ 1`, and the
latter holds whenever `ringChar (ZMod p) = p ≠ 2`. -/
theorem chiC_ne_one (hp : p ≠ 2) : chiC p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  exact (MulChar.ringHomComp_ne_one_iff
    ((Int.castRingHom ℂ).injective_int)).mpr (quadraticChar_ne_one hchar)

/-- Value of the character at `-1`: classical first supplement to quadratic
reciprocity, `quadraticChar (ZMod p) (-1) = (-1)^((p-1)/2)`, transported to ℂ. -/
theorem chiC_neg_one (hp : p ≠ 2) :
    chiC p (-1) = (-1 : ℂ) ^ ((p - 1) / 2) := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hq : quadraticChar (ZMod p) (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [quadraticChar_neg_one hchar, ZMod.card p]
    exact ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)
  have hpe : p / 2 = (p - 1) / 2 := by
    obtain ⟨k, rfl⟩ := hodd; omega
  simp only [chiC, MulChar.ringHomComp_apply, hq, map_pow, map_neg, map_one]
  rw [hpe]

/-- **Square of the quadratic Gauss sum.** For an odd prime `p` and a primitive
additive character `ψ : ZMod p → ℂ`,
`gaussSum (chiC p) ψ ^ 2 = (-1)^((p-1)/2) · p`.

The whole result is `gaussSum_sq` specialised to the (transported) quadratic
character, followed by evaluating the character at `-1` and the field cardinality. -/
theorem gaussSum_quadratic_sq (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ^ 2 = (-1 : ℂ) ^ ((p - 1) / 2) * p := by
  have h := gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
  calc gaussSum (chiC p) ψ ^ 2
      = chiC p (-1) * (Fintype.card (ZMod p) : ℂ) := h
    _ = (-1 : ℂ) ^ ((p - 1) / 2) * p := by rw [chiC_neg_one hp, ZMod.card p]

end QuadraticGaussSumSquare
