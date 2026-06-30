/-
  Additive-character dependence of the quadratic Gauss sum.

  Setup (matching the parent entry `QuadraticGaussSumSquare`):
  for an odd prime `p`, let `χ = chiC p : MulChar (ZMod p) ℂ` be the ℂ-valued
  quadratic (Legendre) character, and let `ψ : AddChar (ZMod p) ℂ` be a primitive
  additive character.  The quadratic Gauss sum is `g = gaussSum χ ψ`, and the parent
  proves `g² = (-1)^((p-1)/2) · p = p*`.

  The Gauss sum `g` visibly *depends* on the additive character `ψ`.  This entry
  pins down that dependence completely.  Every other primitive additive character of
  `ZMod p` has the form `mulShift ψ a` for a unit `a`, and Mathlib's twisting law
  `gaussSum_mulShift` says `χ a · gaussSum χ (mulShift ψ a) = gaussSum χ ψ`.  Because
  `χ` is a *quadratic* character its values on units are `±1`, so this rearranges to

      gaussSum χ (mulShift ψ a) = χ(a) · gaussSum χ ψ.                       (TWIST)

  Consequences proved below:

  * `gaussSum_chiC_mulShift`        : the twisting law (TWIST) above.
  * `gaussSum_chiC_mulShift_sq_eq`  : the SQUARE is twist-independent — every primitive
                                       additive character yields the same `g² = p*`.
                                       So the parent's value `p*` is intrinsic to `p`,
                                       not an artefact of the chosen character.
  * `gaussSum_chiC_ne_zero`         : `g ≠ 0` for every primitive `ψ` (nonvanishing).
  * `gaussSum_mulShift_eq_self_iff` : twisting by `a` *fixes* `g`  ⟺  `a` is a square.
  * `gaussSum_mulShift_eq_neg_iff`  : twisting by `a` *negates* `g` ⟺  `a` is a
                                       quadratic NON-residue.

  In words: replacing the additive character `ψ` by `mulShift ψ a` flips the sign of
  the quadratic Gauss sum precisely when `a` is a quadratic non-residue mod `p`, and
  leaves the square `g² = p*` untouched.

  Self-contained: the square identity is re-derived in-file from Mathlib's generic
  `gaussSum_sq`, so this file imports only `Mathlib`.
-/
import Mathlib

open scoped BigOperators
open AddChar

namespace QuadraticGaussSumTwist

variable {p : ℕ} [Fact p.Prime]

/-- `ℂ`-valued quadratic character mod `p`, obtained from the integer-valued
`quadraticChar (ZMod p)` by composing with the ring hom `ℤ → ℂ`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- `chiC p` takes only the values `0, 1, -1`. -/
theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- The quadratic character is nontrivial for an odd prime. -/
theorem chiC_ne_one (hp : p ≠ 2) : chiC p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  exact (MulChar.ringHomComp_ne_one_iff
    ((Int.castRingHom ℂ).injective_int)).mpr (quadraticChar_ne_one hchar)

/-- On a unit `a`, the character value is nonzero (`χ a · χ a⁻¹ = χ 1 = 1`). -/
theorem chiC_unit_ne_zero (a : (ZMod p)ˣ) : chiC p (a : ZMod p) ≠ 0 := by
  have h : chiC p (a : ZMod p) * chiC p ((a⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel a, Units.val_one, map_one]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- On a unit, the quadratic character takes the value `1` or `-1`. -/
theorem chiC_unit_cases (a : (ZMod p)ˣ) :
    chiC p (a : ZMod p) = 1 ∨ chiC p (a : ZMod p) = -1 := by
  rcases chiC_isQuadratic (a : ZMod p) with h | h | h
  · exact absurd h (chiC_unit_ne_zero a)
  · exact Or.inl h
  · exact Or.inr h

/-- The character value on a unit squares to `1`. -/
theorem chiC_unit_sq (a : (ZMod p)ˣ) : chiC p (a : ZMod p) ^ 2 = 1 := by
  rcases chiC_unit_cases a with h | h <;> rw [h] <;> ring

/-- **Twisting law for the quadratic Gauss sum.** Replacing the additive character
`ψ` by `mulShift ψ a` multiplies the Gauss sum by `χ(a)`:
`gaussSum χ (mulShift ψ a) = χ(a) · gaussSum χ ψ`.

Derived from Mathlib's `gaussSum_mulShift` (`χ a · gaussSum χ (mulShift ψ a) =
gaussSum χ ψ`) by multiplying through by the involution `χ(a)` (`χ(a)² = 1`). -/
theorem gaussSum_chiC_mulShift {ψ : AddChar (ZMod p) ℂ} (a : (ZMod p)ˣ) :
    gaussSum (chiC p) (mulShift ψ (a : ZMod p))
      = chiC p (a : ZMod p) * gaussSum (chiC p) ψ := by
  have hmul := gaussSum_mulShift (chiC p) ψ a
  have hsq := chiC_unit_sq a
  calc gaussSum (chiC p) (mulShift ψ (a : ZMod p))
      = chiC p (a : ZMod p) ^ 2 * gaussSum (chiC p) (mulShift ψ (a : ZMod p)) := by
        rw [hsq, one_mul]
    _ = chiC p (a : ZMod p) *
          (chiC p (a : ZMod p) * gaussSum (chiC p) (mulShift ψ (a : ZMod p))) := by ring
    _ = chiC p (a : ZMod p) * gaussSum (chiC p) ψ := by rw [hmul]

/-- Value of the character at `-1`: `quadraticChar (ZMod p) (-1) = (-1)^((p-1)/2)`,
transported to ℂ. -/
theorem chiC_neg_one (hp : p ≠ 2) :
    chiC p (-1) = (-1 : ℂ) ^ ((p - 1) / 2) := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hq : quadraticChar (ZMod p) (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [quadraticChar_neg_one hchar, ZMod.card p]
    exact ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)
  have hpe : p / 2 = (p - 1) / 2 := by obtain ⟨k, rfl⟩ := hodd; omega
  simp only [chiC, MulChar.ringHomComp_apply, hq, map_pow, map_neg, map_one]
  rw [hpe]

/-- **Square of the quadratic Gauss sum** (re-derived in-file from `gaussSum_sq`).
`gaussSum (chiC p) ψ ^ 2 = (-1)^((p-1)/2) · p`. -/
theorem gaussSum_chiC_sq (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ^ 2 = (-1 : ℂ) ^ ((p - 1) / 2) * p := by
  have h := gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
  calc gaussSum (chiC p) ψ ^ 2
      = chiC p (-1) * (Fintype.card (ZMod p) : ℂ) := h
    _ = (-1 : ℂ) ^ ((p - 1) / 2) * p := by rw [chiC_neg_one hp, ZMod.card p]

/-- **The square is twist-independent.** Every twist `mulShift ψ a` of a primitive
character produces a Gauss sum with the *same* square `g² = p*`.  Hence the parent's
value `p* = (-1)^((p-1)/2)·p` is intrinsic to `p` and independent of the chosen
additive character. -/
theorem gaussSum_chiC_mulShift_sq_eq (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (a : (ZMod p)ˣ) :
    gaussSum (chiC p) (mulShift ψ (a : ZMod p)) ^ 2
      = (-1 : ℂ) ^ ((p - 1) / 2) * p := by
  rw [gaussSum_chiC_mulShift a, mul_pow, chiC_unit_sq a, one_mul, gaussSum_chiC_sq hp hψ]

/-- **Nonvanishing.** For a primitive additive character, the quadratic Gauss sum is
nonzero. -/
theorem gaussSum_chiC_ne_zero (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ≠ 0 := by
  refine gaussSum_ne_zero_of_nontrivial ?_ (chiC_ne_one hp) hψ
  rw [ZMod.card]
  exact_mod_cast (Fact.out : p.Prime).pos.ne'

/-- Pointwise bridge: `chiC p a = -1 ⟺ quadraticChar (ZMod p) a = -1`. -/
theorem chiC_eq_neg_one_iff (a : ZMod p) :
    chiC p a = -1 ↔ quadraticChar (ZMod p) a = -1 := by
  rw [chiC, MulChar.ringHomComp_apply, eq_intCast,
    show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num, Int.cast_inj]

/-- Pointwise bridge: `chiC p a = 1 ⟺ quadraticChar (ZMod p) a = 1`. -/
theorem chiC_eq_one_iff (a : ZMod p) :
    chiC p a = 1 ↔ quadraticChar (ZMod p) a = 1 := by
  rw [chiC, MulChar.ringHomComp_apply, eq_intCast,
    show (1 : ℂ) = ((1 : ℤ) : ℂ) by norm_num, Int.cast_inj]

/-- **Twisting fixes the Gauss sum iff the twist is a square.**
`gaussSum χ (mulShift ψ a) = gaussSum χ ψ ⟺ a is a quadratic residue (χ(a) = 1).** -/
theorem gaussSum_mulShift_eq_self_iff (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (a : (ZMod p)ˣ) :
    gaussSum (chiC p) (mulShift ψ (a : ZMod p)) = gaussSum (chiC p) ψ
      ↔ IsSquare (a : ZMod p) := by
  rw [gaussSum_chiC_mulShift a]
  constructor
  · intro h
    have hG := gaussSum_chiC_ne_zero hp hψ
    have hone : chiC p (a : ZMod p) = 1 :=
      mul_right_cancel₀ hG (by rw [one_mul]; exact h)
    have := (chiC_eq_one_iff (a : ZMod p)).mp hone
    exact (quadraticChar_one_iff_isSquare (Units.ne_zero a)).mp this
  · intro h
    have : quadraticChar (ZMod p) (a : ZMod p) = 1 :=
      (quadraticChar_one_iff_isSquare (Units.ne_zero a)).mpr h
    rw [(chiC_eq_one_iff (a : ZMod p)).mpr this, one_mul]

/-- **Twisting negates the Gauss sum iff the twist is a non-residue.**
`gaussSum χ (mulShift ψ a) = -gaussSum χ ψ ⟺ a is a quadratic NON-residue
(`χ(a) = -1`, i.e. `¬ IsSquare a`).** -/
theorem gaussSum_mulShift_eq_neg_iff (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (a : (ZMod p)ˣ) :
    gaussSum (chiC p) (mulShift ψ (a : ZMod p)) = - gaussSum (chiC p) ψ
      ↔ ¬ IsSquare (a : ZMod p) := by
  rw [gaussSum_chiC_mulShift a]
  constructor
  · intro h
    have hG := gaussSum_chiC_ne_zero hp hψ
    have hneg : chiC p (a : ZMod p) = -1 :=
      mul_right_cancel₀ hG (by rw [neg_one_mul]; exact h)
    have := (chiC_eq_neg_one_iff (a : ZMod p)).mp hneg
    exact (quadraticChar_neg_one_iff_not_isSquare).mp this
  · intro h
    have : quadraticChar (ZMod p) (a : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr h
    rw [(chiC_eq_neg_one_iff (a : ZMod p)).mpr this, neg_one_mul]

end QuadraticGaussSumTwist
