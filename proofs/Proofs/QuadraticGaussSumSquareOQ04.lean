/-
  The quadratic Gauss sum generates a quadratic field.

  Setup (parent entry `QuadraticGaussSumSquare`): for an odd prime `p` and a
  primitive additive character `ψ : ZMod p → ℂ`, the quadratic Gauss sum

      g = gaussSum (chiC p) ψ = ∑ₙ χ(n) · ψ(n)         (χ = quadratic character mod p)

  satisfies the classical square formula

      g² = p* := (-1)^((p-1)/2) · p.

  This entry pushes that one structural step further into field theory.  Because
  `|p*| = p` is prime, `p*` is **not** the square of any rational, so `g` is a
  *quadratic irrational*:

    • `minpoly ℚ g = X² − p*`              (its minimal polynomial over ℚ),
    • `[ℚ(g) : ℚ] = 2`                      (it generates a quadratic extension),
    • `g ∉ ℚ`                              (it is genuinely irrational).

  Equivalently, the quadratic Gauss sum generates the unique quadratic subfield
  `ℚ(√p*)` of the `p`-th cyclotomic field `ℚ(ζ_p)`.

  The square formula `gaussSum_sq_eq` is the parent result, re-derived here from
  Mathlib's generic `gaussSum_sq` so the file is self-contained.  Everything past
  it (`pstar_not_sq`, `minpoly_gaussSum`, `finrank_adjoin_gaussSum`,
  `gaussSum_not_rational`) is the new content.
-/
import Mathlib

open scoped BigOperators
open Polynomial IntermediateField

namespace QuadraticGaussSumSquareOQ04

variable {p : ℕ} [Fact p.Prime]

/-! ## The character and the square formula (parent entry, re-derived) -/

/-- `ℂ`-valued quadratic character mod `p`, from the integer-valued
`quadraticChar (ZMod p)` composed with `ℤ → ℂ`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem chiC_ne_one (hp : p ≠ 2) : chiC p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  exact (MulChar.ringHomComp_ne_one_iff ((Int.castRingHom ℂ).injective_int)).mpr
    (quadraticChar_ne_one hchar)

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

/-- The integer `p* = (-1)^((p-1)/2) · p`. -/
def pstar (p : ℕ) : ℤ := (-1) ^ ((p - 1) / 2) * (p : ℤ)

/-- **Square of the quadratic Gauss sum** (the parent result, restated with the
right-hand side packaged as `p*`). -/
theorem gaussSum_sq_eq (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ^ 2 = (pstar p : ℂ) := by
  calc gaussSum (chiC p) ψ ^ 2
      = chiC p (-1) * (Fintype.card (ZMod p) : ℂ) :=
        gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
    _ = (-1 : ℂ) ^ ((p - 1) / 2) * p := by rw [chiC_neg_one hp, ZMod.card p]
    _ = (pstar p : ℂ) := by simp only [pstar]; push_cast; ring

/-! ## `p*` is not a rational square -/

/-- `|p*| = p` is prime, so `p*` is not the square of any rational number. -/
theorem pstar_not_sq : ∀ b : ℚ, b ^ 2 ≠ (pstar p : ℚ) := by
  intro b hb
  have hpp : p.Prime := Fact.out
  -- `p* = p` (when `p ≡ 1 mod 4`) or `p* = -p` (when `p ≡ 3 mod 4`).
  have hcases : pstar p = (p : ℤ) ∨ pstar p = -(p : ℤ) := by
    rcases Nat.even_or_odd ((p - 1) / 2) with he | ho
    · left; simp [pstar, he.neg_one_pow]
    · right; simp [pstar, ho.neg_one_pow]
  rcases hcases with hpos | hneg
  · -- `b² = p` with `p` prime contradicts irrationality of `√p`.
    rw [hpos] at hb
    have hbR : ((b : ℝ)) ^ 2 = (p : ℝ) := by exact_mod_cast hb
    have hsqrt : Real.sqrt p = |(b : ℝ)| := by rw [← hbR, Real.sqrt_sq_eq_abs]
    have hirr : Irrational (Real.sqrt p) := hpp.irrational_sqrt
    refine hirr ⟨|b|, ?_⟩
    rw [hsqrt]; push_cast; ring
  · -- `b² = -p < 0` is impossible.
    rw [hneg] at hb
    have hnn : (0 : ℚ) ≤ b ^ 2 := sq_nonneg b
    rw [hb] at hnn
    have hppos : (0 : ℚ) < p := by exact_mod_cast hpp.pos
    push_cast at hnn
    linarith

/-! ## The minimal polynomial and the degree -/

/-- `g` is integral over `ℚ`: it is a root of the monic `X² − p*`. -/
theorem isIntegral_gaussSum (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    IsIntegral ℚ (gaussSum (chiC p) ψ) :=
  ⟨X ^ 2 - C (pstar p : ℚ), monic_X_pow_sub_C _ (by norm_num), by
    show (Polynomial.aeval (gaussSum (chiC p) ψ)) (X ^ 2 - C (pstar p : ℚ)) = 0
    have hsq := gaussSum_sq_eq (p := p) hp hψ
    simp only [map_sub, map_pow, aeval_X, map_intCast, hsq, sub_self]⟩

/-- **Minimal polynomial of the quadratic Gauss sum.** Over `ℚ` it is `X² − p*`. -/
theorem minpoly_gaussSum (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    minpoly ℚ (gaussSum (chiC p) ψ) = X ^ 2 - C (pstar p : ℚ) := by
  have haeval : (Polynomial.aeval (gaussSum (chiC p) ψ)) (X ^ 2 - C (pstar p : ℚ)) = 0 := by
    have hsq := gaussSum_sq_eq (p := p) hp hψ
    simp only [map_sub, map_pow, aeval_X, map_intCast, hsq, sub_self]
  have hmonic : (X ^ 2 - C (pstar p : ℚ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hirr : Irreducible (X ^ 2 - C (pstar p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (pstar_not_sq)
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm

/-- **`[ℚ(g) : ℚ] = 2`.** The quadratic Gauss sum generates a quadratic extension
of `ℚ` — the unique quadratic subfield `ℚ(√p*)` of `ℚ(ζ_p)`. -/
theorem finrank_adjoin_gaussSum (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    Module.finrank ℚ ℚ⟮gaussSum (chiC p) ψ⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_gaussSum hp hψ), minpoly_gaussSum hp hψ,
    natDegree_X_pow_sub_C]

/-- **The quadratic Gauss sum is irrational**: it is not the image of any rational. -/
theorem gaussSum_not_rational (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ∉ Set.range ((algebraMap ℚ ℂ)) := by
  rintro ⟨q, hq⟩
  -- If `g = q` then `q² = p*`, contradicting `pstar_not_sq`.
  have hsq := gaussSum_sq_eq (p := p) hp hψ
  rw [← hq, eq_ratCast (algebraMap ℚ ℂ) q] at hsq
  -- `hsq : (↑q)² = ↑(pstar p)` in `ℂ`
  have hq2 : q ^ 2 = (pstar p : ℚ) := by exact_mod_cast hsq
  exact pstar_not_sq q hq2

end QuadraticGaussSumSquareOQ04
