/-
  The magnitude `‖g‖² = p` of the quadratic Gauss sum, derived from character
  orthogonality (Parseval) — independently of the square identity.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, write `g = gaussSum (chiC p) ψ` for the quadratic Gauss sum.
  The entry `QuadraticGaussSumSquareOQ01` proves the magnitude `‖g‖² = p` as a
  COROLLARY of the parent's square identity `g² = (-1)^((p-1)/2)·p`: applying the
  multiplicative `Complex.normSq` to that identity gives `normSq(g)² = p²`, whence
  `normSq g = p` by nonnegativity.  Its open question #3 asks whether the magnitude
  can instead be obtained DIRECTLY from character orthogonality (Parseval), as an
  independent cross-check that does not pass through the square identity.

  This file answers that question affirmatively.  Mathlib's
  `gaussSum_mul_gaussSum_eq_card` is exactly the Parseval/orthogonality statement
      gaussSum χ ψ · gaussSum χ⁻¹ ψ⁻¹ = #(ZMod p)
  for any nontrivial `χ` and primitive `ψ`.  Two elementary facts turn the left side
  into `‖g‖²`:

    * `gaussSum_conj`: complex-conjugating `g` replaces `ψ` by its inverse character
      `ψ⁻¹` and fixes the real-valued quadratic character `chiC p`, i.e.
      `conj (gaussSum (chiC p) ψ) = gaussSum (chiC p) ψ⁻¹`.  (Conjugation sends each
      additive-character value, a root of unity, to its inverse — `AddChar.starComp` —
      and fixes the integer values `0, ±1` of the quadratic character.)

    * `(chiC p)⁻¹ = chiC p` because `chiC p` is a quadratic character
      (`MulChar.IsQuadratic.inv`).

  Hence `gaussSum χ⁻¹ ψ⁻¹ = gaussSum χ ψ⁻¹ = conj g`, and the orthogonality identity
  reads `g · conj g = p`, i.e. `normSq g = p` by `Complex.mul_conj`.  No use is made
  of the square identity `g² = ±p`, so this is a logically independent derivation of
  the magnitude.

  Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare

open scoped BigOperators
open Complex QuadraticGaussSumSquare

namespace QuadraticGaussSumNormParseval

variable {p : ℕ} [Fact p.Prime]

/-- Complex conjugation of the quadratic Gauss sum replaces the additive character by
its inverse and fixes the (real, `±1`-valued) quadratic character:
`conj (gaussSum (chiC p) ψ) = gaussSum (chiC p) ψ⁻¹`. -/
theorem gaussSum_conj (ψ : AddChar (ZMod p) ℂ) :
    (starRingEnd ℂ) (gaussSum (chiC p) ψ) = gaussSum (chiC p) ψ⁻¹ := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_mul]
  have hχ : (starRingEnd ℂ) (chiC p x) = chiC p x := by
    simp only [chiC, MulChar.ringHomComp_apply, eq_intCast, map_intCast]
  have hψc : (starRingEnd ℂ) (ψ x) = ψ⁻¹ x :=
    AddChar.starComp_apply
      (by rw [ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).pos) x
  rw [hχ, hψc]

/-- **Magnitude of the quadratic Gauss sum via Parseval.** For an odd prime `p` and a
primitive additive character `ψ`, `‖gaussSum (chiC p) ψ‖² = p`, derived directly from
character orthogonality (`gaussSum_mul_gaussSum_eq_card`) without the square identity. -/
theorem gaussSum_normSq_eq_card (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum (chiC p) ψ) = p := by
  have key : gaussSum (chiC p) ψ * gaussSum (chiC p)⁻¹ ψ⁻¹
      = (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_mul_gaussSum_eq_card (chiC_ne_one hp) hψ
  rw [chiC_isQuadratic.inv, ← gaussSum_conj, Complex.mul_conj, ZMod.card] at key
  exact_mod_cast key

/-- Restated as `‖g‖ = √p` (the Euclidean magnitude). -/
theorem gaussSum_norm_eq_sqrt (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum (chiC p) ψ‖ = Real.sqrt p := by
  rw [Complex.norm_def, gaussSum_normSq_eq_card hp hψ]

end QuadraticGaussSumNormParseval
