/-
  The parallelogram law in an inner-product space (cauchy-schwarz-oq-07).

  Open question.  Formalize
      ‖x + y‖² + ‖x − y‖² = 2‖x‖² + 2‖y‖²
  in a real or complex inner-product space, by expanding both squares via the
  inner-product self-identity and cancelling the cross terms.

  This is the parallelogram law: the sum of the squares of the two diagonals of a
  parallelogram equals the sum of the squares of its four sides.  It is the precise
  algebraic identity that distinguishes inner-product norms from general normed-space
  norms (Jordan–von Neumann), and the polarization identity below shows how it lets the
  inner product be recovered from the norm alone.

  Mathlib already provides the `*self` form `parallelogram_law_with_norm`
  (`‖x+y‖*‖x+y‖ + ‖x-y‖*‖x-y‖ = 2*(‖x‖*‖x‖ + ‖y‖*‖y‖)`); this file packages the
  squared (`^2`) form requested by the open question — both in the general `RCLike`
  setting and, by the elementary cross-term cancellation the question describes, over a
  real inner-product space — and derives the polarization identity in the same squared
  form as an immediate corollary.

  Sorry-free and axiom-free.
-/
import Mathlib

open RCLike
open scoped InnerProductSpace

namespace CauchySchwarzOQ07

section RCLikeField

/-- **The parallelogram law** (squared form), over a real or complex inner-product space.
`‖x + y‖² + ‖x − y‖² = 2‖x‖² + 2‖y‖²`.  This is the `^2` packaging of Mathlib's
`parallelogram_law_with_norm`.  The scalar field `𝕜` is an explicit argument so the
identity can be specialized to `ℝ` or `ℂ`. -/
theorem parallelogram_norm_sq (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := parallelogram_law_with_norm 𝕜 x y
  simp only [pow_two]
  linarith [h]

end RCLikeField

section RealSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The parallelogram law over a real inner-product space**, proved directly by the
method the open question describes: expand `‖x ± y‖²` via `inner_self`, whereupon the two
cross terms `±2⟪x, y⟫` cancel. -/
theorem parallelogram_norm_sq_real (x y : F) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- **Polarization identity** (squared form): in a real inner-product space the inner
product is recovered from the norm via the diagonals of the parallelogram,
`⟪x, y⟫ = (‖x + y‖² − ‖x − y‖²) / 4`.  An immediate corollary of the cross-term
expansion, dual to the parallelogram law (sum of diagonals vs. difference of diagonals). -/
theorem real_inner_eq_norm_sq_diff_div_four (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- Rearranged parallelogram law: a diagonal is determined by the sides and the other
diagonal, `‖x + y‖² = 2‖x‖² + 2‖y‖² − ‖x − y‖²`. -/
theorem norm_add_sq_eq_real (x y : F) :
    ‖x + y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - ‖x - y‖ ^ 2 := by
  have := parallelogram_norm_sq_real x y; linarith

end RealSpace

section ComplexSpace

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- **The parallelogram law over a complex inner-product space**, the `ℂ`
specialization of `parallelogram_norm_sq`. -/
theorem parallelogram_norm_sq_complex (x y : G) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 :=
  parallelogram_norm_sq ℂ x y

end ComplexSpace

end CauchySchwarzOQ07
