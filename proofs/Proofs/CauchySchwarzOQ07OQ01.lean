/-
  The Jordan–von Neumann converse (cauchy-schwarz-oq-07-oq-01).

  Open question (the converse direction of the parent cauchy-schwarz-oq-07): if a norm
  `‖·‖` on a real or complex normed space satisfies the parallelogram law
      ‖x + y‖² + ‖x − y‖² = 2‖x‖² + 2‖y‖²,
  then it is induced by an inner product, recovered from the norm via the polarization
  identity.

  The parent proved the FORWARD direction — every inner-product norm satisfies the
  parallelogram law.  This file packages the full **Jordan–von Neumann (1935)
  characterization** as a biconditional:

      a compatible inner product exists  ⇔  the parallelogram law holds.

  The hard converse (⇐) is Mathlib's `InnerProductSpace.ofNorm` (the
  Fréchet–von Neumann–Jordan theorem): it constructs the inner product by polarization and
  verifies bilinearity and norm-compatibility.  We expose it in both the `*self` form Mathlib
  uses and the squared `^2` form of the parent, and add a `recovers the norm` corollary
  making `‖x‖² = re⟪x,x⟫` explicit for the recovered inner product.

  To show the criterion is SHARP (not vacuously always satisfiable), we exhibit a concrete
  counterexample: the supremum norm on `ℝ × ℝ` violates the parallelogram law at
  `x = (1,0), y = (0,1)` (the diagonals (1,1) and (1,-1) both have sup-norm 1, giving
  LHS = 2 ≠ 4 = RHS), and therefore — by the characterization — admits NO compatible inner
  product.  So the sup-normed plane is a genuine non-Hilbert Banach space.

  Sorry-free and axiom-free.
-/
import Mathlib

open RCLike
open scoped InnerProductSpace

namespace CauchySchwarzOQ07OQ01

section Characterization

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Jordan–von Neumann characterization (`*self` form).**  A real-or-complex normed space
`E` carries a compatible inner product if and only if its norm satisfies the parallelogram
identity `‖x+y‖·‖x+y‖ + ‖x−y‖·‖x−y‖ = 2(‖x‖·‖x‖ + ‖y‖·‖y‖)`.

The forward direction is Mathlib's `parallelogram_law_with_norm`; the converse is the
Fréchet–von Neumann–Jordan construction `InnerProductSpace.ofNorm`, which builds the inner
product by polarization.  `Nonempty (InnerProductSpace 𝕜 E)` is the precise statement that
*some* inner product compatible with the existing norm exists. -/
theorem nonempty_innerProductSpace_iff_parallelogram :
    Nonempty (InnerProductSpace 𝕜 E) ↔
      ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  constructor
  · rintro ⟨i⟩ x y
    letI := i
    exact parallelogram_law_with_norm 𝕜 x y
  · intro h
    exact ⟨InnerProductSpace.ofNorm 𝕜 h⟩

/-- **Jordan–von Neumann characterization (squared `^2` form).**  The same biconditional in
the squared form used by the parent entry: a compatible inner product exists iff
`‖x+y‖² + ‖x−y‖² = 2‖x‖² + 2‖y‖²`. -/
theorem nonempty_innerProductSpace_iff_parallelogram_sq :
    Nonempty (InnerProductSpace 𝕜 E) ↔
      ∀ x y : E, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  rw [nonempty_innerProductSpace_iff_parallelogram (𝕜 := 𝕜)]
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩ <;>
    · have := h x y; simp only [pow_two] at *; linarith

/-- **The recovered inner product reproduces the norm.**  Given the parallelogram law, the
inner product produced by `InnerProductSpace.ofNorm` satisfies `‖x‖² = re⟪x,x⟫`, i.e. the
polarization-defined inner product is genuinely compatible with the original norm. -/
theorem ofNorm_norm_sq_eq_re_inner
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))
    (x : E) :
    letI := InnerProductSpace.ofNorm 𝕜 h
    ‖x‖ ^ 2 = RCLike.re (inner 𝕜 x x) := by
  letI := InnerProductSpace.ofNorm 𝕜 h
  exact norm_sq_eq_re_inner (𝕜 := 𝕜) x

end Characterization

section Counterexample

/-- **Sharpness: the supremum norm on `ℝ × ℝ` violates the parallelogram law.**  Tested at
`x = (1,0)`, `y = (0,1)`: both diagonals `x+y = (1,1)` and `x−y = (1,−1)` have sup-norm `1`,
so the left-hand side is `1 + 1 = 2`, while the right-hand side is `2(1 + 1) = 4`.  Hence the
parallelogram law fails for the `ℓ^∞` norm. -/
theorem supNorm_not_parallelogram :
    ¬ ∀ x y : ℝ × ℝ,
      ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  intro h
  have key := h (1, 0) (0, 1)
  norm_num [Prod.norm_def, Real.norm_eq_abs, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub] at key

/-- **The sup-normed plane is not an inner-product space.**  Combining the characterization
with the counterexample: since the `ℓ^∞` norm on `ℝ × ℝ` fails the parallelogram law, no
inner product is compatible with it.  This exhibits a concrete finite-dimensional Banach
space that is not a Hilbert space. -/
theorem no_innerProductSpace_sup_norm :
    ¬ Nonempty (InnerProductSpace ℝ (ℝ × ℝ)) := by
  rw [nonempty_innerProductSpace_iff_parallelogram (𝕜 := ℝ)]
  exact supNorm_not_parallelogram

end Counterexample

end CauchySchwarzOQ07OQ01
