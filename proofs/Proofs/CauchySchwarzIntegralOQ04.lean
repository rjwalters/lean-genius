/-
  Cauchy–Schwarz Integral — OQ-04: the Cauchy–Schwarz core of the uncertainty principle

  The gallery entry `CauchySchwarzIntegral` proves the L²/inner-product Cauchy–Schwarz
  inequality `|⟪f,g⟫| ≤ ‖f‖·‖g‖`.  Its OQ-04 asks for the **Heisenberg uncertainty
  principle**.  The full operator-theoretic statement
  `Var_ψ(A)·Var_ψ(B) ≥ ¼|⟪ψ,[A,B]ψ⟫|²` needs self-adjoint operators and the
  commutator, beyond a single file; but the *single inequality that drives it* is a
  clean Cauchy–Schwarz corollary, and that is what we formalize.

  Writing `u = (A−⟨A⟩)ψ`, `v = (B−⟨B⟩)ψ`, the uncertainty product is
  `Var(A)·Var(B) = ‖u‖²·‖v‖²`, and the commutator term is `Im⟪u,v⟫`.  The
  inequality `Var(A)·Var(B) ≥ |Im⟪u,v⟫|²` is therefore *exactly*

      `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`     and its square     `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`,

  the Cauchy–Schwarz step of Heisenberg's proof, valid in any inner product space
  over `ℝ` or `ℂ` (for `ℝ` the imaginary part is `0` and the bound is trivial; the
  content is the `ℂ` case).

  * `abs_im_inner_le_norm_mul_norm` — `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`.
  * `im_inner_sq_le` — `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²`.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Heisenberg (1927); Robertson (1929); the abstract uncertainty
  inequality, e.g. Reed–Simon, *Functional Analysis*, §VIII.
-/

import Mathlib

namespace CauchySchwarzIntegralOQ04

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Uncertainty-principle Cauchy–Schwarz core.**  The imaginary part of the inner
    product is bounded by the product of the norms: `|Im⟪u,v⟫| ≤ ‖u‖·‖v‖`.  With
    `u = (A−⟨A⟩)ψ` and `v = (B−⟨B⟩)ψ`, this is the inequality
    `√(Var A · Var B) ≥ |Im⟪u,v⟫|` underlying Heisenberg's bound. -/
theorem abs_im_inner_le_norm_mul_norm (u v : E) :
    |RCLike.im (inner 𝕜 u v)| ≤ ‖u‖ * ‖v‖ := by
  have h1 : |RCLike.im (inner 𝕜 u v)| ≤ ‖inner 𝕜 u v‖ := RCLike.abs_im_le_norm _
  have h2 : ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  exact h1.trans h2

/-- **Squared uncertainty inequality.**  `(Im⟪u,v⟫)² ≤ ‖u‖²·‖v‖²` — the product of
    the "variances" `‖u‖²`, `‖v‖²` dominates the squared commutator term. -/
theorem im_inner_sq_le (u v : E) :
    (RCLike.im (inner 𝕜 u v)) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := abs_im_inner_le_norm_mul_norm (𝕜 := 𝕜) u v
  nlinarith [h, abs_nonneg (RCLike.im (inner 𝕜 u v)),
    sq_abs (RCLike.im (inner 𝕜 u v)), norm_nonneg u, norm_nonneg v]

end CauchySchwarzIntegralOQ04
