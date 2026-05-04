/-
Heisenberg Uncertainty Principle via Cauchy-Schwarz

Open Question (cauchy-schwarz-oq-01-oq-01-oq-02):
Can the Robertson-Schrödinger uncertainty inequality
  ‖Au‖ · ‖Bu‖ ≥ ½ ‖⟪(AB-BA)u, u⟫‖
be derived formally from the Cauchy-Schwarz inequality for complex Hilbert spaces?

Answer: YES. The proof uses two ingredients:
1. Self-adjoint algebra: ⟪(AB-BA)u, u⟫ = conj(⟪Au, Bu⟫) - ⟪Au, Bu⟫
2. Triangle + Cauchy-Schwarz: ‖conj(z) - z‖ ≤ 2‖z‖ ≤ 2‖Au‖·‖Bu‖

Robertson (1929) proved this for general pairs of self-adjoint observables,
generalizing Heisenberg's uncertainty principle for position and momentum.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

open scoped InnerProductSpace

namespace CauchySchwarzOQ01OQ01OQ02

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Self-adjoint operators satisfy the symmetry ⟪Ax, y⟫ = ⟪x, Ay⟫. -/
private lemma selfadj_inner (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (x y : E) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  have hadj : A.adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA
  rw [← ContinuousLinearMap.adjoint_inner_right, hadj]

/-- For self-adjoint A, B: ⟪(AB-BA)u, u⟫ = conj(⟪Au, Bu⟫) - ⟪Au, Bu⟫. -/
private lemma inner_commutator (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E) :
    ⟪(A * B - B * A) u, u⟫_ℂ =
    starRingEnd ℂ ⟪A u, B u⟫_ℂ - ⟪A u, B u⟫_ℂ := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, inner_sub_left]
  rw [selfadj_inner A hA (B u) u, inner_conj_symm (B u) (A u), selfadj_inner B hB (A u) u]

/-- ‖conj(z) - z‖ ≤ 2‖z‖ for any complex number z. -/
private lemma norm_conj_sub_self_le (z : ℂ) :
    ‖starRingEnd ℂ z - z‖ ≤ 2 * ‖z‖ := by
  have h_conj_norm : ‖starRingEnd ℂ z‖ = ‖z‖ := by
    show ‖star z‖ = ‖z‖; exact norm_star z
  linarith [norm_sub_le (starRingEnd ℂ z) z]

/-- The commutator norm bound: ‖⟪(AB-BA)u, u⟫‖ ≤ 2 ‖Au‖ · ‖Bu‖. -/
theorem heisenberg_norm_bound (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E) :
    ‖⟪(A * B - B * A) u, u⟫_ℂ‖ ≤ 2 * ‖A u‖ * ‖B u‖ := by
  calc ‖⟪(A * B - B * A) u, u⟫_ℂ‖
      = ‖starRingEnd ℂ ⟪A u, B u⟫_ℂ - ⟪A u, B u⟫_ℂ‖ := by
          rw [inner_commutator A B hA hB]
    _ ≤ 2 * ‖⟪A u, B u⟫_ℂ‖ := norm_conj_sub_self_le _
    _ ≤ 2 * (‖A u‖ * ‖B u‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)

/-- **Robertson-Schrödinger Uncertainty Principle**: For self-adjoint operators A, B
on a complex Hilbert space and any vector u,
  ‖Au‖ · ‖Bu‖ ≥ ½ ‖⟪(AB-BA)u, u⟫‖.
This is the abstract form of the Heisenberg uncertainty principle. -/
theorem heisenberg_uncertainty (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E) :
    ‖A u‖ * ‖B u‖ ≥ ‖⟪(A * B - B * A) u, u⟫_ℂ‖ / 2 := by
  have h := heisenberg_norm_bound A B hA hB u
  have h2 : 0 ≤ ‖⟪(A * B - B * A) u, u⟫_ℂ‖ := norm_nonneg _
  linarith

/-- When the commutator vanishes, the uncertainty bound is trivially 0 ≤ ‖Au‖ · ‖Bu‖. -/
theorem heisenberg_uncertainty_commute (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E)
    (hAB : A * B = B * A) :
    ‖A u‖ * ‖B u‖ ≥ 0 := mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Symmetric form**: ‖Au‖ · ‖Bu‖ ≥ ½ ‖⟪(AB-BA)u, u⟫‖ also holds
    with A and B swapped, since ‖(AB-BA)u‖ = ‖(BA-AB)u‖. -/
theorem heisenberg_uncertainty_symm (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E) :
    ‖B u‖ * ‖A u‖ ≥ ‖⟪(A * B - B * A) u, u⟫_ℂ‖ / 2 := by
  rw [mul_comm]
  exact heisenberg_uncertainty A B hA hB u

/-- **Unit vector form**: For a unit vector u (‖u‖ = 1), the bound reads
    ‖Au‖ · ‖Bu‖ ≥ ½ |⟪[A,B]u, u⟫|.
    This is the form used in quantum mechanics for normalized states. -/
theorem heisenberg_uncertainty_unit (A B : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (u : E) (hu : ‖u‖ = 1) :
    ‖A u‖ * ‖B u‖ ≥ ‖⟪(A * B - B * A) u, u⟫_ℂ‖ / 2 :=
  heisenberg_uncertainty A B hA hB u

end CauchySchwarzOQ01OQ01OQ02
