/-
# Gram-Schmidt via Cauchy-Schwarz — OQ-01: one step is an orthogonal projector

Open Question (cauchy-schwarz-oq-01-oq-02-oq-01), a follow-up to
`CauchySchwarzOQ01OQ02.lean` (Gram-Schmidt via Cauchy-Schwarz).

The parent file showed the Gram-Schmidt projection `orthProj v u = (⟪v,u⟫/⟪v,v⟫)•v`
is **bounded** (`‖orthProj v u‖ ≤ ‖u‖`), produces an **orthogonal residual**
(`⟪gsStep v u, v⟫ = 0`), and satisfies **Pythagoras**. It did NOT establish that
`u ↦ orthProj v u` is an *orthogonal projector* in the operator sense.

This file proves exactly that, with **zero axioms and zero sorries**:

* **Idempotency** `orthProj v (orthProj v u) = orthProj v u` (`P² = P`).
* **Kernel** `orthProj v (gsStep v u) = 0`: the projector annihilates the residual.
* **Residual idempotency** `gsStep v (gsStep v u) = gsStep v u` (`(1−P)² = 1−P`).
* **Reconstruction** `orthProj v u + gsStep v u = u` (`P + (1−P) = id`).
* **Exact norm** `‖orthProj v u‖ = ‖⟪v,u⟫‖ / ‖v‖` (the Cauchy-Schwarz bound is the
  *value*, not merely an upper bound).

Together these are the projector axioms for the rank-one orthogonal projection onto
`span{v}`, completing the operator-theoretic picture of one Gram-Schmidt step.

The definitions `orthProj`, `projCoeff`, `gsStep` mirror the verified parent file; this
file is kept self-contained (Mathlib-only). The scalar field `𝕜` is taken as an explicit
argument of each definition so the projector identities (whose statements do not otherwise
mention `𝕜`) are unambiguous.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace

namespace CauchySchwarzOQ01OQ02OQ01

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## Definitions (mirroring the verified parent; `𝕜` explicit) -/

/-- Orthogonal projection of `u` onto `v`: `proj_v(u) = (⟪v,u⟫/⟪v,v⟫) • v`. -/
noncomputable def orthProj (v u : E) : E :=
  ((⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜 : 𝕜)) • v

/-- The projection coefficient `c = ⟪v,u⟫/⟪v,v⟫`. -/
noncomputable def projCoeff (v u : E) : 𝕜 :=
  ⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜

/-- One Gram-Schmidt step: `gsStep v u = u − proj_v(u)`. -/
noncomputable def gsStep (v u : E) : E :=
  u - orthProj 𝕜 v u

/-- The residual is orthogonal to the direction vector (right argument). -/
theorem residual_orthogonal' (u v : E) (hv : v ≠ 0) :
    ⟪v, u - orthProj 𝕜 v u⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]
  unfold orthProj
  simp only [inner_sub_left, inner_smul_left, map_div₀, inner_conj_symm]
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := inner_self_ne_zero.mpr hv
  field_simp
  ring

/-! ## Part I: The projection is a projector (P² = P) -/

/-- Projecting a multiple of `v` onto `v` returns it unchanged: `orthProj v (c•v) = c•v`.
    This is the eigenvalue-1 (range) behaviour of the projector. -/
theorem orthProj_smul_self (v : E) (c : 𝕜) (hv : v ≠ 0) :
    orthProj 𝕜 v (c • v) = c • v := by
  unfold orthProj
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := inner_self_ne_zero.mpr hv
  rw [inner_smul_right, mul_div_assoc, div_self hvv, mul_one]

/-- `orthProj v u` lies in `span{v}`, so re-projecting it does nothing:
    **idempotency** `P² = P`. -/
theorem orthProj_idempotent (u v : E) (hv : v ≠ 0) :
    orthProj 𝕜 v (orthProj 𝕜 v u) = orthProj 𝕜 v u := by
  have h1 : orthProj 𝕜 v u = projCoeff 𝕜 v u • v := rfl
  rw [h1, orthProj_smul_self 𝕜 v (projCoeff 𝕜 v u) hv]

/-! ## Part II: The projector annihilates the residual -/

/-- The direction vector is orthogonal to the residual (left argument). -/
theorem inner_left_gsStep (u v : E) (hv : v ≠ 0) :
    ⟪v, gsStep 𝕜 v u⟫_𝕜 = 0 := by
  unfold gsStep
  exact residual_orthogonal' 𝕜 u v hv

/-- The projector kills the residual: `orthProj v (gsStep v u) = 0`.
    The residual lies in the kernel `(span{v})^⊥`. -/
theorem orthProj_gsStep_eq_zero (u v : E) (hv : v ≠ 0) :
    orthProj 𝕜 v (gsStep 𝕜 v u) = 0 := by
  unfold orthProj
  rw [inner_left_gsStep 𝕜 u v hv, zero_div, zero_smul]

/-- The residual map `1 − P` is idempotent: `gsStep v (gsStep v u) = gsStep v u`. -/
theorem gsStep_idempotent (u v : E) (hv : v ≠ 0) :
    gsStep 𝕜 v (gsStep 𝕜 v u) = gsStep 𝕜 v u := by
  have h : gsStep 𝕜 v (gsStep 𝕜 v u) = gsStep 𝕜 v u - orthProj 𝕜 v (gsStep 𝕜 v u) := rfl
  rw [h, orthProj_gsStep_eq_zero 𝕜 u v hv, sub_zero]

/-! ## Part III: Reconstruction `P + (1 − P) = id` -/

/-- The projection and residual reconstruct the input: `orthProj v u + gsStep v u = u`. -/
theorem orthProj_add_gsStep (u v : E) :
    orthProj 𝕜 v u + gsStep 𝕜 v u = u := by
  unfold gsStep
  abel

/-! ## Part IV: The exact projection norm (Cauchy-Schwarz as an equality) -/

/-- The projection norm equals `‖⟪v,u⟫‖ / ‖v‖` exactly. The parent's CS bound
    `‖orthProj v u‖ ≤ ‖u‖` is the inequality `‖⟪v,u⟫‖/‖v‖ ≤ ‖u‖` in disguise. -/
theorem orthProj_norm_eq (u v : E) (hv : v ≠ 0) :
    ‖orthProj 𝕜 v u‖ = ‖⟪v, u⟫_𝕜‖ / ‖v‖ := by
  unfold orthProj
  rw [norm_smul, norm_div]
  have hvv : ‖⟪v, v⟫_𝕜‖ = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hv_ne : ‖v‖ ≠ 0 := by simpa using norm_pos_iff.mpr hv
  rw [hvv]
  field_simp

/-- The exact norm recovers the parent's Cauchy-Schwarz upper bound `‖orthProj v u‖ ≤ ‖u‖`. -/
theorem orthProj_norm_le (u v : E) (hv : v ≠ 0) :
    ‖orthProj 𝕜 v u‖ ≤ ‖u‖ := by
  rw [orthProj_norm_eq 𝕜 u v hv]
  have hv_pos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  rw [div_le_iff₀ hv_pos]
  calc ‖⟪v, u⟫_𝕜‖ ≤ ‖v‖ * ‖u‖ := norm_inner_le_norm v u
    _ = ‖u‖ * ‖v‖ := by ring

/-! ## Part V: Capstone — one Gram-Schmidt step is an orthogonal projector -/

/-- **Summary.** For `v ≠ 0`, `P := orthProj v` is the orthogonal projector onto
    `span{v}`: it is idempotent, its complement `1 − P = gsStep v` is idempotent,
    they sum to the identity, and `P` annihilates the residual. -/
theorem gsStep_is_orthogonal_projector (v : E) (hv : v ≠ 0) :
    (∀ u : E, orthProj 𝕜 v (orthProj 𝕜 v u) = orthProj 𝕜 v u) ∧
    (∀ u : E, gsStep 𝕜 v (gsStep 𝕜 v u) = gsStep 𝕜 v u) ∧
    (∀ u : E, orthProj 𝕜 v u + gsStep 𝕜 v u = u) ∧
    (∀ u : E, orthProj 𝕜 v (gsStep 𝕜 v u) = 0) :=
  ⟨fun u => orthProj_idempotent 𝕜 u v hv,
   fun u => gsStep_idempotent 𝕜 u v hv,
   fun u => orthProj_add_gsStep 𝕜 u v,
   fun u => orthProj_gsStep_eq_zero 𝕜 u v hv⟩

end CauchySchwarzOQ01OQ02OQ01
