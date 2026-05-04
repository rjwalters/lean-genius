/-
# Robertson's Uncertainty Inequality from Cauchy-Schwarz
Open Question: cauchy-schwarz-oq-01-oq-01-oq-02
"Can the Heisenberg uncertainty principle be derived from the complex Cauchy-Schwarz inequality?"

Answer: YES — Robertson (1929) showed that for symmetric operators A, B on a Hilbert space,
  ΔA(ψ) · ΔB(ψ) ≥ (1/2) · |⟨ψ|[A,B]|ψ⟩|
This follows directly from the Cauchy-Schwarz inequality applied to the centered vectors.
The standard quantum-mechanical Heisenberg relation ΔxΔp ≥ ħ/2 is the special case [x̂,p̂] = iħ.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

open scoped InnerProductSpace
open Complex

namespace CauchySchwarzOQ01OQ01OQ02

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Part I: Antisymmetric inner product bound -/

private theorem norm_sub_conj_le (z : ℂ) : ‖z - starRingEnd ℂ z‖ ≤ 2 * ‖z‖ := by
  calc ‖z - starRingEnd ℂ z‖
      ≤ ‖z‖ + ‖starRingEnd ℂ z‖ := norm_sub_le z _
    _ = ‖z‖ + ‖z‖ := by rw [RCLike.norm_conj]
    _ = 2 * ‖z‖ := by ring

-- For any u v : E, (1/2)|⟪u,v⟫ - ⟪v,u⟫| ≤ ‖u‖·‖v‖
theorem cs_antisymmetric_bound (u v : E) :
    (1/2 : ℝ) * ‖(⟪u, v⟫_ℂ : ℂ) - ⟪v, u⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
  have hconj : ⟪v, u⟫_ℂ = starRingEnd ℂ ⟪u, v⟫_ℂ := by
    rw [inner_conj_symm]
  rw [hconj]
  have h1 : ‖(⟪u, v⟫_ℂ : ℂ) - starRingEnd ℂ ⟪u, v⟫_ℂ‖ ≤ 2 * ‖(⟪u, v⟫_ℂ : ℂ)‖ :=
    norm_sub_conj_le ⟪u, v⟫_ℂ
  have h2 : ‖(⟪u, v⟫_ℂ : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  linarith

/-! ## Part II: Symmetric operators and real expectation values -/

noncomputable def expVal (A : E →ₗ[ℂ] E) (ψ : E) : ℂ := ⟪ψ, A ψ⟫_ℂ

-- Symmetric operators have real expectation values
theorem expVal_im_zero (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (ψ : E) :
    (expVal A ψ).im = 0 := by
  unfold expVal
  have hself : ⟪ψ, A ψ⟫_ℂ = starRingEnd ℂ ⟪ψ, A ψ⟫_ℂ := by
    rw [inner_conj_symm, ← hA ψ ψ]
  have h := congr_arg Complex.im hself
  simp only [RCLike.star_def, starRingEnd_apply, map_star,
             RCLike.conj_im, neg_eq_iff_eq_neg, neg_neg] at h
  linarith

-- The expectation value equals its complex conjugate
theorem expVal_self_conj (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (ψ : E) :
    starRingEnd ℂ (expVal A ψ) = expVal A ψ := by
  have him := expVal_im_zero A hA ψ
  apply Complex.ext
  · simp [starRingEnd_apply, Complex.conj_re]
  · simp [starRingEnd_apply, Complex.conj_im, him]

/-! ## Part III: Commutator and centered vectors -/

-- The commutator expectation value
noncomputable def commutatorEV (A B : E →ₗ[ℂ] E) (ψ : E) : ℂ :=
  ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ

-- Standard deviation of A in state ψ
noncomputable def stdDev (A : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  ‖A ψ - (expVal A ψ) • ψ‖

-- Helper: expand ⟪Xψ - c•ψ, Yψ - d•ψ⟫ = ⟪ψ,X(Yψ)⟫ - c*d
-- using symmetry hX : ⟪Xψ,ψ⟫ = ⟪ψ,Xψ⟫ = c (with star c = c) and ⟪ψ,ψ⟫=1
private theorem inner_centered_eq
    {X Y : E →ₗ[ℂ] E} (hX : X.IsSymmetric)
    (ψ : E) (hψψ : ⟪ψ, ψ⟫_ℂ = 1)
    (hXreal : starRingEnd ℂ ⟪ψ, X ψ⟫_ℂ = ⟪ψ, X ψ⟫_ℂ) :
    ⟪X ψ - ⟪ψ, X ψ⟫_ℂ • ψ, Y ψ - ⟪ψ, Y ψ⟫_ℂ • ψ⟫_ℂ =
    ⟪ψ, X (Y ψ)⟫_ℂ - ⟪ψ, X ψ⟫_ℂ * ⟪ψ, Y ψ⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [hX ψ (Y ψ), hX ψ ψ, hψψ, hXreal]
  ring

-- For unit ψ and symmetric A, B: ⟪u,v⟫ - ⟪v,u⟫ = commutatorEV A B ψ
-- where u = Aψ - ⟨A⟩ψ, v = Bψ - ⟨B⟩ψ
theorem centered_antisymmetric_eq_commutator
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    let u := A ψ - (expVal A ψ) • ψ
    let v := B ψ - (expVal B ψ) • ψ
    (⟪u, v⟫_ℂ : ℂ) - ⟪v, u⟫_ℂ = commutatorEV A B ψ := by
  simp only []
  unfold expVal commutatorEV
  have hψψ : ⟪ψ, ψ⟫_ℂ = (1 : ℂ) := by
    have h := @inner_self_eq_norm_sq_to_K ℂ E _ _ _ ψ
    simp only [RCLike.ofReal_pow] at h
    rw [h, hψ]; norm_num
  have hAreal : starRingEnd ℂ ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := expVal_self_conj A hA ψ
  have hBreal : starRingEnd ℂ ⟪ψ, B ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ := expVal_self_conj B hB ψ
  -- Expand each centered inner product
  have huv := inner_centered_eq hA ψ hψψ hAreal (Y := B)
  have hvu := inner_centered_eq hB ψ hψψ hBreal (Y := A)
  rw [huv, hvu, inner_sub_right]
  ring

/-! ## Part IV: Robertson's Inequality -/

-- Robertson (1929): ΔA · ΔB ≥ (1/2)|⟨ψ|[A,B]|ψ⟩|
theorem robertson_inequality
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    stdDev A ψ * stdDev B ψ ≥ (1/2 : ℝ) * ‖commutatorEV A B ψ‖ := by
  unfold stdDev
  set u := A ψ - (expVal A ψ) • ψ
  set v := B ψ - (expVal B ψ) • ψ
  -- Cauchy-Schwarz: ‖u‖·‖v‖ ≥ (1/2)|⟪u,v⟫ - ⟪v,u⟫|
  have hcs := cs_antisymmetric_bound u v
  -- The antisymmetric part equals the commutator EV
  have hcomm := centered_antisymmetric_eq_commutator A B hA hB ψ hψ
  simp only at hcomm
  rw [hcomm] at hcs
  linarith

/-! ## Part V: Heisenberg uncertainty principle -/

-- For operators with constant commutator [A,B] = c·id:
-- ΔA(ψ) · ΔB(ψ) ≥ |c|/2 for any unit state ψ
theorem heisenberg_constant_commutator
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (c : ℂ) (hcomm : ∀ ψ : E, A (B ψ) - B (A ψ) = c • ψ)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    stdDev A ψ * stdDev B ψ ≥ (1/2 : ℝ) * ‖c‖ := by
  have hrobertson := robertson_inequality A B hA hB ψ hψ
  -- commutatorEV A B ψ = ⟪ψ, c•ψ⟫ = c * ⟪ψ,ψ⟫ = c * 1 = c
  have hcEV : commutatorEV A B ψ = c := by
    unfold commutatorEV
    have hψψ : ⟪ψ, ψ⟫_ℂ = (1 : ℂ) := by
      have h := @inner_self_eq_norm_sq_to_K ℂ E _ _ _ ψ
      simp only [RCLike.ofReal_pow] at h
      rw [h, hψ]; norm_num
    rw [hcomm ψ, inner_smul_right, hψψ, mul_one]
  rw [hcEV] at hrobertson
  linarith

end CauchySchwarzOQ01OQ01OQ02
