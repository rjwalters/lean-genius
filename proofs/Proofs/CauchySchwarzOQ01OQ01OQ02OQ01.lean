/-
# The Robertson–Schrödinger Uncertainty Relation

Open Question: cauchy-schwarz-oq-01-oq-01-oq-02-oq-01
Parent: cauchy-schwarz-oq-01-oq-01-oq-02 ("Robertson's uncertainty inequality from Cauchy-Schwarz")

The parent entry derives **Robertson's** inequality
  ΔA(ψ) · ΔB(ψ)  ≥  (1/2) · |⟨ψ|[A,B]|ψ⟩|
by applying Cauchy–Schwarz to the centered vectors u = (A−⟨A⟩)ψ, v = (B−⟨B⟩)ψ and
keeping **only the antisymmetric (imaginary) part** of ⟪u,v⟫.

The Cauchy–Schwarz inequality actually controls the *full* modulus
  ‖u‖²·‖v‖²  ≥  |⟪u,v⟫|²  =  (Re⟪u,v⟫)²  +  (Im⟪u,v⟫)² .
The imaginary part is the commutator (the Robertson term); the **real part is the
covariance** ½⟨{A,B}⟩ − ⟨A⟩⟨B⟩ (the anticommutator term that Robertson throws away).
Retaining it gives **Schrödinger's (1930) strengthening**:

  σ_A² · σ_B²  ≥  ( ½⟨{A,B}⟩ − ⟨A⟩⟨B⟩ )²  +  ( ½ |⟨[A,B]⟩| )² .

This is strictly sharper than Robertson whenever the covariance is nonzero, and it
reduces to Robertson on dropping the (nonnegative) covariance square. This file proves
the strengthening, the covariance identity behind it, and that it dominates Robertson.

All results are 0-axiom, building on the parent file's symmetric-operator API.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic
import Proofs.CauchySchwarzOQ01OQ01OQ02

open scoped InnerProductSpace
open Complex

namespace CauchySchwarzOQ01OQ01OQ02OQ01

open CauchySchwarzOQ01OQ01OQ02 (expVal stdDev commutatorEV expVal_self_conj
  centered_antisymmetric_eq_commutator)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Part I: A scalar identity for the squared modulus -/

/-- `‖z‖² = (Re z)² + (Im z)²` for a complex number. -/
private theorem cnorm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-! ## Part II: The covariance (anticommutator) functional -/

/-- The anticommutator expectation value `⟨ψ|{A,B}|ψ⟩ = ⟨ψ|(AB+BA)|ψ⟩`. -/
noncomputable def anticommutatorEV (A B : E →ₗ[ℂ] E) (ψ : E) : ℂ :=
  ⟪ψ, A (B ψ) + B (A ψ)⟫_ℂ

/-- The (symmetric) covariance of `A` and `B` in the state `ψ`:
`Cov(A,B) = ½⟨{A,B}⟩ − ⟨A⟩⟨B⟩`. This is the quantity Robertson discards. -/
noncomputable def covarianceEV (A B : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  (anticommutatorEV A B ψ / 2 - expVal A ψ * expVal B ψ).re

/-- Expansion of a centered inner product, mirroring the parent's private helper.
For symmetric `X` and a unit state, `⟪Xψ − ⟨X⟩ψ, Yψ − ⟨Y⟩ψ⟫ = ⟨ψ|XY|ψ⟩ − ⟨X⟩⟨Y⟩`. -/
private theorem inner_centered_eq
    {X Y : E →ₗ[ℂ] E} (hX : X.IsSymmetric)
    (ψ : E) (hψψ : ⟪ψ, ψ⟫_ℂ = 1)
    (hXreal : starRingEnd ℂ ⟪ψ, X ψ⟫_ℂ = ⟪ψ, X ψ⟫_ℂ) :
    ⟪X ψ - ⟪ψ, X ψ⟫_ℂ • ψ, Y ψ - ⟪ψ, Y ψ⟫_ℂ • ψ⟫_ℂ =
    ⟪ψ, X (Y ψ)⟫_ℂ - ⟪ψ, X ψ⟫_ℂ * ⟪ψ, Y ψ⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [hX ψ (Y ψ), hX ψ ψ, hψψ, hXreal]
  ring

/-- Unit-norm states have `⟪ψ,ψ⟫ = 1`. -/
private theorem inner_self_one {ψ : E} (hψ : ‖ψ‖ = 1) : ⟪ψ, ψ⟫_ℂ = (1 : ℂ) := by
  have h := @inner_self_eq_norm_sq_to_K ℂ E _ _ _ ψ
  simp only [RCLike.ofReal_pow] at h
  rw [h, hψ]; norm_num

/-- **Covariance identity.** The real part of the centered inner product `⟪u,v⟫`
(with `u,v` the centered vectors) is exactly the covariance `½⟨{A,B}⟩ − ⟨A⟩⟨B⟩`. -/
theorem covarianceEV_eq_re
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    covarianceEV A B ψ =
      (⟪A ψ - (expVal A ψ) • ψ, B ψ - (expVal B ψ) • ψ⟫_ℂ).re := by
  have hψψ : ⟪ψ, ψ⟫_ℂ = (1 : ℂ) := inner_self_one hψ
  have hAreal : starRingEnd ℂ ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := expVal_self_conj A hA ψ
  have hBreal : starRingEnd ℂ ⟪ψ, B ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ := expVal_self_conj B hB ψ
  set u := A ψ - (expVal A ψ) • ψ with hu
  set v := B ψ - (expVal B ψ) • ψ with hv
  -- Expand both ⟪u,v⟫ and ⟪v,u⟫ via the centered-inner expansion.
  have huv : (⟪u, v⟫_ℂ : ℂ) = ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, A ψ⟫_ℂ * ⟪ψ, B ψ⟫_ℂ := by
    rw [hu, hv]; exact inner_centered_eq hA ψ hψψ hAreal (Y := B)
  have hvu : (⟪v, u⟫_ℂ : ℂ) = ⟪ψ, B (A ψ)⟫_ℂ - ⟪ψ, B ψ⟫_ℂ * ⟪ψ, A ψ⟫_ℂ := by
    rw [hu, hv]; exact inner_centered_eq hB ψ hψψ hBreal (Y := A)
  -- ⟪v,u⟫ = conj ⟪u,v⟫, so ⟪u,v⟫ + ⟪v,u⟫ = 2 · Re⟪u,v⟫.
  have hconj : (⟪v, u⟫_ℂ : ℂ) = starRingEnd ℂ ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have hsum : (⟪u, v⟫_ℂ : ℂ) + ⟪v, u⟫_ℂ =
      anticommutatorEV A B ψ - 2 * (expVal A ψ * expVal B ψ) := by
    rw [huv, hvu]
    unfold anticommutatorEV expVal
    rw [inner_add_right]
    ring
  -- Take real parts. Re of the symmetric sum = 2·Re⟪u,v⟫ (since ⟪v,u⟫ = conj⟪u,v⟫).
  have hsumre : (anticommutatorEV A B ψ - 2 * (expVal A ψ * expVal B ψ)).re
      = 2 * (⟪u, v⟫_ℂ).re := by
    rw [← hsum, hconj, Complex.add_re, Complex.conj_re]; ring
  -- covarianceEV is the real part of (sum)/2.
  unfold covarianceEV
  have hdiv : anticommutatorEV A B ψ / 2 - expVal A ψ * expVal B ψ =
      (anticommutatorEV A B ψ - 2 * (expVal A ψ * expVal B ψ)) / 2 := by ring
  rw [hdiv, Complex.div_ofNat_re, hsumre]; ring

/-! ## Part III: The Robertson–Schrödinger inequality -/

/-- **Robertson–Schrödinger uncertainty relation.** For symmetric operators `A`, `B`
and a unit state `ψ`,
  σ_A² · σ_B²  ≥  Cov(A,B)²  +  ( ½ |⟨[A,B]⟩| )² .
The first term on the right is the anticommutator (covariance) contribution that
strengthens Robertson; the second is the Robertson commutator term itself. -/
theorem robertson_schrodinger_inequality
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    stdDev A ψ ^ 2 * stdDev B ψ ^ 2 ≥
      covarianceEV A B ψ ^ 2 + ((1/2 : ℝ) * ‖commutatorEV A B ψ‖) ^ 2 := by
  set u := A ψ - (expVal A ψ) • ψ with hu
  set v := B ψ - (expVal B ψ) • ψ with hv
  set w : ℂ := ⟪u, v⟫_ℂ with hw
  -- (1) Full Cauchy–Schwarz: ‖w‖² ≤ ‖u‖²·‖v‖².
  have hcs : ‖w‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hcs2 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have hmul : (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
    nlinarith [norm_nonneg w, norm_nonneg u, norm_nonneg v, hcs]
  -- (2) stdDev² = ‖·‖² for the centered vectors (definitional).
  have hsA : stdDev A ψ ^ 2 = ‖u‖ ^ 2 := by rw [hu]; rfl
  have hsB : stdDev B ψ ^ 2 = ‖v‖ ^ 2 := by rw [hv]; rfl
  -- (3) Real part of w is the covariance.
  have hRe : covarianceEV A B ψ = w.re := by
    rw [hw, hu, hv]; exact covarianceEV_eq_re A B hA hB ψ hψ
  -- (4) Imaginary part of w carries the commutator: w − conj w = commutatorEV.
  have hcomm : (w : ℂ) - starRingEnd ℂ w = commutatorEV A B ψ := by
    have h := centered_antisymmetric_eq_commutator A B hA hB ψ hψ
    simp only at h
    have hconj : starRingEnd ℂ w = (⟪v, u⟫_ℂ : ℂ) := by
      rw [hw]; exact inner_conj_symm v u
    rw [hconj, hw]; exact h
  -- From hcomm: commutator is purely imaginary, with im = 2·w.im.
  have hcomm_im : (commutatorEV A B ψ).im = 2 * w.im := by
    rw [← hcomm, Complex.sub_im, Complex.conj_im]; ring
  have hcomm_re : (commutatorEV A B ψ).re = 0 := by
    rw [← hcomm, Complex.sub_re, Complex.conj_re, sub_self]
  have hcomm_normsq : ‖commutatorEV A B ψ‖ ^ 2 = 4 * w.im ^ 2 := by
    rw [cnorm_sq, hcomm_re, hcomm_im]; ring
  -- (5) Assemble: RHS = w.re² + w.im² = ‖w‖² ≤ ‖u‖²‖v‖² = LHS.
  have hRHS : covarianceEV A B ψ ^ 2 + ((1/2 : ℝ) * ‖commutatorEV A B ψ‖) ^ 2
      = w.re ^ 2 + w.im ^ 2 := by
    rw [hRe]
    have : ((1/2 : ℝ) * ‖commutatorEV A B ψ‖) ^ 2 = (1/4) * ‖commutatorEV A B ψ‖ ^ 2 := by
      ring
    rw [this, hcomm_normsq]; ring
  have hwsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := cnorm_sq w
  rw [hsA, hsB, ge_iff_le, hRHS, ← hwsq]
  exact hcs2

/-! ## Part IV: Robertson is the weaker corollary -/

/-- **Schrödinger ⟹ Robertson.** Dropping the (nonnegative) covariance square recovers
the parent's Robertson bound `σ_A·σ_B ≥ ½|⟨[A,B]⟩|`. The strengthening is therefore
genuine: equality in Robertson forces the covariance to vanish. -/
theorem robertson_of_schrodinger
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    stdDev A ψ * stdDev B ψ ≥ (1/2 : ℝ) * ‖commutatorEV A B ψ‖ := by
  have hRS := robertson_schrodinger_inequality A B hA hB ψ hψ
  have hcov : covarianceEV A B ψ ^ 2 ≥ 0 := sq_nonneg _
  -- σ_A²σ_B² ≥ (½‖[A,B]‖)², and both sides nonnegative ⇒ take square roots.
  have hsq : (stdDev A ψ * stdDev B ψ) ^ 2 ≥ ((1/2 : ℝ) * ‖commutatorEV A B ψ‖) ^ 2 := by
    have hsplit : stdDev A ψ ^ 2 * stdDev B ψ ^ 2 = (stdDev A ψ * stdDev B ψ) ^ 2 := by ring
    nlinarith [hRS, hcov]
  have hpos : (0 : ℝ) ≤ (1/2 : ℝ) * ‖commutatorEV A B ψ‖ := by positivity
  have hstd : (0 : ℝ) ≤ stdDev A ψ * stdDev B ψ := by
    apply mul_nonneg <;> exact norm_nonneg _
  nlinarith [hsq, hpos, hstd]

/-- **Covariance as the gap.** The exact Schrödinger identity packaged as a gap:
σ_A²σ_B² − (½|⟨[A,B]⟩|)² ≥ Cov(A,B)² ≥ 0, with the first ≥ being the inequality and
the covariance² the explicit amount by which Schrödinger improves on Robertson. -/
theorem schrodinger_gap_nonneg
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    stdDev A ψ ^ 2 * stdDev B ψ ^ 2 - ((1/2 : ℝ) * ‖commutatorEV A B ψ‖) ^ 2
      ≥ covarianceEV A B ψ ^ 2 := by
  have hRS := robertson_schrodinger_inequality A B hA hB ψ hψ
  linarith

end CauchySchwarzOQ01OQ01OQ02OQ01
