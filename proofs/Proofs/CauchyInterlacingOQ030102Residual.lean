import Mathlib

/-
# Residual (a-posteriori) eigenvalue bound for Hermitian operators

This file proves the **converse / a-posteriori stability** companion to the Weyl
perturbation bound of the parent entry `cauchy-interlacing-theorem-oq-03-oq-01`
(`weyl_eigenvalue_stability` in `CauchyInterlacingOQ030101Stability.lean`).

Where Weyl's bound certifies that *exact* eigenvalues of two nearby operators are
close, the residual bound goes the other way: it **certifies a computed
eigenpair**. Given a unit vector `x` and a scalar `lam` whose residual
`‖T x − lam·x‖` is small, *some* genuine eigenvalue `μ k` must lie within the
residual of `lam`. This is the standard a-posteriori error estimate used in
numerical linear algebra (Bauer–Fike for the Hermitian / normal case).

## Statement

For `T` presented by an orthonormal eigenbasis `b` with real eigenvalues `μ`
(`T (b i) = μ i · b i`), and any unit vector `x`,

  `∃ k, |μ k − lam| ≤ ‖T x − lam·x‖`.

The presentation `T (b i) = μ i · b i` with `b` orthonormal and `μ` real is
exactly the spectral content of a Hermitian operator (spectral theorem), taken as
input as in the parent keystone.

## Proof

Expand `x` in the eigenbasis, `x = ∑ⱼ cⱼ bⱼ` with `cⱼ = ⟪bⱼ, x⟫`. Linearity and
`T bⱼ = μⱼ bⱼ` give the coordinatewise identity

  `⟪bᵢ, T x − lam·x⟫ = (μᵢ − lam)·cᵢ`,

so Parseval (`b.repr` is a linear isometry to `EuclideanSpace`) yields

  `‖T x − lam·x‖² = ∑ᵢ (μᵢ − lam)²|cᵢ|²`   and   `‖x‖² = ∑ᵢ |cᵢ|² = 1`.

Picking the index `k` minimising `(μᵢ − lam)²`,

  `(μ k − lam)² = (μ k − lam)²·∑ᵢ|cᵢ|² ≤ ∑ᵢ(μᵢ − lam)²|cᵢ|² = ‖T x − lam·x‖²`,

and taking square roots gives the bound. No self-adjointness is needed beyond the
eigenbasis presentation; the argument only uses linearity and orthonormality.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open InnerProductSpace

namespace CauchyInterlacing.Residual

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## Parseval's identity in the orthonormal eigenbasis -/

/-- **Parseval's identity.** For an orthonormal basis `b` of a finite-dimensional
inner product space, `‖v‖² = ∑ᵢ ‖⟪bᵢ, v⟫‖²`. Immediate from `b.repr` being a
linear isometry onto `EuclideanSpace` together with the coordinate formula
`b.repr v i = ⟪bᵢ, v⟫`. -/
theorem parseval {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖@inner 𝕜 E _ (b i) v‖ ^ 2 := by
  rw [← b.repr.norm_map v, EuclideanSpace.norm_sq_eq]
  simp_rw [b.repr_apply_apply]

/-! ## The eigen-coordinate identity -/

/-- **Eigen-coordinate identity.** If `T (b i) = μ i · b i` for an orthonormal
basis `b`, then for every `x` the `bᵢ`-coordinate of `T x` is `μᵢ` times the
`bᵢ`-coordinate of `x`:  `⟪bᵢ, T x⟫ = μᵢ · ⟪bᵢ, x⟫`. Proved by expanding `x` in
the eigenbasis and using orthonormality; no adjoint / self-adjointness needed. -/
theorem inner_eigen {n : ℕ} (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (x : E) (i : Fin n) :
    @inner 𝕜 E _ (b i) (T x) = (μ i : 𝕜) * @inner 𝕜 E _ (b i) x := by
  have hTx : (T x : E) = ∑ j, (@inner 𝕜 E _ (b j) x) • ((μ j : 𝕜) • b j) := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, hbT j]
  rw [hTx, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl, mul_one]
    exact mul_comm _ _
  · intro j _ hj
    rw [inner_smul_right, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i j, if_neg (Ne.symm hj), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The residual eigenvalue bound -/

/-- **Residual (a-posteriori) eigenvalue bound.** Let `T` be presented by an
orthonormal eigenbasis `b` with real eigenvalues `μ` (`T (b i) = μ i · b i`).
For every unit vector `x` and scalar `lam`, some eigenvalue `μ k` lies within the
residual `‖T x − lam·x‖` of `lam`:

`∃ k, |μ k − lam| ≤ ‖T x − lam·x‖`.

This certifies an approximately-computed eigenpair `(lam, x)`: a small residual
*guarantees* a true eigenvalue nearby. It is the converse direction to Weyl's
perturbation bound `weyl_eigenvalue_stability`. -/
theorem dist_to_spectrum_le_residual {n : ℕ} (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (x : E) (hx : ‖x‖ = 1) (lam : ℝ) :
    ∃ k, |μ k - lam| ≤ ‖T x - (lam : 𝕜) • x‖ := by
  set ε : ℝ := ‖T x - (lam : 𝕜) • x‖ with hε_def
  have hε : 0 ≤ ε := norm_nonneg _
  -- coordinatewise: ⟪bᵢ, T x − lam·x⟫ = (μᵢ − lam)·⟪bᵢ, x⟫
  have hcoord : ∀ i, @inner 𝕜 E _ (b i) (T x - (lam : 𝕜) • x)
      = ((μ i - lam : ℝ) : 𝕜) * @inner 𝕜 E _ (b i) x := by
    intro i
    rw [inner_sub_right, inner_eigen T b μ hbT x i, inner_smul_right]
    push_cast; ring
  -- squared coordinate norms
  have hni : ∀ i, ‖@inner 𝕜 E _ (b i) (T x - (lam : 𝕜) • x)‖ ^ 2
      = (μ i - lam) ^ 2 * ‖@inner 𝕜 E _ (b i) x‖ ^ 2 := by
    intro i
    rw [hcoord i, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  -- Parseval for `x`:  ∑ᵢ |cᵢ|² = 1
  have hx2 : ∑ i, ‖@inner 𝕜 E _ (b i) x‖ ^ 2 = 1 := by
    rw [← parseval b x, hx]; norm_num
  -- Parseval for the residual:  ∑ᵢ (μᵢ − lam)²|cᵢ|² = ε²
  have hres2 : ∑ i, (μ i - lam) ^ 2 * ‖@inner 𝕜 E _ (b i) x‖ ^ 2 = ε ^ 2 := by
    have hp := parseval b (T x - (lam : 𝕜) • x)
    rw [hε_def]
    rw [hp]
    exact (Finset.sum_congr rfl (fun i _ => hni i)).symm
  -- Fin n is nonempty (x is a unit vector)
  have hne : Nonempty (Fin n) := by
    rcases isEmpty_or_nonempty (Fin n) with hEmpty | hNe
    · haveI := hEmpty; simp at hx2
    · exact hNe
  haveI := hne
  -- pick the eigenvalue closest to `lam`
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_min_image Finset.univ (fun i => (μ i - lam) ^ 2) Finset.univ_nonempty
  refine ⟨k, ?_⟩
  -- (μ k − lam)² ≤ ε²
  have hle : (μ k - lam) ^ 2 ≤ ε ^ 2 := by
    calc (μ k - lam) ^ 2
        = (μ k - lam) ^ 2 * ∑ i, ‖@inner 𝕜 E _ (b i) x‖ ^ 2 := by rw [hx2]; ring
      _ = ∑ i, (μ k - lam) ^ 2 * ‖@inner 𝕜 E _ (b i) x‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, (μ i - lam) ^ 2 * ‖@inner 𝕜 E _ (b i) x‖ ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            exact mul_le_mul_of_nonneg_right (hk i (Finset.mem_univ i)) (sq_nonneg _)
      _ = ε ^ 2 := hres2
  -- take square roots
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hε] at h

/-- **a-posteriori bound with an explicit residual estimate.** If the residual is
known only up to an upper bound `ε` (the typical situation when `ε` is computed),
some eigenvalue still lies within `ε` of `lam`. -/
theorem residual_eigenvalue_bound {n : ℕ} (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (x : E) (hx : ‖x‖ = 1) (lam ε : ℝ)
    (hres : ‖T x - (lam : 𝕜) • x‖ ≤ ε) :
    ∃ k, |μ k - lam| ≤ ε := by
  obtain ⟨k, hk⟩ := dist_to_spectrum_le_residual T b μ hbT x hx lam
  exact ⟨k, le_trans hk hres⟩

/-! ## Contrapositive: a spectral gap forces a large residual -/

/-- **Spectral-gap lower bound on the residual.** If `lam` is strictly more than
`ε` away from *every* eigenvalue, then no unit vector can have residual `≤ ε`:
the residual is bounded below by the distance from `lam` to the spectrum. This is
the contrapositive of `residual_eigenvalue_bound`. -/
theorem residual_gt_of_spectral_gap {n : ℕ} (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (x : E) (hx : ‖x‖ = 1) (lam ε : ℝ)
    (hgap : ∀ i, ε < |μ i - lam|) :
    ε < ‖T x - (lam : 𝕜) • x‖ := by
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := residual_eigenvalue_bound T b μ hbT x hx lam ε h
  exact absurd hk (not_le.mpr (hgap k))

/-! ## Sanity check: an exact eigenpair has zero residual and the bound is sharp -/

/-- For an eigenvector `x = b j` the residual is `0`, and the bound is attained:
`|μ j − μ j| = 0 ≤ 0`. -/
example {n : ℕ} (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (j : Fin n) :
    ∃ k, |μ k - μ j| ≤ ‖T (b j) - ((μ j : ℝ) : 𝕜) • b j‖ :=
  dist_to_spectrum_le_residual T b μ hbT (b j) (b.orthonormal.1 j) (μ j)

end CauchyInterlacing.Residual
