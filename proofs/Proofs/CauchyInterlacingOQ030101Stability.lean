import Mathlib
import Proofs.CauchyInterlacingWeyl

/-
# Weyl's eigenvalue stability bound `|μ(k) − ν(k)| ≤ ‖T − U‖`

This file derives the **operator-norm eigenvalue stability** (Weyl perturbation /
Lipschitz) theorem for symmetric operators as a corollary of the Weyl
*monotonicity* theorem `weyl_monotone` proved in `CauchyInterlacingWeyl.lean`
(itself a corollary of the Courant–Fischer keystone, #25063, 0-sorry/0-axiom).
No new spectral theory is introduced; the only new analytic input is the
elementary Rayleigh bound `re⟪(A − B)x, x⟫ ≤ ‖A − B‖ · ‖x‖²` coming from
Cauchy–Schwarz and the operator-norm inequality `‖(A − B)x‖ ≤ ‖A − B‖ · ‖x‖`.

This answers the lead open question of the parent entry
`cauchy-interlacing-theorem-oq-03`: *"Derive the operator-norm stability bound
`|μ(k) − ν(k)| ≤ ‖T − U‖` from weyl_monotone by sandwiching T between
`U − ‖T−U‖·I` and `U + ‖T−U‖·I` (Loewner)."*

## The sandwich argument

Write `δ := ‖T − U‖` and `E := T − U`. For every `x`,
`re⟪E x, x⟫ ≤ ‖E x‖ · ‖x‖ ≤ ‖E‖ · ‖x‖² = δ · ‖x‖²` (and symmetrically for
`U − T`, using `‖U − T‖ = ‖T − U‖`). Hence in the Loewner order

  `U − δ·I  ⪯  T  ⪯  U + δ·I`.

The operators `U ± δ·I` share `U`'s eigenbasis with eigenvalues `ν ± δ` (a real
shift preserves the antitone ordering). Feeding the two Loewner inequalities into
`weyl_monotone` gives

  `μ(k) ≤ ν(k) + δ`   and   `ν(k) − δ ≤ μ(k)`,

i.e. `|μ(k) − ν(k)| ≤ δ = ‖T − U‖`.

Operators are presented as **continuous** linear maps `T U : E →L[𝕜] E` so that
`‖T − U‖` is the genuine operator norm; the spectral presentation (orthonormal
eigenbasis + antitone eigenvalue enumeration) is taken as input exactly as in the
parent keystone.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open InnerProductSpace

namespace CauchyInterlacing.Stability

open CauchyInterlacing.Weyl

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## The elementary Rayleigh / operator-norm bound -/

/-- **Operator-norm Rayleigh bound.** For continuous operators `A`, `B`, the real
Rayleigh quotient of the difference is controlled by the operator norm:
`re⟪(A − B)x, x⟫ ≤ ‖A − B‖ · ‖x‖²`. Proof: Cauchy–Schwarz
(`re_inner_le_norm`) followed by the operator-norm bound
`‖(A − B)x‖ ≤ ‖A − B‖ · ‖x‖`. -/
theorem reInner_diff_le (A B : E →L[𝕜] E) (x : E) :
    RCLike.re (@inner 𝕜 E _ (A x - B x) x) ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
  have h1 : RCLike.re (@inner 𝕜 E _ (A x - B x) x) ≤ ‖A x - B x‖ * ‖x‖ :=
    re_inner_le_norm (A x - B x) x
  have h2 : A x - B x = (A - B) x := (ContinuousLinearMap.sub_apply A B x).symm
  have h3 : ‖(A - B) x‖ ≤ ‖A - B‖ * ‖x‖ := (A - B).le_opNorm x
  calc RCLike.re (@inner 𝕜 E _ (A x - B x) x)
        ≤ ‖A x - B x‖ * ‖x‖ := h1
    _ = ‖(A - B) x‖ * ‖x‖ := by rw [h2]
    _ ≤ (‖A - B‖ * ‖x‖) * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg x)
    _ = ‖A - B‖ * ‖x‖ ^ 2 := by ring

/-! ## Algebra of the scalar shift `V + s·I` -/

/-- The real Rayleigh quotient of a scalar-shifted operator: `re⟪(V + s·I)x, x⟫`
splits as `re⟪V x, x⟫ + s · ‖x‖²`. -/
theorem reInner_add_smul (s : ℝ) (V : E →ₗ[𝕜] E) (x : E) :
    RCLike.re (@inner 𝕜 E _ ((V + (s : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) x) x)
      = RCLike.re (@inner 𝕜 E _ (V x) x) + s * ‖x‖ ^ 2 := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_add_left, map_add,
    inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The scalar shift `V + s·I` acts on an eigenvector `e i` (eigenvalue `lam i`)
with the shifted eigenvalue `lam i + s`. -/
theorem shift_eigen (s : ℝ) (V : E →ₗ[𝕜] E) {n : ℕ} (e : OrthonormalBasis (Fin n) 𝕜 E)
    (lam : Fin n → ℝ) (hV : ∀ i, V (e i) = (lam i : 𝕜) • e i) (i : Fin n) :
    (V + (s : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) (e i) = ((lam i + s : ℝ) : 𝕜) • e i := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hV i]
  push_cast
  rw [← add_smul]

/-! ## The eigenvalue stability theorem -/

/-- **Weyl's eigenvalue stability bound.** Let `T`, `U` be continuous operators on
a finite-dimensional inner product space, each presented by an orthonormal
eigenbasis (`b`, `c`) and an antitone (descending) eigenvalue enumeration
(`μ`, `ν`). Then the eigenvalues are `1`-Lipschitz in the operator norm:

`|μ(k) − ν(k)| ≤ ‖T − U‖`  for every index `k`.

This is the classical Weyl perturbation theorem `|λ_k(A) − λ_k(B)| ≤ ‖A − B‖`,
obtained here purely from `weyl_monotone` by the Loewner sandwich
`U − ‖T−U‖·I ⪯ T ⪯ U + ‖T−U‖·I`. -/
theorem weyl_eigenvalue_stability
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T U : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ)
    (c : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ)
    (hcU : ∀ i, U (c i) = (ν i : 𝕜) • c i) (hν : Antitone ν)
    (k : Fin n) :
    |μ k - ν k| ≤ ‖T - U‖ := by
  set δ : ℝ := ‖T - U‖ with hδ
  -- the eigen-presentations carried over to the LinearMap coercions
  have hbT' : ∀ i, (T : E →ₗ[𝕜] E) (b i) = (μ i : 𝕜) • b i := hbT
  have hcU' : ∀ i, (U : E →ₗ[𝕜] E) (c i) = (ν i : 𝕜) • c i := hcU
  -- STEP 1: `T ⪯ U + δ·I`, giving `μ k ≤ ν k + δ`
  have hle1 : ∀ x : E, RCLike.re (@inner 𝕜 E _ ((T : E →ₗ[𝕜] E) x) x)
      ≤ RCLike.re (@inner 𝕜 E _ (((U : E →ₗ[𝕜] E) + (δ : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) x) x) := by
    intro x
    rw [reInner_add_smul]
    have hb := reInner_diff_le T U x
    have hsplit : RCLike.re (@inner 𝕜 E _ (T x - U x) x)
        = RCLike.re (@inner 𝕜 E _ (T x) x) - RCLike.re (@inner 𝕜 E _ (U x) x) := by
      rw [inner_sub_left, map_sub]
    rw [hsplit] at hb
    simp only [ContinuousLinearMap.coe_coe]
    linarith
  have h1 : μ k ≤ ν k + δ :=
    weyl_monotone (T : E →ₗ[𝕜] E) ((U : E →ₗ[𝕜] E) + (δ : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E))
      b μ hbT' hμ c (fun i => ν i + δ)
      (fun i => shift_eigen δ (U : E →ₗ[𝕜] E) c ν hcU' i) (hν.add_const δ) hle1 k
  -- STEP 2: `U − δ·I ⪯ T`, giving `ν k − δ ≤ μ k`
  have hle2 : ∀ x : E,
      RCLike.re (@inner 𝕜 E _ (((U : E →ₗ[𝕜] E) + ((-δ : ℝ) : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) x) x)
        ≤ RCLike.re (@inner 𝕜 E _ ((T : E →ₗ[𝕜] E) x) x) := by
    intro x
    rw [reInner_add_smul]
    have hb := reInner_diff_le U T x
    rw [norm_sub_rev] at hb
    have hsplit : RCLike.re (@inner 𝕜 E _ (U x - T x) x)
        = RCLike.re (@inner 𝕜 E _ (U x) x) - RCLike.re (@inner 𝕜 E _ (T x) x) := by
      rw [inner_sub_left, map_sub]
    rw [hsplit] at hb
    simp only [ContinuousLinearMap.coe_coe]
    linarith
  have h2 : ν k + (-δ) ≤ μ k :=
    weyl_monotone ((U : E →ₗ[𝕜] E) + ((-δ : ℝ) : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) (T : E →ₗ[𝕜] E)
      c (fun i => ν i + (-δ))
      (fun i => shift_eigen (-δ) (U : E →ₗ[𝕜] E) c ν hcU' i) (hν.add_const (-δ))
      b μ hbT' hμ hle2 k
  -- combine the two one-sided bounds
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ## Sanity check: the bound is non-vacuous and sharp at `T = U` -/

/-- At `T = U` the eigenvalues coincide pointwise and the bound reads `0 ≤ 0`. -/
example [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →L[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ) (k : Fin n) :
    |μ k - μ k| ≤ ‖T - T‖ := weyl_eigenvalue_stability T T b μ hbT hμ b μ hbT hμ k

end CauchyInterlacing.Stability
