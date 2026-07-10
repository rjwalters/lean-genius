import Mathlib
import Proofs.CauchyInterlacingAssembly

/-
# Cauchy interlacing — the self-contained compression corollary

`CauchyInterlacingAssembly.lean` (#27236, 0-sorry/0-axiom) proves the abstract
interlacing inequalities

  `lam k.succ ≤ mu k ≤ lam k.castSucc`

but it takes the *compression operator* `TH` on the codimension-one subspace
`H`, its spectral data (`bH`, `mu`, `hTH`, `hmu`), and the Rayleigh-agreement
hypothesis `hRayleigh` as **inputs**. That keeps the assembly purely
order-theoretic, but it leaves a real gap: a reader still has to construct the
compression and discharge `hRayleigh` by hand.

This file closes that gap. Given only

* a symmetric operator `T` on a finite-dimensional inner product space `V` of
  dimension `n + 1`, and
* a subspace `H ≤ V` of dimension `n`,

we **build** the orthogonal compression

  `compress T H := P_H ∘ T ∘ ι_H : H →ₗ[𝕜] H`,

prove it is symmetric, pull its spectral data straight from Mathlib's
`LinearMap.IsSymmetric` spectral theorem (`eigenvectorBasis` / `eigenvalues` /
`eigenvalues_antitone`), discharge the Rayleigh-agreement hypothesis from the
adjoint identity for the orthogonal projection, and feed everything into
`cauchy_interlacing`.

The result, `cauchy_interlacing_compression`, is the textbook statement with no
side conditions beyond "`T` is symmetric and `H` is a hyperplane":

  the descending eigenvalues `μ` of the compression of `T` to `H` interlace the
  descending eigenvalues `λ` of `T`:  `λ_{k+1} ≤ μ_k ≤ λ_k`.

## The compression's Rayleigh quotient

The single fact that powers both the symmetry of `compress` and the
Rayleigh-agreement hypothesis is the orthogonal-projection adjoint identity
`Submodule.inner_orthogonalProjection_eq_of_mem_right`:

  `⟪P_H v, u⟫ = ⟪v, u⟫`  for `u ∈ H`.

With `v = T ↑y` and `u = y` this gives `⟪compress y, y⟫_H = ⟪T ↑y, ↑y⟫_V`, and
since the subspace norm satisfies `‖y‖ = ‖↑y‖` (`Submodule.coe_norm`) the two
Rayleigh quotients coincide exactly.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open CauchyInterlacing.Assembly

namespace CauchyInterlacing.Compression

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- The orthogonal **compression** of `T` to a subspace `H`: project `T ↑y` back
into `H`.  For a Hermitian matrix and a coordinate hyperplane this is exactly the
principal submatrix obtained by deleting a row and column. -/
noncomputable def compress (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) : H →ₗ[𝕜] H :=
  (H.orthogonalProjection : V →L[𝕜] H).toLinearMap ∘ₗ (T ∘ₗ H.subtype)

@[simp] theorem compress_apply (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y : H) :
    compress T H y = H.orthogonalProjection (T (y : V)) := rfl

/-- **Projection-adjoint identity for the compression (unconditional, left slot).**
For *any* operator `T`, *any* subspace `H`, and *any* `y z : H`, the compression's inner
product agrees with the ambient one in the left slot:

  `⟪compress T H y, z⟫_H = ⟪T ↑y, ↑z⟫_V`.

No symmetry of `T` and no invariance / special-position hypothesis on `H` is required: the
orthogonal projection in `compress` is adjoint to the inclusion
(`Submodule.inner_orthogonalProjection_eq_of_mem_right`), so it is inert against the in-`H`
test vector `z`.  This is the single unconditional primitive behind both
`isSymmetric_compress` and `rayleigh_compress_eq`, and the bilinear generalisation of the
latter (the Rayleigh quotient is its diagonal `z = y` real part). -/
theorem inner_compress_eq (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y z : H) :
    @inner 𝕜 H _ (compress T H y) z = @inner 𝕜 V _ (T (y : V)) (z : V) := by
  rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]

/-- **Projection-adjoint identity for the compression (unconditional, right slot).**
The right-slot companion of `inner_compress_eq`:

  `⟪y, compress T H z⟫_H = ⟪↑y, T ↑z⟫_V`  for any `T`, any subspace `H`, any `y z : H`.

Same reasoning via `Submodule.inner_orthogonalProjection_eq_of_mem_left`.  Together with
`inner_compress_eq` this is the full unconditional two-sided adjoint identity for the
orthogonal compression; `isSymmetric_compress` is their combination when `T` is symmetric. -/
theorem inner_compress_eq' (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y z : H) :
    @inner 𝕜 H _ y (compress T H z) = @inner 𝕜 V _ (y : V) (T (z : V)) := by
  rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_left]

/-- The compression of a symmetric operator is symmetric.  Both inner products
collapse to `⟪T ↑y, ↑z⟫_V` via the projection adjoint identity, and that is
symmetric because `T` is. -/
theorem isSymmetric_compress {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric)
    (H : Submodule 𝕜 V) : (compress T H).IsSymmetric := by
  intro y z
  -- `⟪compress y, z⟫_H = ⟪T ↑y, ↑z⟫_V` and `⟪y, compress z⟫_H = ⟪↑y, T ↑z⟫_V`.
  have hl : @inner 𝕜 H _ (compress T H y) z = @inner 𝕜 V _ (T (y : V)) (z : V) := by
    rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]
  have hr : @inner 𝕜 H _ y (compress T H z) = @inner 𝕜 V _ (y : V) (T (z : V)) := by
    rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_left]
  show @inner 𝕜 H _ (compress T H y) z = @inner 𝕜 H _ y (compress T H z)
  rw [hl, hr]
  exact hT (y : V) (z : V)

/-- Rayleigh-quotient agreement: on every nonzero `y ∈ H`, the compression has
the same Rayleigh quotient as `T`.  This is the defining property of the
orthogonal compression and is precisely the hypothesis `cauchy_interlacing`
needs. -/
theorem rayleigh_compress_eq (T : V →ₗ[𝕜] V) (H : Submodule 𝕜 V) (y : H) :
    RCLike.re (@inner 𝕜 H _ (compress T H y) y) / ‖y‖ ^ 2
      = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 := by
  have hi : @inner 𝕜 H _ (compress T H y) y = @inner 𝕜 V _ (T (y : V)) (y : V) := by
    rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]
  rw [hi, Submodule.coe_norm]

/-- **Cauchy interlacing (compression corollary).**

Let `T` be a symmetric operator on an `(n+1)`-dimensional inner product space
`V`, with descending eigenvalues `lam := hT.eigenvalues`.  Let `H ≤ V` be a
codimension-one subspace (`finrank H = n`), and let `mu` be the descending
eigenvalues of the orthogonal compression `compress T H` of `T` to `H`.

Then for every `k : Fin n`:

  `lam k.succ ≤ mu k`  and  `mu k ≤ lam k.castSucc`,

i.e. `λ_{k+1} ≤ μ_k ≤ λ_k` in descending notation (`λ_k ≤ μ_k ≤ λ_{k+1}`
ascending).  No Rayleigh hypothesis is required: it is discharged internally
from the orthogonal-projection adjoint identity. -/
theorem cauchy_interlacing_compression
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + 1)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (hT.eigenvalues hVdim) k.succ ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
      ∧ (isSymmetric_compress hT H).eigenvalues hHdim k
          ≤ (hT.eigenvalues hVdim) k.castSucc := by
  -- Spectral data for `T` on `V`.
  set b := hT.eigenvectorBasis hVdim with hb_def
  set lam := hT.eigenvalues hVdim with hlam_def
  have hb : ∀ i, T (b i) = (lam i : 𝕜) • b i := hT.apply_eigenvectorBasis hVdim
  have hlam : Antitone lam := hT.eigenvalues_antitone hVdim
  -- Spectral data for the compression `TH` on `H`.
  set hTH := isSymmetric_compress hT H with hTH_def
  set bH := hTH.eigenvectorBasis hHdim with hbH_def
  set mu := hTH.eigenvalues hHdim with hmu_def
  have hbH : ∀ i, compress T H (bH i) = (mu i : 𝕜) • bH i := hTH.apply_eigenvectorBasis hHdim
  have hmu : Antitone mu := hTH.eigenvalues_antitone hHdim
  -- Rayleigh agreement, in the exact shape `cauchy_interlacing` wants.
  have hRayleigh : ∀ y : H, y ≠ 0 →
      RCLike.re (@inner 𝕜 H _ (compress T H y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 :=
    fun y _ => rayleigh_compress_eq T H y
  exact cauchy_interlacing T b lam hb hlam H hHdim (compress T H) bH mu hbH hmu hRayleigh k

end CauchyInterlacing.Compression
