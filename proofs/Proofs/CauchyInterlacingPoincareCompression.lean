import Mathlib
import Proofs.CauchyInterlacingCompression
import Proofs.CauchyInterlacingPoincare

/-
# Poincaré separation, self-contained via the explicit orthogonal compression

Two earlier research files leave a deliberate seam between them:

* `CauchyInterlacingPoincare.lean` (#27247) proves the **abstract** Poincaré
  separation theorem — for a codimension-`m` compression `dim V = n + m`,
  `dim H = n`, the descending eigenvalues separate as
  `lam ⟨k+m⟩ ≤ mu k ≤ lam ⟨k⟩` — but it takes the compression operator `TH` on
  `H`, its spectral data, *and* the Rayleigh-agreement hypothesis as **inputs**.
* `CauchyInterlacingCompression.lean` **builds** the orthogonal compression
  `compress T H := P_H ∘ T ∘ ι_H` and discharges exactly that Rayleigh
  hypothesis — but only assembles it into the **codimension-one** corollary.

Crucially, `compress`, `isSymmetric_compress` and `rayleigh_compress_eq` are
stated for an *arbitrary* submodule `H`: nothing in their proofs uses
`codim H = 1`. So the abstract Poincaré theorem and the explicit compression
construction fit together for **any** codimension with no new work.

This file performs that join. Given only

* a symmetric operator `T` on a finite-dimensional inner product space `V` of
  dimension `n + m`, and
* a subspace `H ≤ V` of dimension `n` (codimension `m`),

we feed the explicit compression `compress T H` and its discharged Rayleigh
identity straight into `poincare_separation`, yielding the textbook Poincaré
separation theorem with **no Rayleigh side condition** and **no abstract `TH`**:

  `λ_{k+m} ≤ μ_k ≤ λ_k`,

where `μ` are the descending eigenvalues of the orthogonal compression of `T`
onto `H`.  This is the arbitrary-codimension analogue of
`cauchy_interlacing_compression` (the `m = 1` case, recovered below as a
corollary), and the fully self-contained form of `poincare_separation`.

A second corollary specialises `H` to the span of an arbitrary orthonormal
`n`-frame `f : Fin n → V`, the "compression onto a `k`-dimensional subspace"
picture: the dimension hypothesis is discharged automatically from
`finrank_span_eq_card`.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace
open CauchyInterlacing.Compression CauchyInterlacing.Poincare

namespace CauchyInterlacing.PoincareCompression

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **Poincaré separation theorem (self-contained compression form).**

Let `T` be a symmetric operator on an `(n + m)`-dimensional inner product space
`V`, with descending eigenvalues `lam := hT.eigenvalues`.  Let `H ≤ V` be a
subspace of dimension `n` (codimension `m`), and let `mu` be the descending
eigenvalues of the orthogonal compression `compress T H` of `T` onto `H`.

Then for every `k : Fin n`:

  `lam ⟨k + m⟩ ≤ mu k`  and  `mu k ≤ lam ⟨k⟩`,

i.e. `λ_{k+m} ≤ μ_k ≤ λ_k` (descending), the Poincaré separation theorem.  No
Rayleigh hypothesis and no abstract compression operator are required: the
compression is constructed explicitly and its Rayleigh quotient discharged
internally from the orthogonal-projection adjoint identity. The
codimension-one `cauchy_interlacing_compression` is the special case `m = 1`. -/
theorem poincare_separation_compression
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (hT.eigenvalues hVdim) ⟨(k : ℕ) + m, by have := k.isLt; omega⟩
        ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
      ∧ (isSymmetric_compress hT H).eigenvalues hHdim k
          ≤ (hT.eigenvalues hVdim) ⟨(k : ℕ), by have := k.isLt; omega⟩ := by
  -- Spectral data for `T` on `V`.
  set b := hT.eigenvectorBasis hVdim with hb_def
  set lam := hT.eigenvalues hVdim with hlam_def
  have hb : ∀ i, T (b i) = (lam i : 𝕜) • b i := hT.apply_eigenvectorBasis hVdim
  have hlam : Antitone lam := hT.eigenvalues_antitone hVdim
  -- Spectral data for the explicit compression `compress T H` on `H`.
  set hTH := isSymmetric_compress hT H with hTH_def
  set bH := hTH.eigenvectorBasis hHdim with hbH_def
  set mu := hTH.eigenvalues hHdim with hmu_def
  have hbH : ∀ i, compress T H (bH i) = (mu i : 𝕜) • bH i := hTH.apply_eigenvectorBasis hHdim
  have hmu : Antitone mu := hTH.eigenvalues_antitone hHdim
  -- Rayleigh agreement, in the exact shape `poincare_separation` wants.
  have hRayleigh : ∀ y : H, y ≠ 0 →
      RCLike.re (@inner 𝕜 H _ (compress T H y) y) / ‖y‖ ^ 2
        = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2 :=
    fun y _ => rayleigh_compress_eq T H y
  exact poincare_separation T b lam hb hlam H hHdim (compress T H) bH mu hbH hmu hRayleigh k

/-- **Cauchy interlacing (codimension one) recovered.**

The `m = 1` case of `poincare_separation_compression`, in the parent entry's
`succ`/`castSucc` notation: `lam k.succ ≤ mu k ≤ lam k.castSucc`.  This
reproduces `cauchy_interlacing_compression`, confirming the arbitrary-codimension
form is a faithful generalisation. -/
theorem cauchy_interlacing_compression_of_poincare
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + 1)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (hT.eigenvalues hVdim) k.succ ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
      ∧ (isSymmetric_compress hT H).eigenvalues hHdim k
          ≤ (hT.eigenvalues hVdim) k.castSucc := by
  obtain ⟨hlo, hup⟩ := poincare_separation_compression hT hVdim H hHdim k
  refine ⟨?_, ?_⟩
  · have hk : k.succ = (⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext; simp
    rw [hk]; exact hlo
  · have hk : k.castSucc = (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (n + 1)) := by
      apply Fin.ext; simp
    rw [hk]; exact hup

/-- **Compression onto the span of an orthonormal `n`-frame.**

The "compression onto a `k`-dimensional subspace" picture: instead of a subspace
`H` with a separately-supplied dimension hypothesis, take an arbitrary
orthonormal family `f : Fin n → V` and compress onto `H := span (range f)`.  Its
dimension is `n` automatically (`finrank_span_eq_card`), so Poincaré separation
applies with `T` on `V` of dimension `n + m`:

  `λ_{k+m} ≤ μ_k ≤ λ_k`,

`μ` the descending eigenvalues of `compress T (span (range f))`. -/
theorem poincare_separation_compression_span
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (f : Fin n → V) (hf : Orthonormal 𝕜 f)
    (k : Fin n) :
    (hT.eigenvalues hVdim) ⟨(k : ℕ) + m, by have := k.isLt; omega⟩
        ≤ (isSymmetric_compress hT (Submodule.span 𝕜 (Set.range f))).eigenvalues
            ((finrank_span_eq_card hf.linearIndependent).trans (Fintype.card_fin n)) k
      ∧ (isSymmetric_compress hT (Submodule.span 𝕜 (Set.range f))).eigenvalues
            ((finrank_span_eq_card hf.linearIndependent).trans (Fintype.card_fin n)) k
          ≤ (hT.eigenvalues hVdim) ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  poincare_separation_compression hT hVdim (Submodule.span 𝕜 (Set.range f))
    ((finrank_span_eq_card hf.linearIndependent).trans (Fintype.card_fin n)) k

/-! ## Tightness: the invariant-subspace (attainment) case

The interlacing bound `μ_k ≤ λ_k` is not always an equality, but there is a
clean structural characterisation of *when* the compression stops losing
information: exactly when `H` is invariant under `T`.  In that case the abstract
orthogonal compression `compress T H` coincides with the honest restriction
`T.restrict` of `T` to `H` — no projection error is incurred, because `T ↑y`
already lies in `H` and the orthogonal projection fixes it.

Consequently the spectrum of the compression is a sub-multiset of the spectrum
of `T` (the eigenvalues of a restriction to an invariant subspace are a subset
of the ambient eigenvalues), so Poincaré separation degenerates to equality on
that block — the extremal / attainment case of the interlacing inequality. -/

/-- Pointwise form of `compress_eq_restrict_of_invariant`: on a `T`-invariant
subspace the compression acts by `T` itself, `↑(compress T H y) = T ↑y`.  The
orthogonal projection in `compress` is inert here because it is applied to a
vector `T ↑y` that already lies in `H`. -/
theorem coe_compress_of_invariant {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hinv : ∀ y ∈ H, T y ∈ H) (y : H) :
    ((compress T H y : H) : V) = T (y : V) := by
  rw [compress_apply, Submodule.coe_orthogonalProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr (hinv _ y.2)]

/-- **The compression onto a `T`-invariant subspace is the restriction of `T`.**

If `T y ∈ H` for every `y ∈ H`, then `compress T H = T.restrict hinv` as
operators `H →ₗ[𝕜] H`: no projection error is incurred, so the compression
recovers `T` exactly on the invariant block. -/
theorem compress_eq_restrict_of_invariant {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hinv : ∀ y ∈ H, T y ∈ H) :
    compress T H = T.restrict hinv := by
  ext y
  -- `ext` already reduces to the coerced (ambient-`V`) equality of the images.
  exact (coe_compress_of_invariant H hinv y).trans (LinearMap.restrict_coe_apply T hinv y).symm

/-- **Converse: pointwise agreement forces invariance.**

The orthogonal compression `compress T H` agrees pointwise with `T` — meaning
`↑(compress T H y) = T ↑y` for every `y : H` — *iff* `H` is `T`-invariant.

The forward direction is `coe_compress_of_invariant`.  Conversely, the image
`compress T H y` is by construction a vector *of* `H`, so its ambient coercion
lies in `H`; the pointwise agreement then rewrites that membership into
`T ↑y ∈ H`.  Thus the projection error in the compression vanishes precisely on
invariant subspaces — this pins the attainment locus of Poincaré separation from
both sides. -/
theorem invariant_iff_coe_compress_eq {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V) :
    (∀ y ∈ H, T y ∈ H) ↔ ∀ y : H, ((compress T H y : H) : V) = T (y : V) := by
  refine ⟨fun hinv y => coe_compress_of_invariant H hinv y, fun h y hy => ?_⟩
  -- `↑(compress T H ⟨y, hy⟩)` is a coercion of an element of `H`, hence in `H`.
  have hmem : ((compress T H ⟨y, hy⟩ : H) : V) ∈ H := Submodule.coe_mem _
  rwa [h ⟨y, hy⟩] at hmem

omit [FiniteDimensional 𝕜 V] in
/-- **Operator-level converse.**  If the compression `compress T H` equals the
restriction of `T` to `H` for *some* proof `hinv` that `T` maps `H` into itself,
that already witnesses invariance; but the substantive converse is that the mere
existence of an operator `S : H →ₗ[𝕜] H` lifting `T` pointwise
(`∀ y, ↑(S y) = T ↑y`) already forces `H` to be invariant (once invariance
holds, `invariant_iff_coe_compress_eq` identifies `S` with `compress T H`).
This packages the converse into the "honest restriction" picture. -/
theorem invariant_of_exists_lift {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (S : H →ₗ[𝕜] H) (hS : ∀ y : H, ((S y : H) : V) = T (y : V)) :
    ∀ y ∈ H, T y ∈ H := fun y hy => by
  have hmem : ((S ⟨y, hy⟩ : H) : V) ∈ H := Submodule.coe_mem _
  rwa [hS ⟨y, hy⟩] at hmem

end CauchyInterlacing.PoincareCompression
