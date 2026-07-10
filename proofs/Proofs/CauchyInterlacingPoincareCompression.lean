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

/-- **Spectrum inclusion on an invariant subspace (attainment case).**

If `H` is `T`-invariant, every eigenvalue of the orthogonal compression
`compress T H` is an eigenvalue of the ambient operator `T`.  Concretely, the
`k`-th descending eigenvalue `μ_k := (isSymmetric_compress hT H).eigenvalues hHdim k`
of the compression satisfies `Module.End.HasEigenvalue T μ_k`, realised by the
included eigenvector `↑(bH k) ∈ V` (the compression's eigenvector viewed in the
ambient space).

This is the pointwise form of the sub-multiset relationship in the attainment
(invariant-subspace) case: on an invariant `H` the compression coincides with
the honest restriction `T.restrict` (`compress_eq_restrict_of_invariant`), so it
loses no spectral information and its spectrum `{μ_k}` is contained in the
spectrum of `T`.  The Poincaré interlacing bound `μ_k ≤ λ_k` therefore
degenerates onto the ambient spectrum on such a block. -/
theorem hasEigenvalue_compress_eigenvalue_of_invariant
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n : ℕ}
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (hinv : ∀ y ∈ H, T y ∈ H) (k : Fin n) :
    Module.End.HasEigenvalue T
      (((isSymmetric_compress hT H).eigenvalues hHdim k : 𝕜)) := by
  set hTH := isSymmetric_compress hT H with hTH_def
  set bH := hTH.eigenvectorBasis hHdim with hbH_def
  set mu := hTH.eigenvalues hHdim with hmu_def
  -- The compression acts diagonally on its own eigenvector basis.
  have hcomp : compress T H (bH k) = (mu k : 𝕜) • bH k :=
    hTH.apply_eigenvectorBasis hHdim k
  -- Transport to `V` via invariance: `↑(compress T H y) = T ↑y`.
  have hcoe : T ((bH k : V)) = (mu k : 𝕜) • ((bH k : V)) := by
    have e1 := coe_compress_of_invariant H hinv (bH k)
    rw [hcomp] at e1
    simpa using e1.symm
  -- The included eigenvector is nonzero (a unit vector of an orthonormal basis).
  have hne : (bH k : V) ≠ 0 := by
    rw [Ne, Submodule.coe_eq_zero]
    exact bH.orthonormal.ne_zero k
  -- Assemble the eigenvector, then the eigenvalue.
  have hev : Module.End.HasEigenvector T ((mu k : 𝕜)) ((bH k : V)) :=
    ⟨Module.End.mem_eigenspace_iff.mpr hcoe, hne⟩
  exact Module.End.hasEigenvalue_of_hasEigenvector hev

/-- **Full spectrum inclusion on an invariant subspace (no symmetry needed).**

If `H` is `T`-invariant, then *every* eigenvalue of the orthogonal compression
`compress T H` (viewed as an operator on `H`) is an eigenvalue of the ambient
`T`.  Unlike `hasEigenvalue_compress_eigenvalue_of_invariant`, this is stated for
an arbitrary eigenvalue `μ` and requires **no symmetry** of `T`: invariance alone
makes the projection error vanish (`coe_compress_of_invariant`), so any
compression-eigenvector `v : H` lifts to an ambient `T`-eigenvector `↑v ∈ V` for
the same `μ`.

This is the honest eigenvalue-level form of the attainment case: on an invariant
block the compression is the restriction `T.restrict`
(`compress_eq_restrict_of_invariant`), which loses no spectral information. -/
theorem hasEigenvalue_of_hasEigenvalue_compress_of_invariant
    {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H)
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue (compress T H) μ) :
    Module.End.HasEigenvalue T μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  -- `v : H` is a nonzero compression-eigenvector for `μ`.
  have hcv : compress T H v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hne : (v : V) ≠ 0 := by
    rw [Ne, Submodule.coe_eq_zero]; exact hv.2
  -- Transport to `V`: invariance makes `↑(compress T H v) = T ↑v`.
  have hcoe : T (v : V) = μ • (v : V) := by
    have h := coe_compress_of_invariant H hinv v
    rw [hcv] at h
    simpa using h.symm
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hcoe, hne⟩

/-- **Spectrum containment on an invariant subspace.**

Packaged as a set inclusion of spectra: on a `T`-invariant subspace `H` the
spectrum of the compression is contained in the spectrum of `T`,
`spectrum 𝕜 (compress T H) ⊆ spectrum 𝕜 T`.  In finite dimension the spectrum is
exactly the eigenvalue set (`Module.End.hasEigenvalue_iff_mem_spectrum`), so this
is the `spectrum`-level upgrade of
`hasEigenvalue_of_hasEigenvalue_compress_of_invariant`: the sub-multiset /
attainment statement promised by Poincaré separation on an invariant block,
again with no symmetry hypothesis on `T`. -/
theorem spectrum_compress_subset_of_invariant
    {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H) :
    spectrum 𝕜 (compress T H) ⊆ spectrum 𝕜 T := by
  intro μ hμ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ ⊢
  exact hasEigenvalue_of_hasEigenvalue_compress_of_invariant H hinv hμ

/-! ## Reducing subspaces: the spectrum splits as a union of compression spectra

`spectrum_compress_subset_of_invariant` gives the *one-sided* inclusion
`spectrum 𝕜 (compress T H) ⊆ spectrum 𝕜 T` on any invariant `H`.  The sharper
structural question is *when the ambient spectrum is recovered completely* from
compressions.  The clean answer: exactly when `H` **reduces** `T`, i.e. both `H`
and its orthogonal complement `Hᗮ` are `T`-invariant.  Then

  `spectrum 𝕜 T = spectrum 𝕜 (compress T H) ∪ spectrum 𝕜 (compress T Hᗮ)`,

the block-diagonal spectral decomposition: every eigenvalue of `T` is captured by
one of the two compression blocks, and nothing else appears — the two-block
*equality* (attainment) form of Poincaré separation on a reducing subspace, still
with **no symmetry hypothesis** on `T`.

The mechanism is a projection argument: an ambient eigenvector `v ≠ 0`,
`T v = μ • v`, splits as `v = a + (v - a)` with `a := P_H v ∈ H` and
`v - a ∈ Hᗮ`.  Feeding the split into the eigen-equation gives
`T a - μ • a = μ • (v - a) - T (v - a)`, whose left side lies in `H` (invariance
of `H`) and whose right side lies in `Hᗮ` (invariance of `Hᗮ`); as `H ⊓ Hᗮ = ⊥`,
both sides vanish, so `a` and `v - a` are themselves eigenvectors of `T` for `μ`.
Whichever is nonzero lies in an invariant block, so `μ` is an eigenvalue of that
block's compression (`compress T H = T.restrict` there,
`compress_eq_restrict_of_invariant`). -/

/-- **An ambient eigenvector inside an invariant subspace is a compression
eigenvector.**

If `H` is `T`-invariant and `w ∈ H` is a nonzero ambient eigenvector,
`T w = μ • w`, then `μ` is an eigenvalue of the orthogonal compression
`compress T H` (with eigenvector `⟨w, hwH⟩ : H`).  On the invariant block the
compression coincides with `T` on `H` (`coe_compress_of_invariant`), so the
eigen-equation transfers verbatim.  No symmetry of `T` is used. -/
theorem hasEigenvalue_compress_of_mem_of_invariant
    {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H)
    {μ : 𝕜} {w : V} (hwH : w ∈ H) (hw : w ≠ 0) (hTw : T w = μ • w) :
    Module.End.HasEigenvalue (compress T H) μ := by
  -- The compression acts by `T` on the invariant block, so it fixes `w`'s class.
  have hcoe : ((compress T H ⟨w, hwH⟩ : H) : V) = μ • w := by
    rw [coe_compress_of_invariant H hinv ⟨w, hwH⟩]; exact hTw
  have hev : compress T H ⟨w, hwH⟩ = μ • (⟨w, hwH⟩ : H) :=
    Subtype.ext (by rw [hcoe, Submodule.coe_smul])
  have hne : (⟨w, hwH⟩ : H) ≠ 0 := by
    simp only [Ne, Submodule.mk_eq_zero]; exact hw
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hev, hne⟩

/-- **Projection of an eigenvector across a reducing pair (the core mechanism).**

If `H` reduces `T` (both `H` and `Hᗮ` are `T`-invariant) and `T v = μ • v`, then
the two orthogonal components `a := P_H v ∈ H` and `v - a ∈ Hᗮ` are *themselves*
eigenvectors of `T` for the same `μ`:

  `T (P_H v) = μ • P_H v`  and  `T (v - P_H v) = μ • (v - P_H v)`.

Proof (symmetry-free): the eigen-equation `T v = μ • v` rearranges to
`T a - μ • a = μ • (v - a) - T (v - a)`.  The left side lies in `H` (invariance of
`H`), the right side lies in `Hᗮ` (invariance of `Hᗮ`); since `H ⊓ Hᗮ = ⊥`, both
vanish.  This is the projection argument underlying every reducing-subspace
statement below, factored out for reuse. -/
theorem starProjection_eigenvector_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    {μ : 𝕜} {v : V} (hTv : T v = μ • v) :
    T (H.starProjection v) = μ • H.starProjection v ∧
      T (v - H.starProjection v) = μ • (v - H.starProjection v) := by
  set a := H.starProjection v with ha_def
  have haH : a ∈ H := H.starProjection_apply_mem v
  have hbHp : v - a ∈ Hᗮ := H.sub_starProjection_mem_orthogonal v
  have hva : a + (v - a) = v := by abel
  have hsplit : T a - μ • a = μ • (v - a) - T (v - a) := by
    have key : T a + T (v - a) = μ • a + μ • (v - a) := by
      rw [← map_add, ← smul_add, hva, hTv]
    rw [sub_eq_sub_iff_add_eq_add, key]; abel
  have hmemH : T a - μ • a ∈ H := H.sub_mem (hH a haH) (H.smul_mem μ haH)
  have hmemHp : T a - μ • a ∈ Hᗮ := by
    rw [hsplit]; exact Hᗮ.sub_mem (Hᗮ.smul_mem μ hbHp) (hHp _ hbHp)
  have hzero : T a - μ • a = 0 := by
    have hmem : T a - μ • a ∈ H ⊓ Hᗮ := Submodule.mem_inf.mpr ⟨hmemH, hmemHp⟩
    rw [H.inf_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot 𝕜).mp hmem
  refine ⟨sub_eq_zero.mp hzero, ?_⟩
  have hz2 : μ • (v - a) - T (v - a) = 0 := by rw [← hsplit]; exact hzero
  exact (sub_eq_zero.mp hz2).symm

/-- **Every eigenvalue of `T` is captured by one compression block of a reducing
pair.**

If both `H` and its orthogonal complement `Hᗮ` are `T`-invariant (i.e. `H`
reduces `T`), then every eigenvalue `μ` of `T` is an eigenvalue of either
`compress T H` or `compress T Hᗮ`.

Proof: an eigenvector `v ≠ 0` (`T v = μ • v`) splits as `v = a + (v - a)` with
`a := P_H v ∈ H` and `v - a ∈ Hᗮ`.  The eigen-equation gives
`T a - μ • a = μ • (v - a) - T (v - a)`; the left side lies in `H`, the right side
in `Hᗮ`, and `H ⊓ Hᗮ = ⊥`, so both vanish — `a` and `v - a` are eigenvectors of
`T`.  Whichever is nonzero lies in an invariant block, and
`hasEigenvalue_compress_of_mem_of_invariant` promotes it to that block's
compression.  No symmetry of `T` is used. -/
theorem hasEigenvalue_compress_or_orthogonal_of_reducing
    {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue T μ) :
    Module.End.HasEigenvalue (compress T H) μ ∨
      Module.End.HasEigenvalue (compress T Hᗮ) μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hvne : v ≠ 0 := hv.2
  -- Orthogonal split `v = a + (v - a)`, `a ∈ H`, `v - a ∈ Hᗮ`; both are
  -- eigenvectors for `μ` by the reducing-pair projection mechanism.
  have haH : H.starProjection v ∈ H := H.starProjection_apply_mem v
  have hbHp : v - H.starProjection v ∈ Hᗮ := H.sub_starProjection_mem_orthogonal v
  obtain ⟨hTa, hTb⟩ := starProjection_eigenvector_of_reducing H hH hHp hTv
  -- At least one component is nonzero; feed it into the invariant block.
  by_cases hacase : H.starProjection v = 0
  · right
    have hb_ne : v - H.starProjection v ≠ 0 := by rw [hacase, sub_zero]; exact hvne
    exact hasEigenvalue_compress_of_mem_of_invariant Hᗮ hHp hbHp hb_ne hTb
  · left
    exact hasEigenvalue_compress_of_mem_of_invariant H hH haH hacase hTa

/-- **Spectral decomposition over a reducing subspace.**

If `H` reduces `T` — both `H` and `Hᗮ` are `T`-invariant — then the spectrum of
`T` is exactly the union of the spectra of the two orthogonal compressions:

  `spectrum 𝕜 T = spectrum 𝕜 (compress T H) ∪ spectrum 𝕜 (compress T Hᗮ)`.

The `⊇` inclusion is `spectrum_compress_subset_of_invariant` applied to each
block; the `⊆` inclusion is `hasEigenvalue_compress_or_orthogonal_of_reducing`.
This is the equality (two-block attainment) form of Poincaré separation on a
reducing subspace, again with **no symmetry hypothesis** on `T`. -/
theorem spectrum_eq_union_of_reducing
    {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    spectrum 𝕜 T = spectrum 𝕜 (compress T H) ∪ spectrum 𝕜 (compress T Hᗮ) := by
  apply Set.Subset.antisymm
  · intro μ hμ
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
    rcases hasEigenvalue_compress_or_orthogonal_of_reducing H hH hHp hμ with h | h
    · exact Set.mem_union_left _ (Module.End.hasEigenvalue_iff_mem_spectrum.mp h)
    · exact Set.mem_union_right _ (Module.End.hasEigenvalue_iff_mem_spectrum.mp h)
  · exact Set.union_subset
      (spectrum_compress_subset_of_invariant H hH)
      (spectrum_compress_subset_of_invariant Hᗮ hHp)

/-! ## Eigenspace decomposition over a reducing subspace (multiplicity bookkeeping)

`spectrum_eq_union_of_reducing` records that a reducing pair splits the ambient
spectrum as a *set* union.  The finer, multiplicity-aware statement is that each
individual eigenspace splits as an **internal orthogonal direct sum** of its two
blockwise pieces:

  `eigenspace T μ = (eigenspace T μ ⊓ H) ⊔ (eigenspace T μ ⊓ Hᗮ)`,

with the two summands disjoint (they live in `H` and `Hᗮ`, and `H ⊓ Hᗮ = ⊥`).
Taking dimensions turns this into the algebraic-multiplicity bookkeeping of the
block-diagonal picture:

  `dim (eigenspace T μ) = dim (eigenspace T μ ⊓ H) + dim (eigenspace T μ ⊓ Hᗮ)`.

The multiplicity of `μ` for `T` is exactly the sum of its multiplicities on the
two blocks — the eigenspace-level refinement of the spectrum union.  Everything
is symmetry-free, driven by `starProjection_eigenvector_of_reducing`. -/

omit [FiniteDimensional 𝕜 V] in
/-- The two blockwise pieces of an eigenspace over a reducing pair are disjoint:
`(eigenspace T μ ⊓ H) ⊓ (eigenspace T μ ⊓ Hᗮ) = ⊥`, because they sit inside `H`
and `Hᗮ` respectively and `H ⊓ Hᗮ = ⊥`.  (No invariance needed — this is purely
the orthogonality of `H` and `Hᗮ`.) -/
theorem eigenspace_inf_reducing_disjoint {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (μ : 𝕜) :
    (Module.End.eigenspace T μ ⊓ H) ⊓ (Module.End.eigenspace T μ ⊓ Hᗮ) = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc (Module.End.eigenspace T μ ⊓ H) ⊓ (Module.End.eigenspace T μ ⊓ Hᗮ)
      ≤ H ⊓ Hᗮ :=
        le_inf (le_trans inf_le_left inf_le_right)
          (le_trans inf_le_right inf_le_right)
    _ = ⊥ := H.inf_orthogonal_eq_bot

/-- **Eigenspace decomposition over a reducing subspace.**

If `H` reduces `T` — both `H` and `Hᗮ` are `T`-invariant — then for every `μ` the
`μ`-eigenspace of `T` is the internal direct sum of its `H`- and `Hᗮ`-parts:

  `eigenspace T μ = (eigenspace T μ ⊓ H) ⊔ (eigenspace T μ ⊓ Hᗮ)`.

The `⊇` inclusion is trivial (both summands are `≤ eigenspace T μ`); for `⊆`, an
eigenvector `v` splits as `v = P_H v + (v - P_H v)`, and
`starProjection_eigenvector_of_reducing` shows both pieces are again
`μ`-eigenvectors, lying in `H` and `Hᗮ` respectively.  Combined with
`eigenspace_inf_reducing_disjoint` this exhibits the eigenspace as an internal
*orthogonal* direct sum.  No symmetry of `T` is used. -/
theorem eigenspace_eq_sup_inf_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (μ : 𝕜) :
    Module.End.eigenspace T μ =
      (Module.End.eigenspace T μ ⊓ H) ⊔ (Module.End.eigenspace T μ ⊓ Hᗮ) := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_left inf_le_left)
  have hTv : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have haH : H.starProjection v ∈ H := H.starProjection_apply_mem v
  have hbHp : v - H.starProjection v ∈ Hᗮ := H.sub_starProjection_mem_orthogonal v
  obtain ⟨hTa, hTb⟩ := starProjection_eigenvector_of_reducing H hH hHp hTv
  have haE : H.starProjection v ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hTa
  have hbE : v - H.starProjection v ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hTb
  have hmem : H.starProjection v + (v - H.starProjection v) ∈
      (Module.End.eigenspace T μ ⊓ H) ⊔ (Module.End.eigenspace T μ ⊓ Hᗮ) :=
    Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨haE, haH⟩)
      (Submodule.mem_inf.mpr ⟨hbE, hbHp⟩)
  have hva : H.starProjection v + (v - H.starProjection v) = v := by abel
  rwa [hva] at hmem

/-- **Multiplicity additivity over a reducing subspace.**

The dimension form of `eigenspace_eq_sup_inf_of_reducing`: on a reducing pair the
algebraic multiplicity of each eigenvalue `μ` of `T` is the sum of its
multiplicities on the two orthogonal blocks,

  `dim (eigenspace T μ) = dim (eigenspace T μ ⊓ H) + dim (eigenspace T μ ⊓ Hᗮ)`.

Immediate from the internal-direct-sum decomposition
(`eigenspace_eq_sup_inf_of_reducing` for the `⊔`, `eigenspace_inf_reducing_disjoint`
for the `⊓ = ⊥`) via `Submodule.finrank_sup_add_finrank_inf_eq`.  This is the
multiplicity-level bookkeeping of the block-diagonal spectral decomposition. -/
theorem finrank_eigenspace_eq_add_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace T μ) =
      Module.finrank 𝕜 (Module.End.eigenspace T μ ⊓ H : Submodule 𝕜 V) +
        Module.finrank 𝕜 (Module.End.eigenspace T μ ⊓ Hᗮ : Submodule 𝕜 V) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Module.End.eigenspace T μ ⊓ H) (Module.End.eigenspace T μ ⊓ Hᗮ)
  rwa [eigenspace_inf_reducing_disjoint H μ, finrank_bot, add_zero,
    ← eigenspace_eq_sup_inf_of_reducing H hH hHp μ] at h

/-! ## Blockwise eigenspaces: exact multiplicity of a compression on an invariant block

The results above compare *ambient* eigenspaces (`eigenspace T μ ⊓ H` etc.).  The
final step identifies those pieces with the eigenspaces of the compression
operators themselves, turning the multiplicity bookkeeping into an honest
statement about `compress T H` as an operator on `H`.

On a `T`-invariant subspace `H`, the coercion `H → V` carries the `μ`-eigenspace
of the compression `compress T H` isomorphically onto `eigenspace T μ ⊓ H`: a
compression-eigenvector `v : H` lifts to the ambient `T`-eigenvector `↑v ∈ H`
(`coe_compress_of_invariant`), and conversely every ambient `μ`-eigenvector lying
in `H` is a compression-eigenvector (`compress T H = T` on the invariant block).
Taking dimensions gives the *exact* blockwise multiplicity, and combining the two
blocks of a reducing pair yields the with-multiplicity spectral decomposition:

  `dim (eigenspace T μ)
     = dim (eigenspace (compress T H) μ) + dim (eigenspace (compress T Hᗮ) μ)`,

the multiplicity-aware refinement of `spectrum_eq_union_of_reducing`.  Everything
remains symmetry-free. -/

/-- **The compression's `μ`-eigenspace maps onto `eigenspace T μ ⊓ H` on an
invariant block.**

If `H` is `T`-invariant, the coercion `H.subtype : H → V` sends the `μ`-eigenspace
of `compress T H` exactly onto `eigenspace T μ ⊓ H`:

  `(eigenspace (compress T H) μ).map H.subtype = eigenspace T μ ⊓ H`.

Forward: a compression-eigenvector `v` transports to `T ↑v = μ • ↑v` via
`coe_compress_of_invariant`, and `↑v ∈ H` automatically.  Backward: an ambient
`μ`-eigenvector `w ∈ H` gives `compress T H ⟨w,·⟩ = μ • ⟨w,·⟩`, again because the
compression acts by `T` on the invariant block.  No symmetry of `T` is used. -/
theorem map_eigenspace_compress_eq_inf_of_invariant {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H) (μ : 𝕜) :
    (Module.End.eigenspace (compress T H) μ).map H.subtype
      = Module.End.eigenspace T μ ⊓ H := by
  apply le_antisymm
  · rintro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hcv : compress T H v = μ • v := Module.End.mem_eigenspace_iff.mp hv
    have hcoe : T (v : V) = μ • (v : V) := by
      have h := coe_compress_of_invariant H hinv v
      rw [hcv] at h; simpa using h.symm
    exact Submodule.mem_inf.mpr ⟨Module.End.mem_eigenspace_iff.mpr hcoe, v.2⟩
  · intro w hw
    obtain ⟨hwE, hwH⟩ := Submodule.mem_inf.mp hw
    have hTw : T w = μ • w := Module.End.mem_eigenspace_iff.mp hwE
    have hcoe : ((compress T H ⟨w, hwH⟩ : H) : V) = μ • w := by
      rw [coe_compress_of_invariant H hinv ⟨w, hwH⟩]; exact hTw
    have hev : compress T H ⟨w, hwH⟩ = μ • (⟨w, hwH⟩ : H) :=
      Subtype.ext (by rw [hcoe, Submodule.coe_smul])
    exact Submodule.mem_map.mpr
      ⟨⟨w, hwH⟩, Module.End.mem_eigenspace_iff.mpr hev, rfl⟩

/-- **Exact blockwise multiplicity on an invariant subspace.**

On a `T`-invariant `H`, the algebraic multiplicity of `μ` for the compression
`compress T H` equals the dimension of the ambient eigenspace *intersected with
the block*:

  `dim (eigenspace (compress T H) μ) = dim (eigenspace T μ ⊓ H)`.

Immediate from `map_eigenspace_compress_eq_inf_of_invariant` via the injective
coercion `H.subtype` (`Submodule.equivMapOfInjective`), which is a linear
isomorphism onto its image. -/
theorem finrank_eigenspace_compress_eq_of_invariant {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace (compress T H) μ)
      = Module.finrank 𝕜 (Module.End.eigenspace T μ ⊓ H : Submodule 𝕜 V) := by
  have e := (Submodule.equivMapOfInjective H.subtype
    (LinearMap.ker_eq_bot.mp (Submodule.ker_subtype H))
    (Module.End.eigenspace (compress T H) μ)).finrank_eq
  rw [map_eigenspace_compress_eq_inf_of_invariant H hinv μ] at e
  exact e

/-- **Multiplicity monotonicity of a compression on an invariant subspace.**

The multiplicity-level refinement of `spectrum_compress_subset_of_invariant`: on a
`T`-invariant `H` the algebraic multiplicity of every `μ` for the compression is
bounded by its ambient multiplicity,

  `dim (eigenspace (compress T H) μ) ≤ dim (eigenspace T μ)`.

Combine `finrank_eigenspace_compress_eq_of_invariant` with the trivial inclusion
`eigenspace T μ ⊓ H ≤ eigenspace T μ`.  This is the honest "sub-multiset" form of
the spectrum inclusion — no eigenvalue's multiplicity can grow under compression
onto an invariant block. -/
theorem finrank_eigenspace_compress_le_of_invariant {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace (compress T H) μ)
      ≤ Module.finrank 𝕜 (Module.End.eigenspace T μ) := by
  rw [finrank_eigenspace_compress_eq_of_invariant H hinv μ]
  exact Submodule.finrank_mono inf_le_left

/-- **With-multiplicity spectral decomposition over a reducing subspace.**

The multiplicity-aware capstone: if `H` reduces `T` (both `H` and `Hᗮ` are
`T`-invariant), then for every `μ` the algebraic multiplicity of `μ` for `T` is
the *sum* of its multiplicities for the two compression blocks,

  `dim (eigenspace T μ)
     = dim (eigenspace (compress T H) μ) + dim (eigenspace (compress T Hᗮ) μ)`.

This is the eigenspace-level refinement of `spectrum_eq_union_of_reducing`: the
set-level union is upgraded to an exact multiplicity identity.  Immediate from
`finrank_eigenspace_eq_add_of_reducing` (multiplicity additivity over the ambient
blocks) rewritten through `finrank_eigenspace_compress_eq_of_invariant` on each
block.  Symmetry-free. -/
theorem finrank_eigenspace_eq_add_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace T μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (compress T H) μ) +
        Module.finrank 𝕜 (Module.End.eigenspace (compress T Hᗮ) μ) := by
  rw [finrank_eigenspace_eq_add_of_reducing H hH hHp μ,
    finrank_eigenspace_compress_eq_of_invariant H hH μ,
    finrank_eigenspace_compress_eq_of_invariant Hᗮ hHp μ]

/-! ## The operator-theoretic root: reducing ⟺ commuting with the projection

Every reducing-subspace result above (the spectrum union, the eigenspace direct
sum, the multiplicity additivity) is a shadow of a single operator identity: `H`
reduces `T` **iff** `T` commutes with the orthogonal projection `P_H`.  This
section proves that characterisation and derives the block-diagonal
reconstruction

  `P_H T P_H + P_{Hᗮ} T P_{Hᗮ} = T`

on a reducing subspace, together with its trace corollary.  Everything is
symmetry-free — the projection `P_H := H.starProjection` is self-adjoint by
construction, but the *operator* `T` is arbitrary. -/

/-- Local characterisation of the kernel of an orthogonal projection: `P_H v = 0`
iff `v ∈ Hᗮ`.  (Re-derived from the reconstruction identity
`P_H v + P_{Hᗮ} v = v` so the section depends only on lemmas available at this
Mathlib pin.) -/
private theorem starProjection_eq_zero_iff_mem_orthogonal {H : Submodule 𝕜 V}
    {v : V} : H.starProjection v = 0 ↔ v ∈ Hᗮ := by
  have hadd : H.starProjection v + Hᗮ.starProjection v = v :=
    H.starProjection_add_starProjection_orthogonal v
  constructor
  · intro h
    rw [h, zero_add] at hadd
    rw [← hadd]; exact Hᗮ.starProjection_apply_mem v
  · intro hv
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at hadd
    have h2 : H.starProjection v + v = 0 + v := by rw [zero_add]; exact hadd
    exact add_right_cancel h2

/-- **Reducing ⟹ commuting.**  If both `H` and `Hᗮ` are `T`-invariant then `T`
commutes pointwise with the orthogonal projection `P_H := H.starProjection`:

  `T (P_H v) = P_H (T v)`  for every `v`.

Split `v = P_H v + P_{Hᗮ} v` with `P_H v ∈ H` and `P_{Hᗮ} v ∈ Hᗮ`.  Invariance
sends `T (P_H v) ∈ H` and `T (P_{Hᗮ} v) ∈ Hᗮ`, so applying `P_H` to
`T v = T (P_H v) + T (P_{Hᗮ} v)` keeps the first term (it already lies in `H`) and
kills the second (it lies in `Hᗮ`), leaving exactly `T (P_H v)`. -/
theorem commute_starProjection_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) (v : V) :
    T (H.starProjection v) = H.starProjection (T v) := by
  set a := H.starProjection v with ha_def
  set b := Hᗮ.starProjection v with hb_def
  have hab : a + b = v := H.starProjection_add_starProjection_orthogonal v
  have haH : a ∈ H := H.starProjection_apply_mem v
  have hbHp : b ∈ Hᗮ := Hᗮ.starProjection_apply_mem v
  have hTaH : T a ∈ H := hH a haH
  have hTbHp : T b ∈ Hᗮ := hHp b hbHp
  have hTv : T v = T a + T b := by rw [← hab, map_add]
  rw [hTv, map_add, Submodule.starProjection_eq_self_iff.mpr hTaH,
    starProjection_eq_zero_iff_mem_orthogonal.mpr hTbHp, add_zero]

/-- **Commuting ⟹ reducing.**  If `T` commutes with the orthogonal projection
`P_H` (pointwise, `T (P_H v) = P_H (T v)` for all `v`), then both `H` and `Hᗮ`
are `T`-invariant, i.e. `H` reduces `T`.

For `y ∈ H`, `P_H y = y`, so `P_H (T y) = T (P_H y) = T y`, hence `T y ∈ H`.  For
`y ∈ Hᗮ`, `P_H y = 0`, so `P_H (T y) = T (P_H y) = 0`, hence `T y ∈ Hᗮ`. -/
theorem reducing_of_commute_starProjection {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hcomm : ∀ v, T (H.starProjection v) = H.starProjection (T v)) :
    (∀ y ∈ H, T y ∈ H) ∧ (∀ y ∈ Hᗮ, T y ∈ Hᗮ) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have h : H.starProjection (T y) = T y := by
      rw [← hcomm y, Submodule.starProjection_eq_self_iff.mpr hy]
    exact Submodule.starProjection_eq_self_iff.mp h
  · have h : H.starProjection (T y) = 0 := by
      rw [← hcomm y, starProjection_eq_zero_iff_mem_orthogonal.mpr hy, map_zero]
    exact starProjection_eq_zero_iff_mem_orthogonal.mp h

/-- **Reducing subspaces are exactly the projection-commutants (characterisation).**

The operator-theoretic heart of every reducing-subspace result in this file: a
subspace `H` reduces `T` — both `H` and `Hᗮ` are `T`-invariant — *iff* `T`
commutes with the orthogonal projection `P_H := H.starProjection`:

  `(∀ y ∈ H, T y ∈ H) ∧ (∀ y ∈ Hᗮ, T y ∈ Hᗮ)  ↔  ∀ v, T (P_H v) = P_H (T v)`.

Forward is `commute_starProjection_of_reducing`, backward is
`reducing_of_commute_starProjection`.  No symmetry of `T` is used; the only
self-adjointness in play is that of the projection itself.  This is the textbook
"`H` reduces `T` ⟺ `PT = TP`" for a self-adjoint projection `P = P_H`. -/
theorem reducing_iff_commute_starProjection {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V) :
    ((∀ y ∈ H, T y ∈ H) ∧ (∀ y ∈ Hᗮ, T y ∈ Hᗮ)) ↔
      ∀ v, T (H.starProjection v) = H.starProjection (T v) :=
  ⟨fun h => commute_starProjection_of_reducing H h.1 h.2,
    reducing_of_commute_starProjection H⟩

/-- **Block-diagonal reconstruction (pointwise).**

On a reducing subspace the two orthogonal compressions reassemble `T` exactly:

  `P_H (T (P_H v)) + P_{Hᗮ} (T (P_{Hᗮ} v)) = T v`  for every `v`.

Using `commute_starProjection_of_reducing` on each block, `P_H (T (P_H v))`
collapses to `P_H (P_H (T v)) = P_H (T v)` (idempotence of the projection), and
likewise for `Hᗮ`; the two pieces sum to `T v` by
`starProjection_add_starProjection_orthogonal`.  (That `Hᗮ` also reduces `T` uses
`Hᗮᗮ = H`.)  This is the operator-level statement whose diagonal blocks are the
compressions `compress T H` and `compress T Hᗮ`, and whose spectral shadow is
`spectrum_eq_union_of_reducing`. -/
theorem starProjection_compress_add_orthogonal_eq_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    (v : V) :
    H.starProjection (T (H.starProjection v)) +
        Hᗮ.starProjection (T (Hᗮ.starProjection v)) = T v := by
  have hcH := commute_starProjection_of_reducing H hH hHp v
  -- `Hᗮ` also reduces `T`: `Hᗮ` is invariant and `(Hᗮ)ᗮ = H` is invariant.
  have hHpp : ∀ y ∈ Hᗮᗮ, T y ∈ Hᗮᗮ := by rw [H.orthogonal_orthogonal]; exact hH
  have hcHp := commute_starProjection_of_reducing Hᗮ hHp hHpp v
  rw [hcH, hcHp,
    Submodule.starProjection_eq_self_iff.mpr (H.starProjection_apply_mem (T v)),
    Submodule.starProjection_eq_self_iff.mpr (Hᗮ.starProjection_apply_mem (T v))]
  exact H.starProjection_add_starProjection_orthogonal (T v)

/-- **Block-diagonal reconstruction (operator form).**

The operator identity behind `starProjection_compress_add_orthogonal_eq_of_reducing`:
on a reducing subspace the ambient compressions `P_H ∘ T ∘ P_H` and
`P_{Hᗮ} ∘ T ∘ P_{Hᗮ}` sum to `T` as endomorphisms of `V`. -/
theorem starProjection_compress_add_orthogonal_op_eq_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (H.starProjection.toLinearMap ∘ₗ T ∘ₗ H.starProjection.toLinearMap) +
        (Hᗮ.starProjection.toLinearMap ∘ₗ T ∘ₗ Hᗮ.starProjection.toLinearMap) = T := by
  ext v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  exact starProjection_compress_add_orthogonal_eq_of_reducing H hH hHp v

/-- **Trace additivity over a reducing subspace.**

Taking the trace of the block-diagonal reconstruction
(`starProjection_compress_add_orthogonal_op_eq_of_reducing`) gives that the trace
of `T` splits as the sum of the traces of its two ambient compression blocks:

  `tr T = tr (P_H T P_H) + tr (P_{Hᗮ} T P_{Hᗮ})`.

The concrete invariant-level form of the block-diagonal picture, and the trace
analogue of the multiplicity additivity `finrank_eigenspace_eq_add_of_reducing`.
Symmetry-free. -/
theorem trace_eq_add_starProjection_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.trace 𝕜 V T =
      LinearMap.trace 𝕜 V
          (H.starProjection.toLinearMap ∘ₗ T ∘ₗ H.starProjection.toLinearMap) +
        LinearMap.trace 𝕜 V
          (Hᗮ.starProjection.toLinearMap ∘ₗ T ∘ₗ Hᗮ.starProjection.toLinearMap) := by
  have h := (LinearMap.trace 𝕜 V).map_add
    (H.starProjection.toLinearMap ∘ₗ T ∘ₗ H.starProjection.toLinearMap)
    (Hᗮ.starProjection.toLinearMap ∘ₗ T ∘ₗ Hᗮ.starProjection.toLinearMap)
  rw [starProjection_compress_add_orthogonal_op_eq_of_reducing H hH hHp] at h
  exact h

/-- **Ambient-compression trace = honest compression trace (cyclic-trace bridge).**

The ambient compression `P_H ∘ T ∘ P_H : V → V` and the honest compression
`compress T H : H → H` carry the *same* trace, across the `H ↪ V` coercion:

  `tr_V (P_H T P_H) = tr_H (compress T H)`.

Factor the self-adjoint projection as `P_H = ι ∘ π` with `ι := H.subtype : H → V`
the inclusion and `π := orthogonalProjection H : V → H`.  Then
`P_H T P_H = ι ∘ (compress T H) ∘ π` because `compress T H = π ∘ T ∘ ι`, so the
cyclic property of the trace (`LinearMap.trace_comp_comm'`) moves the outer `ι`
to the right, producing `(compress T H ∘ π) ∘ ι = compress T H ∘ (π ∘ ι)`.  The
inner `π ∘ ι = id_H` because the orthogonal projection fixes vectors already in
`H` (`orthogonalProjection_mem_subspace_eq_self`), leaving exactly
`tr_H (compress T H)`.  No symmetry of `T` and no reducing hypothesis is used —
this is a pure trace-conjugation identity valid for any operator and any
subspace. -/
theorem trace_starProjection_compress_eq_trace_compress {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) :
    LinearMap.trace 𝕜 V
        (H.starProjection.toLinearMap ∘ₗ T ∘ₗ H.starProjection.toLinearMap)
      = LinearMap.trace 𝕜 H (compress T H) := by
  set ι : H →ₗ[𝕜] V := H.subtype with hι
  set π : V →ₗ[𝕜] H := (H.orthogonalProjection : V →L[𝕜] H).toLinearMap with hπ
  -- Operator identity: the ambient compression is the conjugate `ι (compress) π`.
  have hop : H.starProjection.toLinearMap ∘ₗ T ∘ₗ H.starProjection.toLinearMap
      = ι ∘ₗ ((compress T H) ∘ₗ π) := by
    ext v
    simp only [ι, π, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_apply, compress_apply, Submodule.subtype_apply]
  -- The projection is a left inverse of the inclusion on `H`.
  have hπι : π ∘ₗ ι = LinearMap.id := by
    ext y
    simp only [ι, π, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, Submodule.orthogonalProjection_mem_subspace_eq_self,
      LinearMap.id_coe, id_eq]
  rw [hop, LinearMap.trace_comp_comm' ((compress T H) ∘ₗ π) ι,
    LinearMap.comp_assoc, hπι, LinearMap.comp_id]

/-- **Honest trace additivity over a reducing subspace.**

Upgrade of `trace_eq_add_starProjection_compress_of_reducing` from the ambient
compressions to the honest per-block compression operators: if `H` reduces `T`
then the trace of `T` splits as the sum of the traces of the two honest
compressions `compress T H : H → H` and `compress T Hᗮ : Hᗮ → Hᗮ`,

  `tr_V T = tr_H (compress T H) + tr_{Hᗮ} (compress T Hᗮ)`.

Obtained from the ambient block-diagonal trace split
`trace_eq_add_starProjection_compress_of_reducing` by identifying each ambient
compression trace with its honest compression trace via the cyclic-trace bridge
`trace_starProjection_compress_eq_trace_compress`.  This is the trace analogue,
now over the *honest* compression operators, of the multiplicity additivity
`finrank_eigenspace_eq_add_compress_of_reducing`.  Symmetry-free. -/
theorem trace_eq_add_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.trace 𝕜 V T =
      LinearMap.trace 𝕜 H (compress T H) +
        LinearMap.trace 𝕜 (Hᗮ) (compress T Hᗮ) := by
  rw [trace_eq_add_starProjection_compress_of_reducing H hH hHp,
    trace_starProjection_compress_eq_trace_compress H,
    trace_starProjection_compress_eq_trace_compress Hᗮ]

/-! ## Spectral reading: trace = sum of eigenvalues

The trace identities above are *symmetry-free* — they hold for any operator on
any subspace.  The final step interprets them spectrally: for a **symmetric**
operator the trace equals the sum of the eigenvalues (with multiplicity),
because the eigenvector basis diagonalises the operator.  This is where symmetry
finally buys the eigenvalue picture, turning the honest trace additivity
`trace_eq_add_compress_of_reducing` into an additivity statement about the actual
eigenvalue sums of the two compression blocks. -/

omit [FiniteDimensional 𝕜 V] in
/-- **Trace of a diagonalised operator = sum of its diagonal entries.**

If `T` acts diagonally on a basis `b`, `T (b i) = d i • b i`, then its trace is
the sum of the diagonal scalars `d i`.  A one-step consequence of
`LinearMap.trace_eq_matrix_trace`: the matrix of `T` in `b` is diagonal with
entries `d i`, whose matrix trace is `∑ i, d i`.  No symmetry or inner-product
structure is used. -/
theorem trace_eq_sum_of_apply_basis_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : V →ₗ[𝕜] V} (b : Module.Basis ι 𝕜 V) {d : ι → 𝕜}
    (hb : ∀ i, T (b i) = d i • b i) :
    LinearMap.trace 𝕜 V T = ∑ i, d i := by
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, hb, map_smul,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- **Trace = sum of eigenvalues (symmetric operator).**

For a symmetric operator `T` on an `n`-dimensional inner product space, the trace
equals the sum of its `n` eigenvalues (with multiplicity):

  `tr T = ∑ i, λ_i`.

Immediate from `trace_eq_sum_of_apply_basis_smul` applied to the eigenvector
basis, on which `T` acts by the eigenvalues (`apply_eigenvectorBasis`). -/
theorem trace_eq_sum_eigenvalues {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n : ℕ}
    (hVdim : Module.finrank 𝕜 V = n) :
    LinearMap.trace 𝕜 V T = ∑ i, ((hT.eigenvalues hVdim i : 𝕜)) :=
  trace_eq_sum_of_apply_basis_smul (hT.eigenvectorBasis hVdim).toBasis
    (hT.apply_eigenvectorBasis hVdim)

/-- **Eigenvalue-sum additivity over a reducing subspace.**

The spectral capstone of the file.  If `H` reduces a symmetric operator `T`, then
the sum of the eigenvalues of `T` splits as the sum of the eigenvalue sums of the
two honest compression blocks `compress T H` and `compress T Hᗮ`:

  `∑ λ_i(T) = ∑ λ_i(compress T H) + ∑ λ_i(compress T Hᗮ)`.

Obtained by reading the symmetry-free honest trace additivity
`trace_eq_add_compress_of_reducing` through the spectral identity
`trace_eq_sum_eigenvalues` on each of the three symmetric operators `T`,
`compress T H`, `compress T Hᗮ` (the latter two symmetric by
`isSymmetric_compress`).  This is the eigenvalue-sum analogue of the multiplicity
additivity `finrank_eigenspace_eq_add_compress_of_reducing`, and the trace-level
shadow of the Poincaré separation `poincare_separation_compression`. -/
theorem sum_eigenvalues_eq_add_of_reducing {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric)
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    {n nH nHp : ℕ} (hVdim : Module.finrank 𝕜 V = n)
    (hHdim : Module.finrank 𝕜 H = nH) (hHpdim : Module.finrank 𝕜 Hᗮ = nHp) :
    ∑ i, ((hT.eigenvalues hVdim i : 𝕜))
      = ∑ i, (((isSymmetric_compress hT H).eigenvalues hHdim i : 𝕜))
        + ∑ i, (((isSymmetric_compress hT Hᗮ).eigenvalues hHpdim i : 𝕜)) := by
  rw [← trace_eq_sum_eigenvalues hT hVdim,
    ← trace_eq_sum_eigenvalues (isSymmetric_compress hT H) hHdim,
    ← trace_eq_sum_eigenvalues (isSymmetric_compress hT Hᗮ) hHpdim]
  exact trace_eq_add_compress_of_reducing H hH hHp

/-- **Determinant factorization over a reducing subspace.**

The multiplicative analogue of `trace_eq_add_compress_of_reducing`: if `H` reduces
`T` (both `H` and `Hᗮ` are `T`-invariant) then the determinant of `T` factors as
the product of the determinants of its two honest compression blocks,

  `det T = det (compress T H) · det (compress T Hᗮ)`.

On a reducing subspace `T` is block-diagonal: under the linear equivalence
`H × Hᗮ ≃ V` supplied by the orthogonal decomposition
(`Submodule.prodEquivOfIsCompl` for the complement `Hᗮ`), `T` is conjugate to the
product map `(compress T H).prodMap (compress T Hᗮ)` — each honest compression
coincides with `T` on its invariant block (`coe_compress_of_invariant`), so no
off-diagonal error survives.  Conjugation preserves the determinant
(`LinearMap.det_conj`) and the determinant of a product map is the product of the
determinants (`LinearMap.det_prodMap`).  Symmetry-free; the determinant /
eigenvalue-product analogue of the trace / eigenvalue-sum additivity
`trace_eq_add_compress_of_reducing` and `sum_eigenvalues_eq_add_of_reducing`, and
the multiplicative shadow of the multiplicity additivity
`finrank_eigenspace_eq_add_compress_of_reducing`. -/
theorem det_eq_mul_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.det T =
      LinearMap.det (compress T H) * LinearMap.det (compress T Hᗮ) := by
  classical
  -- `Hᗮ` is a complement of `H`, giving the orthogonal decomposition `H × Hᗮ ≃ V`.
  have hcompl : IsCompl H Hᗮ :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  -- On the reducing subspace, `T` conjugates to the block-diagonal product map:
  -- `T ∘ₗ e = e ∘ₗ (compress T H).prodMap (compress T Hᗮ)`.
  have hconj :
      T ∘ₗ (Submodule.prodEquivOfIsCompl H Hᗮ hcompl : (H × Hᗮ) →ₗ[𝕜] V)
        = (Submodule.prodEquivOfIsCompl H Hᗮ hcompl : (H × Hᗮ) →ₗ[𝕜] V)
            ∘ₗ LinearMap.prodMap (compress T H) (compress T Hᗮ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨h, k⟩ := x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [coe_compress_of_invariant H hH h, coe_compress_of_invariant Hᗮ hHp k, map_add]
  -- Solve for `T` as the explicit conjugate `e ∘ₗ prodMap ∘ₗ e.symm`.
  have hT :
      T = (Submodule.prodEquivOfIsCompl H Hᗮ hcompl : (H × Hᗮ) →ₗ[𝕜] V)
            ∘ₗ LinearMap.prodMap (compress T H) (compress T Hᗮ)
            ∘ₗ ((Submodule.prodEquivOfIsCompl H Hᗮ hcompl).symm : V →ₗ[𝕜] (H × Hᗮ)) := by
    rw [← LinearMap.comp_assoc, ← hconj, LinearMap.comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  -- Read `det T` through the conjugation (only the LHS `T`, not the `T`s inside
  -- `compress`), then split the product-map determinant.
  have key : LinearMap.det T
      = LinearMap.det (LinearMap.prodMap (compress T H) (compress T Hᗮ)) := by
    conv_lhs => rw [hT]
    rw [LinearMap.det_conj]
  rw [key, LinearMap.det_prodMap]

/-- **Characteristic-polynomial factorization over a reducing subspace.**

The polynomial master identity of the reducing-subspace block decomposition: if `H`
reduces `T` (both `H` and `Hᗮ` are `T`-invariant) then the characteristic polynomial of
`T` factors as the product of the characteristic polynomials of its two honest compression
blocks,

  `charpoly T = charpoly (compress T H) · charpoly (compress T Hᗮ)`.

This *subsumes* both scalar factorizations already proved on the reducing subspace: the
trace additivity `trace_eq_add_compress_of_reducing` is the second-from-top coefficient of
this identity, and the determinant factorization `det_eq_mul_compress_of_reducing` is its
constant term (up to the sign `(-1)^{finrank V}`).  The proof mirrors
`det_eq_mul_compress_of_reducing` exactly — the same block-diagonal conjugation
`T = e.conj ((compress T H).prodMap (compress T Hᗮ))` through the orthogonal decomposition
`e : (H × Hᗮ) ≃ₗ V` — but reads it through `LinearEquiv.charpoly_conj` (charpoly is
conjugation-invariant) and `LinearMap.charpoly_prodMap` (the charpoly of a block-diagonal
map is the product, `Matrix.charpoly_fromBlocks_zero₁₂`).  Symmetry-free. -/
theorem charpoly_eq_mul_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.charpoly T =
      LinearMap.charpoly (compress T H) * LinearMap.charpoly (compress T Hᗮ) := by
  classical
  have hcompl : IsCompl H Hᗮ :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  -- Same block-diagonal conjugation as `det_eq_mul_compress_of_reducing`:
  -- `T ∘ₗ e = e ∘ₗ (compress T H).prodMap (compress T Hᗮ)`.
  have hconj :
      T ∘ₗ (Submodule.prodEquivOfIsCompl H Hᗮ hcompl : (H × Hᗮ) →ₗ[𝕜] V)
        = (Submodule.prodEquivOfIsCompl H Hᗮ hcompl : (H × Hᗮ) →ₗ[𝕜] V)
            ∘ₗ LinearMap.prodMap (compress T H) (compress T Hᗮ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨h, k⟩ := x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [coe_compress_of_invariant H hH h, coe_compress_of_invariant Hᗮ hHp k, map_add]
  -- Package the conjugation as `T = e.conj (prodMap …)`.
  have hT :
      T = (Submodule.prodEquivOfIsCompl H Hᗮ hcompl).conj
            (LinearMap.prodMap (compress T H) (compress T Hᗮ)) := by
    -- `LinearEquiv.conj_apply` unfolds to the *left*-associated `(↑e ∘ₗ f) ∘ₗ ↑e.symm`,
    -- so (unlike the raw-form determinant proof) we do NOT lead with `← comp_assoc`.
    rw [LinearEquiv.conj_apply, ← hconj, LinearMap.comp_assoc,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.comp_id]
  -- Read `charpoly T` through the conjugation (only the LHS `T`, not the `T`s inside
  -- `compress`), then split the block-diagonal charpoly.
  have key : LinearMap.charpoly T
      = LinearMap.charpoly (LinearMap.prodMap (compress T H) (compress T Hᗮ)) := by
    conv_lhs => rw [hT]
    rw [LinearEquiv.charpoly_conj]
  rw [key, LinearMap.charpoly_prodMap]

/-- **The compression spectrum is the honest-restriction spectrum on an invariant
block.**  Since `compress T H = T.restrict hinv` on an invariant subspace
(`compress_eq_restrict_of_invariant`), the two operators share a spectrum; the
containment `spectrum_compress_subset_of_invariant` is thus the classical fact
that a restriction to an invariant subspace has spectrum inside the ambient one,
routed through the explicit orthogonal compression. -/
theorem spectrum_compress_eq_restrict_of_invariant {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hinv : ∀ y ∈ H, T y ∈ H) :
    spectrum 𝕜 (compress T H) = spectrum 𝕜 (T.restrict hinv) := by
  rw [compress_eq_restrict_of_invariant H hinv]

/-- **Eigenvalue-multiset additivity over a reducing subspace.**  Passing to roots (with
multiplicity) turns the characteristic-polynomial master identity
`charpoly_eq_mul_compress_of_reducing` into its spectral form: the multiset of roots of
`charpoly T` (the eigenvalues of `T`, counted with algebraic multiplicity) is the
**disjoint union** of the root multisets of the two compression blocks,

  `(charpoly T).roots = (charpoly (compress T H)).roots + (charpoly (compress T Hᗮ)).roots`.

This is the *with-multiplicity, root-level* refinement of the set-level spectrum equality
`spectrum_eq_union_of_reducing` and the eigenspace multiplicity additivity
`finrank_eigenspace_eq_add_compress_of_reducing`: it records not only which eigenvalues
occur but exactly how many times each does, sorted blockwise.  (Over `𝕜 = ℂ` the charpoly
splits, so these roots *are* the full eigenvalue list; for self-adjoint `T` over `ℝ` it
already splits into real eigenvalues.)  Proof: `Polynomial.roots_mul`, valid because the
product is `charpoly T`, which is monic and hence nonzero.  Symmetry-free. -/
theorem roots_charpoly_eq_add_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly T).roots =
      (LinearMap.charpoly (compress T H)).roots
        + (LinearMap.charpoly (compress T Hᗮ)).roots := by
  rw [charpoly_eq_mul_compress_of_reducing H hH hHp]
  refine Polynomial.roots_mul ?_
  rw [← charpoly_eq_mul_compress_of_reducing H hH hHp]
  exact (LinearMap.charpoly_monic T).ne_zero

/-- **Eigenvalue-count additivity over a reducing subspace.**  The counting shadow of
`roots_charpoly_eq_add_compress_of_reducing`: the number of eigenvalues of `T` counted with
algebraic multiplicity splits as the sum over the two compression blocks,

  `(charpoly T).roots.card
      = (charpoly (compress T H)).roots.card + (charpoly (compress T Hᗮ)).roots.card`.

(When the charpoly splits — e.g. over `ℂ`, or a self-adjoint operator over `ℝ` — each side
is a genuine `finrank`, so this recovers `finrank V = finrank H + finrank Hᗮ` read on the
eigenvalue lists.)  Immediate from the multiset additivity via `Multiset.card_add`. -/
theorem card_roots_charpoly_eq_add_compress_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly T).roots.card =
      (LinearMap.charpoly (compress T H)).roots.card
        + (LinearMap.charpoly (compress T Hᗮ)).roots.card := by
  rw [roots_charpoly_eq_add_compress_of_reducing H hH hHp, Multiset.card_add]

/-- **The `H`-block eigenvalue multiset is a sub-multiset of the ambient one.**
The with-multiplicity, root-level refinement of the set-level containment
`spectrum_compress_subset_of_invariant`: over a reducing subspace the eigenvalues of the
`H`-compression (roots of `charpoly (compress T H)`, counted with algebraic multiplicity)
occur, *with at least the same multiplicity*, among the eigenvalues of the ambient `T`,

  `(charpoly (compress T H)).roots ≤ (charpoly T).roots`.

This is the multiset shadow of the divisibility `charpoly_compress_dvd_of_reducing`
(`p ∣ q` forces `p.roots ≤ q.roots`) and sharpens the mere set inclusion of spectra to a
counted containment.  Immediate from the additivity
`roots_charpoly_eq_add_compress_of_reducing` via `Multiset.le_add_right`.  Symmetry-free. -/
theorem roots_charpoly_compress_le_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly (compress T H)).roots ≤ (LinearMap.charpoly T).roots := by
  rw [roots_charpoly_eq_add_compress_of_reducing H hH hHp]
  exact Multiset.le_add_right _ _

/-- The `Hᗮ`-block companion of `roots_charpoly_compress_le_of_reducing`: the orthogonal
compression's eigenvalue multiset is likewise a sub-multiset of the ambient one,

  `(charpoly (compress T Hᗮ)).roots ≤ (charpoly T).roots`.

The two blocks' eigenvalue multisets partition the ambient one
(`roots_charpoly_eq_add_compress_of_reducing`), so each is bounded above by the whole;
here via `Multiset.le_add_left`. -/
theorem roots_charpoly_orthogonal_compress_le_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly (compress T Hᗮ)).roots ≤ (LinearMap.charpoly T).roots := by
  rw [roots_charpoly_eq_add_compress_of_reducing H hH hHp]
  exact Multiset.le_add_left _ _

/-! ### Upgrading eigenvalue-count additivity to a genuine `finrank` identity

The multiset additivity `card_roots_charpoly_eq_add_compress_of_reducing` is
*unconditional*, but its individual `roots.card` terms only equal the honest
block dimensions once the relevant characteristic polynomials **split** (over
`ℝ` a charpoly can carry complex-conjugate roots that never appear in
`.roots`).  Under a single splitting hypothesis on the ambient `charpoly T`,
both blocks split automatically (their charpolys *divide* `charpoly T`), so the
eigenvalue lists have length exactly `finrank`, turning the count additivity
into the genuine `finrank V = finrank H + finrank Hᗮ` read on eigenvalue
lists.  (Over `𝕜 = ℂ` every charpoly splits, so all hypotheses are free; for a
self-adjoint `T` over `ℝ` the spectral theorem supplies the same splitting.) -/

/-- Each compression block's characteristic polynomial **divides** the ambient
one, straight from the master factorisation `charpoly_eq_mul_compress_of_reducing`. -/
theorem charpoly_compress_dvd_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.charpoly (compress T H) ∣ LinearMap.charpoly T :=
  ⟨LinearMap.charpoly (compress T Hᗮ), charpoly_eq_mul_compress_of_reducing H hH hHp⟩

/-- The orthogonal block's charpoly likewise divides the ambient one (the
factorisation is symmetric in the two blocks up to `mul_comm`). -/
theorem charpoly_orthogonal_compress_dvd_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    LinearMap.charpoly (compress T Hᗮ) ∣ LinearMap.charpoly T :=
  ⟨LinearMap.charpoly (compress T H), by
    rw [charpoly_eq_mul_compress_of_reducing H hH hHp, mul_comm]⟩

/-- **Eigenvalue-list length = dimension, when the charpoly splits.**  For any
operator `S` on a finite-dimensional inner product space whose characteristic
polynomial splits, the multiset of eigenvalues (roots of `charpoly S`, counted
with algebraic multiplicity) has cardinality exactly `finrank`.  This is the
bridge that upgrades a `Multiset.card` of eigenvalues into an honest dimension:
`Polynomial.splits_iff_card_roots` gives `roots.card = natDegree`, and
`LinearMap.charpoly_natDegree` identifies that degree with `finrank`. -/
theorem card_roots_charpoly_eq_finrank_of_splits {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] {S : W →ₗ[𝕜] W}
    (hsplit : (LinearMap.charpoly S).Splits) :
    (LinearMap.charpoly S).roots.card = Module.finrank 𝕜 W := by
  rw [Polynomial.splits_iff_card_roots.mp hsplit, LinearMap.charpoly_natDegree]

/-- On a reducing subspace, if the ambient `charpoly T` splits then the `H`-block
compression's eigenvalue list has length exactly `finrank 𝕜 H`.  The block charpoly
splits because it divides `charpoly T` (`charpoly_compress_dvd_of_reducing`), and then
`card_roots_charpoly_eq_finrank_of_splits` reads its length off as a dimension. -/
theorem card_roots_charpoly_compress_eq_finrank_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    (hsplit : (LinearMap.charpoly T).Splits) :
    (LinearMap.charpoly (compress T H)).roots.card = Module.finrank 𝕜 H :=
  card_roots_charpoly_eq_finrank_of_splits
    (hsplit.splits_of_dvd (LinearMap.charpoly_monic T).ne_zero
      (charpoly_compress_dvd_of_reducing H hH hHp))

/-- The `Hᗮ`-block companion of `card_roots_charpoly_compress_eq_finrank_of_reducing`:
the orthogonal compression's eigenvalue list has length exactly `finrank 𝕜 Hᗮ`. -/
theorem card_roots_charpoly_orthogonal_compress_eq_finrank_of_reducing {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    (hsplit : (LinearMap.charpoly T).Splits) :
    (LinearMap.charpoly (compress T Hᗮ)).roots.card = Module.finrank 𝕜 Hᗮ :=
  card_roots_charpoly_eq_finrank_of_splits
    (hsplit.splits_of_dvd (LinearMap.charpoly_monic T).ne_zero
      (charpoly_orthogonal_compress_dvd_of_reducing H hH hHp))

/-- **The `finrank` identity read on eigenvalue lists.**  Combining the
unconditional multiset additivity `card_roots_charpoly_eq_add_compress_of_reducing`
with the splitting hypothesis, the ambient dimension equals the sum of the two
compression blocks' eigenvalue-list lengths:

  `finrank V = (charpoly (compress T H)).roots.card + (charpoly (compress T Hᗮ)).roots.card`.

Together with `card_roots_charpoly_compress_eq_finrank_of_reducing` (and its `Hᗮ`
companion), which identify each summand with `finrank H` and `finrank Hᗮ`, this is the
genuine `finrank V = finrank H + finrank Hᗮ` of a reducing decomposition **realised on
the eigenvalue lists**: not merely that the dimensions add, but that the eigenvalues of
`T` (with multiplicity) partition exactly into the eigenvalues of the two blocks.
Symmetry-free. -/
theorem finrank_eq_add_card_roots_compress_of_reducing_of_splits {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ)
    (hsplit : (LinearMap.charpoly T).Splits) :
    Module.finrank 𝕜 V =
      (LinearMap.charpoly (compress T H)).roots.card
        + (LinearMap.charpoly (compress T Hᗮ)).roots.card := by
  rw [← card_roots_charpoly_eq_finrank_of_splits hsplit,
    card_roots_charpoly_eq_add_compress_of_reducing H hH hHp]

/-! ### The algebraically closed (e.g. `ℂ`) corollaries: splitting is automatic

Every theorem in the previous section carries an explicit splitting hypothesis
`(LinearMap.charpoly _).Splits`.  Over an **algebraically closed** field — in
particular `𝕜 = ℂ`, the archetypal `RCLike` field — that hypothesis is free:
`IsAlgClosed.splits` splits every polynomial over its own field.  The docstrings
above repeatedly note that "over `𝕜 = ℂ` every charpoly splits, so all
hypotheses are free"; this section states the resulting *hypothesis-free*
corollaries.  With `[IsAlgClosed 𝕜]` in force the eigenvalue lists of `T` and of
each compression block have length exactly the relevant `finrank`,
unconditionally — no separate `Splits` argument is required. -/

/-- **Eigenvalue-list length = dimension, over an algebraically closed field.**
The `IsAlgClosed` specialisation of `card_roots_charpoly_eq_finrank_of_splits`:
for any operator on a finite-dimensional space over an algebraically closed
field the multiset of eigenvalues (roots of the charpoly, with multiplicity) has
cardinality exactly `finrank`, with no splitting hypothesis. -/
theorem card_roots_charpoly_eq_finrank_of_isAlgClosed {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    [IsAlgClosed 𝕜] (S : W →ₗ[𝕜] W) :
    (LinearMap.charpoly S).roots.card = Module.finrank 𝕜 W :=
  card_roots_charpoly_eq_finrank_of_splits (IsAlgClosed.splits _)

/-- Over an algebraically closed field, the `H`-block compression's eigenvalue
list has length exactly `finrank 𝕜 H` on a reducing subspace — the
hypothesis-free form of `card_roots_charpoly_compress_eq_finrank_of_reducing`. -/
theorem card_roots_charpoly_compress_eq_finrank_of_reducing_of_isAlgClosed
    [IsAlgClosed 𝕜] {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly (compress T H)).roots.card = Module.finrank 𝕜 H :=
  card_roots_charpoly_compress_eq_finrank_of_reducing H hH hHp (IsAlgClosed.splits _)

/-- The `Hᗮ`-block companion of the previous corollary: over an algebraically
closed field the orthogonal compression's eigenvalue list has length exactly
`finrank 𝕜 Hᗮ`, with no splitting hypothesis. -/
theorem card_roots_charpoly_orthogonal_compress_eq_finrank_of_reducing_of_isAlgClosed
    [IsAlgClosed 𝕜] {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (LinearMap.charpoly (compress T Hᗮ)).roots.card = Module.finrank 𝕜 Hᗮ :=
  card_roots_charpoly_orthogonal_compress_eq_finrank_of_reducing H hH hHp
    (IsAlgClosed.splits _)

/-- **The `finrank` identity on eigenvalue lists, over an algebraically closed
field.**  The hypothesis-free specialisation of
`finrank_eq_add_card_roots_compress_of_reducing_of_splits`: on any reducing
subspace over an algebraically closed field (e.g. `ℂ`), the ambient dimension is
the sum of the two compression blocks' eigenvalue-list lengths,

  `finrank V = (charpoly (compress T H)).roots.card
                + (charpoly (compress T Hᗮ)).roots.card`,

with **no** splitting side condition.  This is the reading the earlier docstrings
promise: over `ℂ` the eigenvalues of `T` (with multiplicity) partition exactly
into the eigenvalues of the two blocks. -/
theorem finrank_eq_add_card_roots_compress_of_reducing_of_isAlgClosed
    [IsAlgClosed 𝕜] {T : V →ₗ[𝕜] V}
    (H : Submodule 𝕜 V) (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    Module.finrank 𝕜 V =
      (LinearMap.charpoly (compress T H)).roots.card
        + (LinearMap.charpoly (compress T Hᗮ)).roots.card :=
  finrank_eq_add_card_roots_compress_of_reducing_of_splits H hH hHp
    (IsAlgClosed.splits _)

/-! ## Spectral confinement: the compression's eigenvalues stay in `[λ_min, λ_max]`

Poincaré separation gives the *local* interlacing `λ_{k+m} ≤ μ_k ≤ λ_k` for each
`k`.  Because the ambient list `lam := hT.eigenvalues` is **descending**
(`hT.eigenvalues_antitone`), the local bounds telescope to a single *global*
confinement: every eigenvalue `μ_k` of the orthogonal compression lies between
the **smallest** and **largest** eigenvalue of `T`,

  `λ_{n+m-1} ≤ μ_k ≤ λ_0`.

Indeed `μ_k ≤ λ_k ≤ λ_0` since `0 ≤ k` and `lam` is antitone, and
`λ_{n+m-1} ≤ λ_{k+m} ≤ μ_k` since `k + m ≤ n + m - 1`.  This is the operator
form of the statement that compressing a self-adjoint operator to a subspace can
never push an eigenvalue outside `T`'s numerical range `[λ_min, λ_max]`: no
Rayleigh quotient over `H ⊆ V` can exceed the global maximum or fall below the
global minimum.  It is the coarse, index-free shadow of the fine interlacing,
and needs only the top/bottom instances of `poincare_separation_compression`
composed with antitonicity of the ambient spectrum. -/

/-- **Compression eigenvalues are bounded above by the top eigenvalue of `T`.**
For every `k`, the `k`-th descending eigenvalue `μ_k` of the orthogonal
compression `compress T H` satisfies `μ_k ≤ λ_0`, the largest eigenvalue of `T`.
Immediate from the interlacing bound `μ_k ≤ λ_k` and `λ_k ≤ λ_0` (antitonicity,
`0 ≤ k`). -/
theorem compress_eigenvalue_le_top_of_poincare
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (isSymmetric_compress hT H).eigenvalues hHdim k
      ≤ (hT.eigenvalues hVdim) ⟨0, by have := k.isLt; omega⟩ := by
  obtain ⟨_, hup⟩ := poincare_separation_compression hT hVdim H hHdim k
  refine hup.trans (hT.eigenvalues_antitone hVdim (Fin.le_def.mpr ?_))
  simp only [Fin.val_mk]
  omega

/-- **Compression eigenvalues are bounded below by the bottom eigenvalue of `T`.**
For every `k`, the `k`-th descending eigenvalue `μ_k` of the orthogonal
compression `compress T H` satisfies `λ_{n+m-1} ≤ μ_k`, where `λ_{n+m-1}` is the
smallest eigenvalue of `T`.  Immediate from `λ_{k+m} ≤ μ_k` and
`λ_{n+m-1} ≤ λ_{k+m}` (antitonicity, `k + m ≤ n + m - 1`). -/
theorem bot_le_compress_eigenvalue_of_poincare
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (hT.eigenvalues hVdim) ⟨n + m - 1, by have := k.isLt; omega⟩
      ≤ (isSymmetric_compress hT H).eigenvalues hHdim k := by
  obtain ⟨hlo, _⟩ := poincare_separation_compression hT hVdim H hHdim k
  refine le_trans (hT.eigenvalues_antitone hVdim (Fin.le_def.mpr ?_)) hlo
  simp only [Fin.val_mk]
  have := k.isLt; omega

/-- **Spectral confinement of the orthogonal compression.**  Combining the two
extremal bounds: every eigenvalue `μ_k` of `compress T H` lies between the
smallest and largest eigenvalue of `T`,

  `λ_{n+m-1} ≤ μ_k ≤ λ_0`.

The compression cannot create an eigenvalue outside the numerical range
`[λ_min, λ_max]` of `T` — the global, index-free consequence of Poincaré
interlacing. -/
theorem compress_eigenvalue_mem_Icc_of_poincare
    {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (k : Fin n) :
    (hT.eigenvalues hVdim) ⟨n + m - 1, by have := k.isLt; omega⟩
        ≤ (isSymmetric_compress hT H).eigenvalues hHdim k
      ∧ (isSymmetric_compress hT H).eigenvalues hHdim k
          ≤ (hT.eigenvalues hVdim) ⟨0, by have := k.isLt; omega⟩ :=
  ⟨bot_le_compress_eigenvalue_of_poincare hT hVdim H hHdim k,
   compress_eigenvalue_le_top_of_poincare hT hVdim H hHdim k⟩

end CauchyInterlacing.PoincareCompression
