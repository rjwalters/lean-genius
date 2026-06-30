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

end CauchyInterlacing.PoincareCompression
