import Mathlib
import Proofs.CauchyInterlacingPoincare
import Proofs.CauchyInterlacingCompression

/-
# Positivity and spectral range of orthogonal compressions

This file delivers the two textbook corollaries of the **Poincaré separation /
Cauchy interlacing** machinery that the problem asks for:

1. **Positivity of compressions.**  Every orthogonal compression of a positive
   semidefinite (PSD) operator is again PSD.  We give it in the cleanest possible
   *operator* form, stated with Mathlib's `LinearMap.IsPositive`:

     `T.IsPositive → (compress T H).IsPositive`.

   The proof needs no eigenvalues and no spectral theorem: the orthogonal
   compression's Rayleigh quotient *agrees* with `T`'s on `H`
   (`Submodule.inner_orthogonalProjection_eq_of_mem_right`), so nonnegativity of
   `re ⟪T x, x⟫` transfers verbatim.

2. **The Schur–Horn (majorization) direction, eigenvalue corollaries.**  From the
   termwise Poincaré bounds `lam ⟨k+m⟩ ≤ mu k ≤ lam ⟨k⟩` we read off, for the
   descending spectrum `mu` of the compression:

   * `compress_eigenvalues_nonneg`: if `T ⪰ 0` (all `lam i ≥ 0`) then every
     compression eigenvalue is `≥ 0` — the eigenvalue-form of (1), straight from
     the Poincaré *lower* bound `0 ≤ lam ⟨k+m⟩ ≤ mu k`;
   * `compress_eigenvalue_mem_Icc`: every compression eigenvalue lies in the
     spectral range `[lam_min, lam_max]` of `T` (chaining the two Poincaré bounds
     with antitonicity of `lam`);
   * `trace_compress_nonneg`: a PSD compression has nonnegative trace.

   The *weak* (Ky Fan) majorization itself — `∑_{k<j} mu k ≤ ∑_{k<j} lam k` — is
   the sibling entry `CauchyInterlacingKyFan.lean`; here we package the positivity
   and spectral-range consequences that complete the "Schur–Horn direction"
   picture.  (Full equality-majorization for the zero-padded length-`(n+m)`
   spectrum is a dimension mismatch and is *not* claimed.)

Everything is a verified consequence of the already-proven Poincaré separation
and compression-Rayleigh lemmas — no new spectral theory, no axioms, no sorries.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace BigOperators
open CauchyInterlacing.Poincare

namespace CauchyInterlacing.MajorizationPositivity

/-! ### Positivity of compressions (operator form) -/

section Positivity

open CauchyInterlacing.Compression

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **Positivity of compressions.**  The orthogonal compression of a positive
operator `T` to any subspace `H` is again positive.

`LinearMap.IsPositive` packages symmetry together with `∀ x, 0 ≤ re ⟪T x, x⟫`.
Symmetry transfers via `isSymmetric_compress`; the Rayleigh nonnegativity
transfers because `⟪compress T H y, y⟫_H = ⟪T ↑y, ↑y⟫_V` exactly
(`inner_orthogonalProjection_eq_of_mem_right`).  No spectral theorem and no
eigenvalues are needed. -/
theorem compress_isPositive {T : V →ₗ[𝕜] V} (hT : T.IsPositive) (H : Submodule 𝕜 V) :
    (compress T H).IsPositive := by
  refine ⟨isSymmetric_compress hT.isSymmetric H, fun y => ?_⟩
  have hi : @inner 𝕜 H _ (compress T H y) y = @inner 𝕜 V _ (T (y : V)) (y : V) := by
    rw [compress_apply, Submodule.inner_orthogonalProjection_eq_of_mem_right]
  rw [hi]
  exact hT.2 (y : V)

end Positivity

/-! ### Eigenvalue corollaries from Poincaré separation -/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] {n m : ℕ}
  (T : V →ₗ[𝕜] V) (b : OrthonormalBasis (Fin (n + m)) 𝕜 V) (lam : Fin (n + m) → ℝ)
  (hT : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam)
  (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
  (TH : H →ₗ[𝕜] H) (bH : OrthonormalBasis (Fin n) 𝕜 H) (mu : Fin n → ℝ)
  (hTH : ∀ i, TH (bH i) = (mu i : 𝕜) • bH i) (hmu : Antitone mu)
  (hRayleigh : ∀ y : H, y ≠ 0 →
    RCLike.re (@inner 𝕜 H _ (TH y) y) / ‖y‖ ^ 2
      = RCLike.re (@inner 𝕜 V _ (T (y : V)) (y : V)) / ‖(y : V)‖ ^ 2)

-- The Poincaré hypotheses are consumed inside the proof bodies; force inclusion.
include T b hT hlam hHdim TH bH hTH hmu hRayleigh

/-- **PSD compression has nonnegative eigenvalues.**  If every eigenvalue of `T`
is nonnegative (i.e. `T ⪰ 0`), then every eigenvalue of its compression is
nonnegative.  This is the eigenvalue-form of `compress_isPositive`, read straight
from the Poincaré *lower* bound `lam ⟨k+m⟩ ≤ mu k`. -/
theorem compress_eigenvalues_nonneg (hpos : ∀ i, 0 ≤ lam i) (k : Fin n) :
    0 ≤ mu k :=
  le_trans (hpos _)
    (poincare_separation T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh k).1

/-- **Spectral-range containment.**  Every eigenvalue of the compression lies in
the spectral range `[lam_min, lam_max]` of `T`, where `lam_max = lam ⟨0⟩` and
`lam_min = lam ⟨n+m-1⟩` (recall `lam` is descending).  This sandwiches the
compression spectrum inside the full spectrum, chaining the two Poincaré bounds
with antitonicity of `lam`. -/
theorem compress_eigenvalue_mem_Icc (k : Fin n) :
    mu k ∈ Set.Icc (lam ⟨n + m - 1, by have := k.isLt; omega⟩)
                   (lam ⟨0, by have := k.isLt; omega⟩) := by
  have hk := k.isLt
  have hsep := poincare_separation T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh k
  refine ⟨?_, ?_⟩
  · -- lam_min = lam ⟨n+m-1⟩ ≤ lam ⟨k+m⟩ ≤ mu k
    have hle : (⟨(k : ℕ) + m, by omega⟩ : Fin (n + m)) ≤ ⟨n + m - 1, by omega⟩ := by
      rw [Fin.le_def]; omega
    exact le_trans (hlam hle) hsep.1
  · -- mu k ≤ lam ⟨k⟩ ≤ lam ⟨0⟩ = lam_max
    have hle : (⟨0, by omega⟩ : Fin (n + m)) ≤ ⟨(k : ℕ), by omega⟩ := by
      rw [Fin.le_def]; omega
    exact le_trans hsep.2 (hlam hle)

/-- **Nonnegative trace of a PSD compression.**  If `T ⪰ 0` then the trace of its
compression (the sum of all compression eigenvalues) is nonnegative. -/
theorem trace_compress_nonneg (hpos : ∀ i, 0 ≤ lam i) :
    0 ≤ ∑ k : Fin n, mu k :=
  Finset.sum_nonneg fun k _ =>
    compress_eigenvalues_nonneg T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh hpos k

end CauchyInterlacing.MajorizationPositivity
