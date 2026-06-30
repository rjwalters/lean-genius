import Mathlib
import Proofs.CauchyInterlacingPoincare

/-
# Ky Fan trace interlacing for a compression — weak majorization from Poincaré separation

`CauchyInterlacingPoincare.lean` (#27247) proves the **Poincaré separation
theorem**: for a symmetric operator `T` on an `(n + m)`-dimensional inner product
space `V` with descending eigenvalues `lam`, and a codimension-`m` subspace
`H ≤ V` carrying a symmetric operator `TH` whose Rayleigh quotient agrees with
`T`'s (the orthogonal compression), the descending eigenvalues `mu` of `TH`
separate the eigenvalues of `T` *termwise*:

  `lam ⟨k + m⟩ ≤ mu k ≤ lam ⟨k⟩`     for every `k : Fin n`.

This file answers the natural follow-up: what do these termwise inequalities say
about **sums** of eigenvalues — i.e. about the **trace** of the compression?

Summing `mu k ≤ lam ⟨k⟩` over any index set `s ⊆ Fin n` gives

  `∑_{k ∈ s} mu k ≤ ∑_{k ∈ s} lam ⟨k⟩`,

and summing `lam ⟨k + m⟩ ≤ mu k` gives the matching lower bound.  Three readings:

* **Weak majorization (Ky Fan).**  Taking `s = {0, 1, …, j-1}` (an initial
  segment), every top-`j` partial sum of the compression spectrum is dominated by
  the top-`j` partial sum of the spectrum of `T`:
  `∑_{k < j} mu k ≤ ∑_{k < j} lam k`.  The descending eigenvalues of a compression
  are *weakly majorized* by the largest eigenvalues of the full operator.

* **Trace trapping.**  Taking `s = univ`, the trace of the compression — the sum
  of all `n` of its eigenvalues — lies between the sum of the `n` *smallest* and
  the sum of the `n` *largest* eigenvalues of `T`:
  `∑_{j=m}^{n+m-1} lam j ≤ ∑_k mu k ≤ ∑_{j=0}^{n-1} lam j`.

The proof is the monotonicity of finite sums applied to the termwise Poincaré
bounds: no new spectral theory is used.  The mathematical content is entirely the
Poincaré separation theorem; this file packages its summed (Ky Fan) consequences.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace BigOperators
open CauchyInterlacing.Poincare

namespace CauchyInterlacing.KyFan

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

-- The Poincaré hypotheses are consumed only inside the proof bodies, so force
-- their inclusion into every theorem below.
include T b hT hlam hHdim TH bH hTH hmu hRayleigh

/-- **Ky Fan upper sum bound (arbitrary index set).**  Summing the upper Poincaré
inequality `mu k ≤ lam ⟨k⟩` over any `s : Finset (Fin n)`: the partial sum of the
compression eigenvalues is at most the corresponding sum of the `lam ⟨k⟩`. -/
theorem sum_mu_le_sum_top_lam (s : Finset (Fin n)) :
    ∑ k ∈ s, mu k ≤ ∑ k ∈ s, lam ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  Finset.sum_le_sum fun k _ =>
    (poincare_separation T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh k).2

/-- **Ky Fan lower sum bound (arbitrary index set).**  Summing the lower Poincaré
inequality `lam ⟨k + m⟩ ≤ mu k` over any `s : Finset (Fin n)`. -/
theorem sum_bot_lam_le_sum_mu (s : Finset (Fin n)) :
    ∑ k ∈ s, lam ⟨(k : ℕ) + m, by have := k.isLt; omega⟩ ≤ ∑ k ∈ s, mu k :=
  Finset.sum_le_sum fun k _ =>
    (poincare_separation T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh k).1

/-- **Weak majorization (top-`j` partial sums).**  For every `j : ℕ`, the sum of
the compression eigenvalues with index `< j` is at most the sum of the
corresponding `j` largest eigenvalues of `T`:

  `∑_{k < j} mu k ≤ ∑_{k < j} lam k`.

This is the Ky Fan weak-majorization statement: the descending spectrum of the
compression is weakly majorized by the largest eigenvalues of the full
operator. -/
theorem partial_sum_mu_le_partial_sum_lam (j : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < j), mu k
      ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < j),
          lam ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  sum_mu_le_sum_top_lam T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh _

/-- **Trace upper bound.**  The trace of the compression (sum of all its
eigenvalues) is at most the sum of the `n` largest eigenvalues of `T`. -/
theorem trace_compress_le :
    ∑ k : Fin n, mu k ≤ ∑ k : Fin n, lam ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  sum_mu_le_sum_top_lam T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh _

/-- **Trace lower bound.**  The trace of the compression is at least the sum of the
`n` smallest eigenvalues of `T` (those with index `m, m+1, …, n+m-1`). -/
theorem trace_compress_ge :
    ∑ k : Fin n, lam ⟨(k : ℕ) + m, by have := k.isLt; omega⟩ ≤ ∑ k : Fin n, mu k :=
  sum_bot_lam_le_sum_mu T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh _

/-- **Trace interlacing (two-sided).**  The trace of the compression `TH` of `T`
onto a codimension-`m` subspace is trapped between the sum of the `n` smallest and
the sum of the `n` largest eigenvalues of `T`:

  `∑_{j=m}^{n+m-1} lam j ≤ ∑_k mu k ≤ ∑_{j=0}^{n-1} lam j`. -/
theorem trace_interlacing :
    (∑ k : Fin n, lam ⟨(k : ℕ) + m, by have := k.isLt; omega⟩ ≤ ∑ k : Fin n, mu k)
      ∧ (∑ k : Fin n, mu k ≤ ∑ k : Fin n, lam ⟨(k : ℕ), by have := k.isLt; omega⟩) :=
  ⟨trace_compress_ge T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh,
   trace_compress_le T b lam hT hlam H hHdim TH bH mu hTH hmu hRayleigh⟩

end CauchyInterlacing.KyFan
