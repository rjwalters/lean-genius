import Mathlib
import Proofs.CauchyInterlacingPoincareCompression

/-
# Ky Fan trace interlacing for the *honest* orthogonal compression — Rayleigh hypothesis discharged

`CauchyInterlacingKyFan.lean` sums the termwise Poincaré separation inequalities
into their Ky Fan (weak-majorization / trace) consequences, but it does so for an
**abstract** compression operator `TH` on `H`, carrying the Rayleigh-agreement
side condition

  `⟪TH y, y⟫_H / ‖y‖² = ⟪T ↑y, ↑y⟫_V / ‖↑y‖²`

as a hypothesis on every statement. `CauchyInterlacingCompression.lean` /
`CauchyInterlacingPoincareCompression.lean` show that for the **explicit**
orthogonal compression `compress T H := P_H ∘ T ∘ ι_H` that hypothesis is
automatic (`rayleigh_compress_eq`), and use this to upgrade the *pointwise*
Poincaré separation to the unconditional `poincare_separation_compression`.

This file performs the same discharge for the **summed** (Ky Fan) consequences:
feeding `poincare_separation_compression` through `Finset.sum_le_sum` gives the Ky
Fan weak-majorization and trace-trapping statements for the honest compression
`compress T H` with **no Rayleigh side condition and no abstract `TH`**.  Writing
`lam := hT.eigenvalues` for the descending eigenvalues of `T` and `mu` for those
of `compress T H`:

* `sum_compress_le_sum_top`  : `∑_{k∈s} mu k ≤ ∑_{k∈s} lam ⟨k⟩`     (any `s`)
* `sum_bot_le_sum_compress`  : `∑_{k∈s} lam ⟨k+m⟩ ≤ ∑_{k∈s} mu k`   (any `s`)
* `partial_sum_compress_le_partial_sum_top` : top-`j` weak majorization
* `trace_compress_mem_Icc`   : the real trace of `compress T H` lies in
  `[∑ smallest n eigenvalues of T, ∑ largest n eigenvalues of T]`.

The `trace_compress_mem_Icc` statement is stated on the genuine operator trace
`LinearMap.trace 𝕜 H (compress T H)` (its real part), bridged to the eigenvalue
sum through `trace_eq_sum_eigenvalues`.

This is the arbitrary-codimension, Rayleigh-free Ky Fan analogue of
`poincare_separation_compression`.  It closes the seam left by
`CauchyInterlacingKyFan.lean` (abstract, hypothesis-laden) exactly as
`CauchyInterlacingPoincareCompression.lean` closed the pointwise one.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace BigOperators
open CauchyInterlacing.Compression CauchyInterlacing.PoincareCompression

namespace CauchyInterlacing.KyFanCompression

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **Ky Fan upper sum bound for the honest compression (arbitrary index set).**
Summing the upper Poincaré inequality `mu k ≤ lam ⟨k⟩` — discharged for the
orthogonal compression `compress T H` — over any `s : Finset (Fin n)`.  No
Rayleigh hypothesis. -/
theorem sum_compress_le_sum_top {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (s : Finset (Fin n)) :
    ∑ k ∈ s, (isSymmetric_compress hT H).eigenvalues hHdim k
      ≤ ∑ k ∈ s, (hT.eigenvalues hVdim) ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  Finset.sum_le_sum fun k _ => (poincare_separation_compression hT hVdim H hHdim k).2

/-- **Ky Fan lower sum bound for the honest compression (arbitrary index set).**
Summing the lower Poincaré inequality `lam ⟨k + m⟩ ≤ mu k` over any
`s : Finset (Fin n)`, for the orthogonal compression `compress T H`. -/
theorem sum_bot_le_sum_compress {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n)
    (s : Finset (Fin n)) :
    ∑ k ∈ s, (hT.eigenvalues hVdim) ⟨(k : ℕ) + m, by have := k.isLt; omega⟩
      ≤ ∑ k ∈ s, (isSymmetric_compress hT H).eigenvalues hHdim k :=
  Finset.sum_le_sum fun k _ => (poincare_separation_compression hT hVdim H hHdim k).1

/-- **Weak majorization (top-`j` partial sums) for the honest compression.**
For every `j : ℕ`, the sum of the `compress T H` eigenvalues with index `< j` is
at most the sum of the `j` largest eigenvalues of `T`:

  `∑_{k < j} mu k ≤ ∑_{k < j} lam k`.

The descending spectrum of the orthogonal compression is weakly majorized by the
largest eigenvalues of the full operator — Ky Fan, with no Rayleigh side
condition. -/
theorem partial_sum_compress_le_partial_sum_top {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric)
    {n m : ℕ} (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n) (j : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < j),
        (isSymmetric_compress hT H).eigenvalues hHdim k
      ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < j),
          (hT.eigenvalues hVdim) ⟨(k : ℕ), by have := k.isLt; omega⟩ :=
  sum_compress_le_sum_top hT hVdim H hHdim _

/-- **Real part of the compression trace = sum of its eigenvalues.**  A convenience
bridge from the genuine operator trace `LinearMap.trace 𝕜 H (compress T H)` (a
`𝕜`-scalar) to the real eigenvalue sum that the Ky Fan bounds control.  The
eigenvalues of a symmetric operator are real, so taking `RCLike.re` through the
cast sum leaves them fixed. -/
theorem re_trace_compress_eq_sum {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric)
    {n : ℕ} (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n) :
    RCLike.re (LinearMap.trace 𝕜 H (compress T H))
      = ∑ k, (isSymmetric_compress hT H).eigenvalues hHdim k := by
  rw [trace_eq_sum_eigenvalues (isSymmetric_compress hT H) hHdim, map_sum]
  simp only [RCLike.ofReal_re]

/-- **Trace interlacing for the honest compression (two-sided, on the operator trace).**

The real part of the genuine operator trace of the orthogonal compression
`compress T H` onto a codimension-`m` subspace lies between the sum of the `n`
smallest and the sum of the `n` largest eigenvalues of `T`:

  `∑_{j=m}^{n+m-1} lam j ≤ Re tr(compress T H) ≤ ∑_{j=0}^{n-1} lam j`.

Rayleigh-free: the hypothesis is discharged internally.  This is the honest
operator-trace form of `CauchyInterlacingKyFan.trace_interlacing`. -/
theorem trace_compress_mem_Icc {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) {n m : ℕ}
    (hVdim : Module.finrank 𝕜 V = n + m)
    (H : Submodule 𝕜 V) (hHdim : Module.finrank 𝕜 H = n) :
    RCLike.re (LinearMap.trace 𝕜 H (compress T H))
      ∈ Set.Icc (∑ k : Fin n, (hT.eigenvalues hVdim) ⟨(k : ℕ) + m, by have := k.isLt; omega⟩)
          (∑ k : Fin n, (hT.eigenvalues hVdim) ⟨(k : ℕ), by have := k.isLt; omega⟩) := by
  rw [Set.mem_Icc, re_trace_compress_eq_sum hT H hHdim]
  exact ⟨sum_bot_le_sum_compress hT hVdim H hHdim Finset.univ,
    sum_compress_le_sum_top hT hVdim H hHdim Finset.univ⟩

end CauchyInterlacing.KyFanCompression

