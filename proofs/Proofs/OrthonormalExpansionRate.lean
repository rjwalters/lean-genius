import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-
# Rate of convergence for orthonormal expansions

Problem id: `cauchy-schwarz-oq-02-oq-02-oq-02`.

## Background

For an orthonormal family `v : ι → E` in an inner product space and a vector `x`, the
*orthonormal partial sum* (the abstract Fourier / Legendre partial sum)

  `S s = ∑ i ∈ s, ⟪v i, x⟫ • v i`

is the orthogonal projection of `x` onto the span of `{v i : i ∈ s}`.  The parent entry
(`cauchy-schwarz-oq-02-oq-02`, Bessel's inequality in infinite dimensions) records that
`∑' i, ‖⟪v i, x⟫‖² ≤ ‖x‖²` and that the coefficient series is summable.  This entry studies the
**rate at which `S s` converges to `x`** as `s` grows.

## The exported identity Mathlib hides

Mathlib proves Bessel's inequality (`Orthonormal.sum_inner_products_le`) by establishing, *inside*
its proof, the exact error identity

  `‖x − S s‖² = ‖x‖² − ∑ i ∈ s, ‖⟪v i, x⟫‖²`,

but never exposes it as a standalone lemma.  This identity is the whole engine of convergence-rate
analysis, so we extract it (`norm_sub_partialSum_sq`) and build the quantitative theory on top.

## Main results

* `norm_sub_partialSum_sq` : the **error identity** `‖x − S s‖² = ‖x‖² − ∑ i ∈ s, ‖⟪v i, x⟫‖²`.
* `sq_error_antitone` : the squared error is **monotone non-increasing** — enlarging the index set
  never worsens the approximation, decreasing the error by exactly the squared coefficients added.
* `partialSum_isBestApprox_le` : Bessel's finite inequality recovered, `∑ i ∈ s, ‖⟪v i, x⟫‖² ≤ ‖x‖²`.
* `tendsto_sq_error` : the squared error **converges** to the Parseval defect
  `‖x‖² − ∑' i, ‖⟪v i, x⟫‖²` along the directed set of finite index sets.
* `tendsto_partialSum_iff_parseval` : the partial sums converge to `x` **iff** Parseval's identity
  `∑' i, ‖⟪v i, x⟫‖² = ‖x‖²` holds — i.e. completeness of the orthonormal system at `x`.
* `sq_error_eq_tail_of_parseval` / `geometric_rate` : under Parseval, the squared error after the
  first `n` terms equals the **tail** `∑' k, ‖⟪v (n + k), x⟫‖²`; with geometric coefficient decay
  `‖⟪v i, x⟫‖² ≤ C r^i` (`0 ≤ r < 1`, the analytic / smooth regime motivating Fourier and Legendre
  series) this gives the explicit **geometric convergence rate** `‖x − S (range n)‖² ≤ C r^n / (1 − r)`.

All results are `0`-axiom, `0`-sorry.
-/

namespace OrthonormalExpansionRate

open RCLike Real Filter Topology ComplexConjugate
open scoped BigOperators

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **orthonormal partial sum** (abstract Fourier / Legendre partial sum) of `x` over the
finite index set `s`: the orthogonal projection of `x` onto the span of `{v i : i ∈ s}`. The field
`𝕜` is an explicit argument because the coefficients `⟪v i, x⟫` live in `𝕜` while the result lives
in `E`, so `𝕜` is not inferable from the result type. -/
def partialSum (𝕜 : Type*) [RCLike 𝕜] [InnerProductSpace 𝕜 E] (v : ι → E) (x : E)
    (s : Finset ι) : E := ∑ i ∈ s, (inner 𝕜 (v i) x) • v i

/- ============================================================
   Part I — The error identity Mathlib hides
   ============================================================ -/

/-- **Error identity.** For an orthonormal family `v`, the squared approximation error of the
partial sum is the norm of `x` minus the partial Bessel sum:
`‖x − S s‖² = ‖x‖² − ∑ i ∈ s, ‖⟪v i, x⟫‖²`.

Mathlib proves exactly this as an unnamed `suffices` step inside `Orthonormal.sum_inner_products_le`;
here it is extracted as a reusable lemma — the engine of the whole convergence-rate analysis. -/
theorem norm_sub_partialSum_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι) :
    ‖x - partialSum 𝕜 v x s‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 := by
  simp only [partialSum]
  have h₂ :
      (∑ i ∈ s, ∑ j ∈ s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k ∈ s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    classical exact hv.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

/-- The partial Bessel sum is bounded by `‖x‖²` (Bessel's finite inequality), recovered as an
immediate corollary of the error identity together with `‖x − S s‖² ≥ 0`. -/
theorem partialSum_isBestApprox_le {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) (s : Finset ι) :
    ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := norm_sub_partialSum_sq hv x s
  nlinarith [sq_nonneg ‖x - partialSum 𝕜 v x s‖, h]

/- ============================================================
   Part II — Monotone improvement of the approximation
   ============================================================ -/

/-- **Monotone improvement.** Enlarging the index set never worsens the approximation: the squared
error is non-increasing in `s`. Concretely, passing from `s` to a superset `t` decreases the
squared error by exactly the squared coefficients of the freshly added basis vectors. -/
theorem sq_error_antitone {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) {s t : Finset ι}
    (hst : s ⊆ t) :
    ‖x - partialSum 𝕜 v x t‖ ^ 2 ≤ ‖x - partialSum 𝕜 v x s‖ ^ 2 := by
  rw [norm_sub_partialSum_sq hv x s, norm_sub_partialSum_sq hv x t]
  have : ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 ≤ ∑ i ∈ t, ‖⟪v i, x⟫‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => by positivity)
  linarith

/- ============================================================
   Part III — Convergence of the partial sums
   ============================================================ -/

/-- **Convergence of the squared error.** Along the directed set of finite index sets, the squared
approximation error converges to the *Parseval defect* `‖x‖² − ∑' i, ‖⟪v i, x⟫‖²`. -/
theorem tendsto_sq_error {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    Tendsto (fun s : Finset ι => ‖x - partialSum 𝕜 v x s‖ ^ 2) atTop
      (𝓝 (‖x‖ ^ 2 - ∑' i, ‖⟪v i, x⟫‖ ^ 2)) := by
  have hsum := (hv.inner_products_summable x).hasSum
  have h : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2) atTop
      (𝓝 (∑' i, ‖⟪v i, x⟫‖ ^ 2)) := hsum
  have heq : (fun s : Finset ι => ‖x - partialSum 𝕜 v x s‖ ^ 2)
      = fun s : Finset ι => ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 := by
    funext s; exact norm_sub_partialSum_sq hv x s
  rw [heq]
  exact (tendsto_const_nhds).sub h

/-- **Convergence ⟺ Parseval.** The orthonormal partial sums converge to `x` (in norm) if and only
if Parseval's identity `∑' i, ‖⟪v i, x⟫‖² = ‖x‖²` holds — i.e. the system is complete at `x`. -/
theorem tendsto_partialSum_iff_parseval {v : ι → E} (hv : Orthonormal 𝕜 v) (x : E) :
    Tendsto (fun s : Finset ι => ‖x - partialSum 𝕜 v x s‖ ^ 2) atTop (𝓝 0) ↔
      ∑' i, ‖⟪v i, x⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  constructor
  · intro h
    have huniq := tendsto_nhds_unique (tendsto_sq_error hv x) h
    linarith [huniq]
  · intro hP
    have h := tendsto_sq_error hv x
    rw [hP] at h
    simpa [sub_self] using h

/- ============================================================
   Part IV — Quantitative geometric rate (Parseval regime)
   ============================================================ -/

variable {v : ℕ → E}

/-- Under Parseval at `x`, the squared error after the first `n` terms equals the **tail** of the
Bessel series, `∑' k, ‖⟪v (k + n), x⟫‖²`. This is the precise object a convergence rate bounds. -/
theorem sq_error_eq_tail_of_parseval (hv : Orthonormal 𝕜 v) (x : E)
    (hP : ∑' i, ‖⟪v i, x⟫‖ ^ 2 = ‖x‖ ^ 2) (n : ℕ) :
    ‖x - partialSum 𝕜 v x (Finset.range n)‖ ^ 2 = ∑' k, ‖⟪v (k + n), x⟫‖ ^ 2 := by
  have hsummable := hv.inner_products_summable x
  rw [norm_sub_partialSum_sq hv x (Finset.range n)]
  have hsplit := hsummable.sum_add_tsum_nat_add n
  rw [hP] at hsplit
  linarith [hsplit]

/-- **Geometric convergence rate.** Suppose the orthonormal system is complete at `x` (Parseval)
and the squared coefficients decay geometrically, `‖⟪v i, x⟫‖² ≤ C r^i` with `0 ≤ r < 1` — the
behaviour of Fourier and Legendre coefficients of analytic / smooth functions. Then the squared
approximation error after `n` terms decays geometrically:
`‖x − S (range n)‖² ≤ C r^n / (1 − r)`. -/
theorem geometric_rate (hv : Orthonormal 𝕜 v) (x : E)
    (hP : ∑' i, ‖⟪v i, x⟫‖ ^ 2 = ‖x‖ ^ 2)
    {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : ∀ i, ‖⟪v i, x⟫‖ ^ 2 ≤ C * r ^ i) (n : ℕ) :
    ‖x - partialSum 𝕜 v x (Finset.range n)‖ ^ 2 ≤ C * r ^ n / (1 - r) := by
  rw [sq_error_eq_tail_of_parseval hv x hP n]
  have htail_summable : Summable (fun k : ℕ => ‖⟪v (k + n), x⟫‖ ^ 2) :=
    (hv.inner_products_summable x).comp_injective (add_left_injective n)
  have hgeo : Summable (fun k : ℕ => C * r ^ (k + n)) := by
    have hs : Summable (fun k : ℕ => (C * r ^ n) * r ^ k) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    exact hs.congr (fun k => by rw [pow_add]; ring)
  have htail_le : ∑' k, ‖⟪v (k + n), x⟫‖ ^ 2 ≤ ∑' k : ℕ, C * r ^ (k + n) :=
    Summable.tsum_le_tsum (fun k => hC (k + n)) htail_summable hgeo
  refine htail_le.trans (le_of_eq ?_)
  calc ∑' k : ℕ, C * r ^ (k + n)
      = ∑' k : ℕ, (C * r ^ n) * r ^ k := by
        refine tsum_congr (fun k => ?_); rw [pow_add]; ring
    _ = (C * r ^ n) * ∑' k : ℕ, r ^ k := tsum_mul_left
    _ = (C * r ^ n) * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = C * r ^ n / (1 - r) := by rw [div_eq_mul_inv]

end OrthonormalExpansionRate
