import Mathlib
import Proofs.UrysohnsLemmaOQ01OQ01OQ02

/-!
# An Explicit Modulus of Uniform Convergence for the Urysohn–Tietze Series

The grandparent entry (`urysohns-lemma-oq-01-oq-01-oq-01`) builds the Tietze
extension **by hand** as a genuinely convergent series

    G  =  ∑' n, gₙ          in the Banach space  BoundedContinuousFunction X ℝ

and the parent entry (`urysohns-lemma-oq-01-oq-01-oq-02`) tracks the sup-norm of
the *partial sums* to recover the sharp norm-preserving form `‖G‖ = ‖f‖`.

This entry answers the parent's second open question:

> *Expose an explicit modulus of uniform convergence by bounding the tail*
> `‖G − ∑_{i<n} gᵢ‖ ≤ (2/3)ⁿ · M`, *quantifying how fast the partial sums
> approach the norm-preserving extension.*

The partial-sum bound `partialSum_norm_le` of the parent only says each partial
sum stays inside `[-M, M]`; it does **not** say the partial sums converge, nor
how fast.  Here we make the rate explicit.  The mechanism is the geometric
*tail*: writing `G − ∑_{i<n} gᵢ = ∑' i, g_{i+n}` (the tail of a summable series in
a complete space), the majorant `‖g_{i+n}‖ ≤ (2/3)^{i+n}·(M/3)` sums to

    ∑' i, (2/3)^{i+n}·(M/3) = (2/3)ⁿ · ∑' i, (2/3)ⁱ·(M/3) = (2/3)ⁿ · M.

So the truncation error decays geometrically with explicit ratio `2/3`, and the
partial sums converge **uniformly** (in sup-norm) to `G`.

## Main results

* `TietzeTsum.tsum_geo_tail` — the shifted geometric majorant sums to
  `(2/3)ⁿ · M`.
* `TietzeTsum.norm_tsum_sub_partialSum_le` — the headline tail bound
  `‖(∑' i, gᵢ) − ∑_{i<n} gᵢ‖ ≤ (2/3)ⁿ · M`.
* `TietzeTsum.tendsto_partialSum` — the partial sums converge uniformly to the
  series, with the explicit `(2/3)ⁿ·M → 0` modulus.
* `tietze_extension_explicit_modulus` — the packaged statement: the
  norm-preserving Tietze extension `G` is the uniform limit of the explicit
  correction series with truncation error `≤ (2/3)ⁿ·‖f‖`.

Everything is machine-checked with no `sorry`, building only on the parent's
explicit series and never on Mathlib's `TietzeExtension` machinery.
-/

open Set Function Filter Topology

namespace TietzeTsum

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] {s : Set X}
  (hs : IsClosed s) (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, |f x| ≤ M)

/-- The shifted geometric majorant is summable: shifting the index of a summable
series leaves it summable. -/
lemma summable_geo_shift (n : ℕ) :
    Summable (fun i : ℕ => (2 / 3 : ℝ) ^ (i + n) * (M / 3)) :=
  (summable_nat_add_iff n).2 (summable_geo (M := M))

/-- **The shifted geometric majorant sums to `(2/3)ⁿ · M`.**  Factoring the common
power `(2/3)ⁿ` out of the tail `∑' i, (2/3)^{i+n}·(M/3)` reduces it to the full
geometric sum `∑' i, (2/3)ⁱ·(M/3) = M`, scaled by `(2/3)ⁿ`. -/
lemma tsum_geo_tail (n : ℕ) :
    ∑' i : ℕ, (2 / 3 : ℝ) ^ (i + n) * (M / 3) = (2 / 3 : ℝ) ^ n * M := by
  have e : ∀ i : ℕ,
      (2 / 3 : ℝ) ^ (i + n) * (M / 3) = (2 / 3 : ℝ) ^ i * ((2 / 3 : ℝ) ^ n * (M / 3)) := by
    intro i; rw [pow_add]; ring
  rw [tsum_congr e, tsum_mul_right,
    tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1),
    show (1 - 2 / 3 : ℝ)⁻¹ = 3 by norm_num]
  ring

/-- **Explicit modulus of uniform convergence.**  The truncation error of the
explicit Urysohn correction series decays geometrically:

    ‖(∑' i, gᵢ) − ∑_{i<n} gᵢ‖ ≤ (2/3)ⁿ · M.

The tail `(∑' i, gᵢ) − ∑_{i<n} gᵢ` equals the shifted series `∑' i, g_{i+n}`
(the series is summable in the complete space of bounded continuous functions),
whose norm is bounded by the shifted geometric majorant `∑' i, (2/3)^{i+n}·(M/3)`,
which sums to `(2/3)ⁿ·M` by `tsum_geo_tail`. -/
lemma norm_tsum_sub_partialSum_le (n : ℕ) :
    ‖(∑' i, gbcf hs f hM hf i) - ∑ i ∈ Finset.range n, gbcf hs f hM hf i‖
      ≤ (2 / 3 : ℝ) ^ n * M := by
  have hsum : Summable (gbcf hs f hM hf) := summable_gbcf hs f hM hf
  -- Identify the truncation error with the shifted tail series.
  have htail : (∑' i, gbcf hs f hM hf i) - ∑ i ∈ Finset.range n, gbcf hs f hM hf i
      = ∑' i, gbcf hs f hM hf (i + n) := by
    have h := Summable.sum_add_tsum_nat_add n hsum
    rw [← h]; abel
  -- Summability of the shifted families (in norm, and the majorant).
  have hsum_norm_tail : Summable (fun i => ‖gbcf hs f hM hf (i + n)‖) :=
    (summable_nat_add_iff n).2 (summable_norm_gbcf hs f hM hf)
  rw [htail]
  calc
    ‖∑' i, gbcf hs f hM hf (i + n)‖
        ≤ ∑' i, ‖gbcf hs f hM hf (i + n)‖ := norm_tsum_le_tsum_norm hsum_norm_tail
    _ ≤ ∑' i, (2 / 3 : ℝ) ^ (i + n) * (M / 3) :=
          hsum_norm_tail.tsum_le_tsum (fun i => gbcf_norm_le hs f hM hf (i + n))
            (summable_geo_shift (M := M) n)
    _ = (2 / 3 : ℝ) ^ n * M := tsum_geo_tail (M := M) n

/-- **Uniform convergence of the partial sums, with explicit rate.**  The partial
sums `∑_{i<n} gᵢ` converge to the series `∑' i, gᵢ` in sup-norm, the truncation
error being squeezed to `0` by the geometric modulus `(2/3)ⁿ·M`. -/
lemma tendsto_partialSum :
    Tendsto (fun n => ∑ i ∈ Finset.range n, gbcf hs f hM hf i) atTop
      (𝓝 (∑' i, gbcf hs f hM hf i)) := by
  -- The geometric modulus tends to `0`.
  have hpow : Tendsto (fun n => (2 / 3 : ℝ) ^ n * M) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3)
        (by norm_num : (2 / 3 : ℝ) < 1)).mul_const M
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hpow
  rw [dist_eq_norm, norm_sub_rev]
  exact norm_tsum_sub_partialSum_le hs f hM hf n

end TietzeTsum

/-- **The norm-preserving Tietze extension with an explicit convergence modulus.**

For a closed set `s` in a normal space `X` and a *bounded* continuous
`f : s →ᵇ ℝ`, the explicit Urysohn correction series `g : ℕ → (X →ᵇ ℝ)` — built
entirely from Urysohn's lemma, with no appeal to Mathlib's `TietzeExtension`
machinery — assembles into a bounded continuous extension `G = ∑' n, gₙ` of `f`
that is simultaneously:

* an extension: `G = f` on `s`;
* norm-preserving: `‖G‖ = ‖f‖`;
* the *uniform* limit of its partial sums with an **explicit geometric modulus**:

    ‖G − ∑_{i<n} gᵢ‖ ≤ (2/3)ⁿ · ‖f‖.

The last clause quantifies exactly how fast the explicit construction converges,
turning the parent's qualitative "partial sums stay bounded" into a sharp,
computable error estimate. -/
theorem tietze_extension_explicit_modulus {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) (f : BoundedContinuousFunction s ℝ) :
    ∃ (G : BoundedContinuousFunction X ℝ) (g : ℕ → BoundedContinuousFunction X ℝ),
      (∀ x : s, G (x : X) = f x) ∧ ‖G‖ = ‖f‖ ∧ G = ∑' n, g n ∧
      (∀ n, ‖G - ∑ i ∈ Finset.range n, g i‖ ≤ (2 / 3 : ℝ) ^ n * ‖f‖) := by
  -- Specialise the parent's explicit series to the sharp bound `M = ‖f‖`.
  have hM : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hf : ∀ x : s, |f.toContinuousMap x| ≤ ‖f‖ := by
    intro x
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  -- The norm-preserving extension and its identification as the explicit series.
  obtain ⟨G, hGeq, hGtsum, hGle⟩ :=
    tietze_extension_via_tsum hs f.toContinuousMap hM hf
  refine ⟨G, TietzeTsum.gbcf hs f.toContinuousMap hM hf, hGeq, ?_, hGtsum, ?_⟩
  · -- `‖G‖ = ‖f‖`: antisymmetry, exactly as in the parent's norm-preserving theorem.
    refine le_antisymm ?_ ?_
    · -- `‖G‖ ≤ ‖f‖`: the parent's sharp bound `|G y| ≤ ‖f‖` everywhere.
      refine (BoundedContinuousFunction.norm_le hM).2 (fun y => ?_)
      simpa [Real.norm_eq_abs] using hGle y
    · -- `‖f‖ ≤ ‖G‖`: `G` extends `f`, so each `|f x| = |G x| ≤ ‖G‖`.
      refine (BoundedContinuousFunction.norm_le (norm_nonneg G)).2 (fun x => ?_)
      have hx : (f x : ℝ) = G (x : X) := (hGeq x).symm
      rw [hx]
      exact G.norm_coe_le_norm (x : X)
  · -- Explicit modulus: the tail bound with `M = ‖f‖`.
    intro n
    rw [hGtsum]
    exact TietzeTsum.norm_tsum_sub_partialSum_le hs f.toContinuousMap hM hf n
