import Mathlib
import Proofs.UrysohnsLemmaOQ01OQ01

/-!
# Tietze Extension as an Explicit Series of Bounded Continuous Corrections

The parent entry (`urysohns-lemma-oq-01-oq-01`) isolates the *engine* of the classical
Tietze proof — the one-step Urysohn approximation `urysohn_approx_step` and the
quantitative iteration `urysohn_approx_iterate` — but it assembles the final extension by
calling Mathlib's `TietzeExtension` machinery (`exists_restrict_eq`), which hides the
limit behind a black box.

This entry removes that black box.  We build the extension **by hand** as a genuinely
convergent series

    G  =  ∑' n, gₙ          in the Banach space  BoundedContinuousFunction X ℝ

where each correction `gₙ` is the global bounded-continuous function produced by one
application of Urysohn's lemma to the current residual, and `‖gₙ‖ ≤ (2/3)ⁿ · (M/3)`.

The geometric majorant makes the series **absolutely convergent**, hence summable because
`BoundedContinuousFunction X ℝ` is complete.  The partial sums approximate `f` on the
closed set `s` with error `(2/3)ⁿ · M → 0`, so the sum restricts to `f`.  Summing the
majorant, `‖G‖ ≤ ∑' n, (2/3)ⁿ · (M/3) = (M/3)·3 = M`, so the extension lands in the *same*
sup-bound `[-M, M]` as the data — the explicit bounded Tietze extension.

## Main results

* `TietzeTsum.gbcf` — the `n`-th correction as a bounded continuous function on `X`.
* `TietzeTsum.gbcf_norm_le` — the geometric sup-norm bound `‖gₙ‖ ≤ (2/3)ⁿ·(M/3)`.
* `TietzeTsum.summable_gbcf` — absolute convergence of the correction series.
* `tietze_extension_via_tsum` — the assembled theorem: there is a bounded continuous
  `G = ∑' n, gₙ` with `G = f` on `s` and `|G| ≤ M` everywhere, built purely as the series.

Everything is machine-checked with no `sorry`, and no part of Mathlib's `TietzeExtension`
API is used.
-/

open Set Function Filter Topology

namespace TietzeTsum

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] {s : Set X}
  (hs : IsClosed s) (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x : s, |f x| ≤ M)

/-- The residual `rₙ = f - (g₀ + … + g_{n-1})|_s` together with its geometric sup-bound
`|rₙ| ≤ (2/3)ⁿ · M`.  The successor step applies the one-step Urysohn lemma
`urysohn_approx_step` to the current residual and subtracts the resulting correction. -/
noncomputable def Res : (n : ℕ) → {r : C(s, ℝ) // ∀ x : s, |r x| ≤ (2 / 3 : ℝ) ^ n * M}
  | 0 => ⟨f, fun x => by simpa using hf x⟩
  | n + 1 =>
      let p := Res n
      ⟨p.1 - restrictToClosed s
          (urysohn_approx_step hs p.1 (mul_nonneg (by positivity) hM) p.2).choose,
        fun x => by
          have happ :=
            (urysohn_approx_step hs p.1 (mul_nonneg (by positivity) hM) p.2).choose_spec.2 x
          have hval :
              (p.1 - restrictToClosed s
                  (urysohn_approx_step hs p.1 (mul_nonneg (by positivity) hM) p.2).choose) x
                = p.1 x - (urysohn_approx_step hs p.1 (mul_nonneg (by positivity) hM) p.2).choose
                    (x : X) := by
            simp [restrictToClosed]
          rw [hval]
          calc
            |p.1 x - (urysohn_approx_step hs p.1 (mul_nonneg (by positivity) hM) p.2).choose (x : X)|
                ≤ 2 / 3 * ((2 / 3 : ℝ) ^ n * M) := happ
            _ = (2 / 3 : ℝ) ^ (n + 1) * M := by ring⟩

/-- The `n`-th correction as a plain continuous function on `X`, obtained from Urysohn's lemma
applied to the residual `Res n`. -/
noncomputable def gcorr (n : ℕ) : C(X, ℝ) :=
  (urysohn_approx_step hs (Res hs f hM hf n).1
      (mul_nonneg (by positivity) hM) (Res hs f hM hf n).2).choose

@[simp] lemma Res_zero : (Res hs f hM hf 0).1 = f := rfl

/-- The defining recursion of the residual, in terms of the correction. -/
lemma Res_succ_fst (n : ℕ) :
    (Res hs f hM hf (n + 1)).1
      = (Res hs f hM hf n).1 - restrictToClosed s (gcorr hs f hM hf n) := rfl

/-- Each correction is globally bounded by `(2/3)ⁿ · (M/3)` — the engine of summability. -/
lemma gcorr_bound (n : ℕ) (y : X) :
    |gcorr hs f hM hf n y| ≤ (2 / 3 : ℝ) ^ n * (M / 3) := by
  have h :=
    (urysohn_approx_step hs (Res hs f hM hf n).1
      (mul_nonneg (by positivity) hM) (Res hs f hM hf n).2).choose_spec.1 y
  calc
    |gcorr hs f hM hf n y| ≤ (2 / 3 : ℝ) ^ n * M / 3 := h
    _ = (2 / 3 : ℝ) ^ n * (M / 3) := by ring

/-- The `n`-th correction packaged as an element of the Banach space of bounded continuous
functions. -/
noncomputable def gbcf (n : ℕ) : BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gcorr hs f hM hf n)
    (gcorr hs f hM hf n).continuous ((2 / 3 : ℝ) ^ n * (M / 3))
    (fun y => by simpa [Real.norm_eq_abs] using gcorr_bound hs f hM hf n y)

@[simp] lemma gbcf_apply (n : ℕ) (y : X) : gbcf hs f hM hf n y = gcorr hs f hM hf n y := rfl

/-- Sup-norm bound on the `n`-th correction. -/
lemma gbcf_norm_le (n : ℕ) : ‖gbcf hs f hM hf n‖ ≤ (2 / 3 : ℝ) ^ n * (M / 3) := by
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (by positivity) (by linarith))).2
    (fun y => ?_)
  simpa [Real.norm_eq_abs] using gcorr_bound hs f hM hf n y

/-- The comparison geometric series `∑ (2/3)ⁿ·(M/3)` is summable. -/
lemma summable_geo : Summable (fun n : ℕ => (2 / 3 : ℝ) ^ n * (M / 3)) :=
  (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 1)).mul_right (M / 3)

/-- **Absolute convergence of the correction series.** -/
lemma summable_norm_gbcf : Summable (fun n => ‖gbcf hs f hM hf n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (gbcf_norm_le hs f hM hf)
    (summable_geo (M := M))

/-- The correction series is summable in the Banach space of bounded continuous functions. -/
lemma summable_gbcf : Summable (gbcf hs f hM hf) :=
  (summable_norm_gbcf hs f hM hf).of_norm

end TietzeTsum

open TietzeTsum in
/-- **Tietze extension theorem, as an explicit series.**

For a closed set `s` in a normal space `X` and a continuous `f : s → ℝ` with `|f| ≤ M`,
the function `G = ∑' n, gₙ`, where each `gₙ` is the bounded-continuous Urysohn correction to
the running residual, is a bounded continuous extension of `f` to all of `X` with the *same*
sup-bound `|G| ≤ M`.  The construction is the genuine uniform limit of the partial sums and
uses none of Mathlib's `TietzeExtension` machinery. -/
theorem tietze_extension_via_tsum {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) (f : C(s, ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x : s, |f x| ≤ M) :
    ∃ G : BoundedContinuousFunction X ℝ,
      (∀ x : s, G (x : X) = f x) ∧ G = ∑' n, gbcf hs f hM hf n ∧ (∀ y, |G y| ≤ M) := by
  classical
  set G : BoundedContinuousFunction X ℝ := ∑' n, gbcf hs f hM hf n with hG
  have hsum : Summable (gbcf hs f hM hf) := summable_gbcf hs f hM hf
  have hHasSum : HasSum (gbcf hs f hM hf) G := by rw [hG]; exact hsum.hasSum
  -- The partial sums on `s` equal `f - rₙ`.
  have psum : ∀ (x : s) (n : ℕ),
      ∑ i ∈ Finset.range n, (gbcf hs f hM hf i) (x : X) = f x - (Res hs f hM hf n).1 x := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Res_succ_fst]
      simp only [ContinuousMap.sub_apply, restrictToClosed_apply, gbcf_apply]
      ring
  -- The residual tends to `0` pointwise on `s`.
  have hpow : Tendsto (fun n => (2 / 3 : ℝ) ^ n * M) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3)
        (by norm_num : (2 / 3 : ℝ) < 1)).mul_const M
  have hres0 : ∀ x : s, Tendsto (fun n => (Res hs f hM hf n).1 x) atTop (𝓝 0) := by
    intro x
    refine squeeze_zero_norm (fun n => ?_) hpow
    simpa [Real.norm_eq_abs] using (Res hs f hM hf n).2 x
  refine ⟨G, fun x => ?_, hG, fun y => ?_⟩
  · -- Evaluate the series at `x : s` and identify the limit with `f x`.
    -- Evaluation at `(x : X)` is a continuous additive homomorphism.
    let ev : BoundedContinuousFunction X ℝ →+ ℝ :=
      { toFun := fun h => h (x : X), map_zero' := by simp, map_add' := by intro a b; simp }
    have hev : Continuous ev := by
      have hL : LipschitzWith 1 ev := by
        rw [lipschitzWith_iff_dist_le_mul]
        intro a b
        simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, NNReal.coe_one, one_mul]
        exact BoundedContinuousFunction.dist_coe_le_dist (x : X)
      exact hL.continuous
    have hx : HasSum (fun n => (gbcf hs f hM hf n) (x : X)) (G (x : X)) := by
      have := hHasSum.map ev hev
      simpa [ev, Function.comp] using this
    have hpart : Tendsto
        (fun n => ∑ i ∈ Finset.range n, (gbcf hs f hM hf i) (x : X)) atTop (𝓝 (G (x : X))) :=
      hx.tendsto_sum_nat
    have hpart' : Tendsto (fun n => f x - (Res hs f hM hf n).1 x) atTop (𝓝 (G (x : X))) := by
      simpa only [psum x] using hpart
    have hlim : Tendsto (fun n => f x - (Res hs f hM hf n).1 x) atTop (𝓝 (f x)) := by
      simpa using Tendsto.const_sub (f x) (hres0 x)
    exact tendsto_nhds_unique hpart' hlim
  · -- Sup-norm bound: `‖G‖ ≤ ∑ (2/3)ⁿ (M/3) = M`.
    have hnorm : ‖G‖ ≤ M := by
      have h1 : ‖G‖ ≤ ∑' n, ‖gbcf hs f hM hf n‖ := by
        rw [hG]; exact norm_tsum_le_tsum_norm (summable_norm_gbcf hs f hM hf)
      have h2 : ∑' n, ‖gbcf hs f hM hf n‖ ≤ ∑' n, (2 / 3 : ℝ) ^ n * (M / 3) :=
        Summable.tsum_le_tsum (gbcf_norm_le hs f hM hf) (summable_norm_gbcf hs f hM hf)
          (summable_geo (M := M))
      have h3 : ∑' n, (2 / 3 : ℝ) ^ n * (M / 3) = M := by
        have hr : (1 - 2 / 3 : ℝ)⁻¹ = 3 := by norm_num
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2 / 3)
          (by norm_num : (2 / 3 : ℝ) < 1), hr]
        ring
      linarith [h1, h2, h3.ge, h3.le]
    have := (BoundedContinuousFunction.norm_le hM).1 hnorm y
    simpa [Real.norm_eq_abs] using this
