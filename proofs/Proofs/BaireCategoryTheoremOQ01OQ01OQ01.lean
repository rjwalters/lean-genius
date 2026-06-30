import Mathlib
import Proofs.BaireCategoryTheoremOQ01

/-!
# The Open Mapping and Closed Graph theorems from Baire's theorem

This file completes the *three pillars of linear functional analysis* in the gallery.
The parent file `BaireCategoryTheoremOQ01OQ01.lean` derived the **Uniform Boundedness
Principle** (Banach–Steinhaus) from the gallery Baire category theorem; this file derives
the other two cornerstones — the **Open Mapping Theorem** and the **Closed Graph
Theorem** — from the *same* gallery category theorem
(`BaireCategoryTheoremOQ01.baire_nonempty_interior`).

## The role of Baire

All three theorems share a single Baire-theoretic engine.  For the open mapping theorem the
engine appears in exactly one place: the image of the unit ball under a surjective operator
covers the target by a countable union of closed sets, so Baire's category theorem hands us
one whose closure has nonempty interior.  Everything afterwards — the rescaling shell
estimate, the convergent successive-approximation series, the open-map and inverse-map
deductions — is pure metric/completeness bookkeeping with **no further appeal to Baire**.

Here the single category-theorem call is routed through the gallery theorem
`baire_nonempty_interior` (the re-export of `nonempty_interior_of_iUnion_of_closed`),
making Baire genuinely load-bearing for this entry, exactly as in the parent's
Banach–Steinhaus derivation.

## Main results

* `exists_approx_preimage_norm_le` — the Baire step: every `y` is approximated to within
  `‖y‖/2` by the image of an element of norm `≤ C‖y‖`.
* `exists_preimage_norm_le` — the quantitative open mapping theorem: every `y` has an exact
  preimage of controlled norm `‖x‖ ≤ C‖y‖` (completeness of the source).
* `isOpenMap` — the **Open Mapping Theorem**: a surjective bounded operator between Banach
  spaces is an open map.
* `continuous_linearEquiv_symm` — the **Inverse Mapping (Banach isomorphism) Theorem**: the
  inverse of a continuous linear bijection between Banach spaces is continuous.
* `continuous_of_isClosed_graph` — the **Closed Graph Theorem**: a linear map between Banach
  spaces with closed graph is continuous.

The argument follows the classical Baire proof (the same route Mathlib takes internally);
the contribution of this entry is to present the open mapping and closed graph theorems as
explicit, fully machine-checked consequences of the gallery Baire category theorem.  No
`sorry`, no extra axioms.
-/

namespace BaireCategoryTheoremOQ01OQ01OQ01

open Set Metric Function Filter
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **First (Baire) step of the open mapping theorem.** For a surjective bounded operator
`T : E →L[𝕜] F` with `F` complete, every `y ∈ F` is approximated to within `‖y‖/2` by the
image of some `x` with `‖x‖ ≤ C‖y‖`. The *only* use of Baire's theorem in the whole
development happens here, supplied by the gallery category theorem
`BaireCategoryTheoremOQ01.baire_nonempty_interior`. -/
theorem exists_approx_preimage_norm_le [CompleteSpace F] (T : E →L[𝕜] F)
    (surj : Surjective T) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (T x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  haveI : Nonempty F := ⟨0⟩
  -- The closed sets `closure (T '' ball 0 n)` cover `F` by surjectivity.
  have A : ⋃ n : ℕ, closure (T '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  -- **The Baire category theorem** (gallery re-export): one of them has nonempty interior.
  have hbaire : ∃ n : ℕ, (interior (closure (T '' ball 0 n))).Nonempty :=
    BaireCategoryTheoremOQ01.baire_nonempty_interior (fun n => isClosed_closure) A
  rcases hbaire with ⟨n, a, ha⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at ha
  rcases ha with ⟨ε, εpos, H⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rcases rescale_to_shell hc (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    -- two points of `closure (T '' ball 0 n)` near `a + d • y` and `a`
    have ha₁ : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H ha₁) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have ha₂ : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]; exact εpos
    rcases Metric.mem_closure_iff.1 (H ha₂) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    -- the difference image is close to `d • y`
    have I : ‖T x - d • y‖ ≤ 2 * δ :=
      calc
        ‖T x - d • y‖ = ‖T x₁ - (a + d • y) - (T x₂ - a)‖ := by
          congr 1; simp only [x, T.map_sub]; abel
        _ ≤ ‖T x₁ - (a + d • y)‖ + ‖T x₂ - a‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by grind [dist_eq_norm']
    -- rescale by `d⁻¹` to land near `y`
    have J : ‖T (d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ := by
      have hxy : T (d⁻¹ • x) - y = d⁻¹ • (T x - d • y) := by
        rw [T.map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hd, one_smul]
      rw [hxy, norm_smul, norm_inv]
      calc
        ‖d‖⁻¹ * ‖T x - d • y‖ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = 1 / 2 * ‖y‖ := by
          simp only [δ]
          field_simp
          ring
    rw [← dist_eq_norm] at J
    have hd' : ‖d‖⁻¹ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ := by simpa using dinv
    have hxx : ‖x₁ - x₂‖ ≤ (n : ℝ) + n :=
      le_trans (norm_sub_le _ _) (add_le_add hx₁.le hx₂.le)
    have K : ‖d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by
      have h1 : ‖d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, norm_inv]
      rw [h1]
      calc
        ‖d‖⁻¹ * ‖x₁ - x₂‖ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * ((n : ℝ) + n) :=
          mul_le_mul hd' hxx (norm_nonneg _) (by positivity)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨d⁻¹ • x, J, K⟩

variable [CompleteSpace E] [CompleteSpace F]

/-- **The Open Mapping Theorem (quantitative form).** A surjective bounded linear map between
Banach spaces admits, for every target `y`, an exact preimage `x` with `‖x‖ ≤ C‖y‖`. The
preimage is built as a convergent successive-approximation series, using completeness of the
source `E`. -/
theorem exists_preimage_norm_le (T : E →L[𝕜] F) (surj : Surjective T) :
    ∃ C > 0, ∀ y, ∃ x, T x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le T surj
  choose g hg using hC
  let h y := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) C0
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n IH => rw [Finset.sum_range_succ, T.map_add, IH, iterate_succ_apply', sub_add]
  have hxlim : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) :=
    su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (T x)) :=
    (T.continuous.tendsto _).comp hxlim
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;>
      norm_num
  have feq : T x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- **The Open Mapping Theorem.** A surjective bounded linear map between Banach spaces is an
open map. -/
protected theorem isOpenMap (T : E →L[𝕜] F) (surj : Surjective T) : IsOpenMap T := by
  intro s hs
  rcases exists_preimage_norm_le T surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have hxw : T (x + w) = z := by rw [T.map_add, wim, fxy, add_sub_cancel]
  rw [← hxw]
  have hmem : x + w ∈ ball x ε :=
    calc
      dist (x + w) x = ‖w‖ := by simp
      _ ≤ C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ (ne_of_gt Cpos)
  exact Set.mem_image_of_mem _ (hε hmem)

/-- **The Inverse Mapping (Banach isomorphism) Theorem.** The inverse of a continuous linear
bijection between Banach spaces is continuous. -/
theorem continuous_linearEquiv_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    Continuous e.symm := by
  set T : E →L[𝕜] F := ⟨e.toLinearMap, h⟩ with hT
  have hTe : ∀ x, T x = e x := fun _ => rfl
  rw [continuous_def]
  intro s hs
  -- `e.symm ⁻¹' s = e '' s` since `e` is a bijection; the image is open by the open mapping theorem
  have hset : ⇑e.symm ⁻¹' s = T '' s := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, hTe]
    constructor
    · intro hy; exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩; simpa using hx
  rw [hset]
  exact BaireCategoryTheoremOQ01OQ01OQ01.isOpenMap T e.surjective s hs

/-- **The Closed Graph Theorem.** A linear map between Banach spaces whose graph is closed is
continuous. The graph is a closed (hence complete) subspace of `E × F`; the first projection
restricts to a continuous linear bijection onto `E`, whose inverse is continuous by the
inverse mapping theorem, and the map is recovered as the second projection composed with that
inverse. -/
theorem continuous_of_isClosed_graph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := by
  letI : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E →ₗ[𝕜] E × F := LinearMap.id.prod g
  have hli : Function.LeftInverse Prod.fst φ₀ := fun _ => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse hli).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  have hsymm : Continuous (φ.symm) := continuous_subtype_val.fst
  have hφ : Continuous (φ : E → g.graph) := by
    have hc := continuous_linearEquiv_symm φ.symm hsymm
    rwa [LinearEquiv.symm_symm] at hc
  exact (continuous_subtype_val.comp hφ).snd

end BaireCategoryTheoremOQ01OQ01OQ01
