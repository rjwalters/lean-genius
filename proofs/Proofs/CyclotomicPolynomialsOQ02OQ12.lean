/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — EXACT two-path-component
# structure of the quadratic cyclotomic lemniscates (n = 3, 4, 6)

  Slug: erdos-1215-oq-02
  Prior work (this OQ family):
    * OQ02OQ01–07 — sharp two-sided radius/area sandwich for `{|Φ_n| < C}`.
    * OQ02OQ08/OQ10 — first-crossing exit path along every ray, sharp bounds.
    * OQ02OQ11  — small-C DISCONNECTION of the quadratic lemniscates
      (Cassini cover by the two focal `√C`-balls, disjoint when `4C < |a−b|²`).

  ## This file — from "at least two pieces" to "exactly two pieces"

  OQ02OQ11 proved the quadratic cyclotomic lemniscates fall apart into at
  least two pieces in the separated regime.  This file pins the EXACT
  path-component count: each Cassini "petal" (the part of the lemniscate
  inside one focal ball) is **star-shaped about its focus**, hence
  path-connected, so

  > **Main result** (`quadratic_lemniscate_two_path_components`).
  > For `0 < C` with `4C < ‖a − b‖²`, every point of
  > `S = {z : ‖(z−a)(z−b)‖ < C}` is joined inside `S` to focus `a` or to
  > focus `b`, and the foci are NOT joined inside `S` — i.e. `S` has
  > exactly the two path components of its foci.

  The engine is a ray-monotonicity certificate: for `w := z − a`,
  `c := b − a`, `W := ‖w‖`, `D := ‖c‖`, `x := re (w·conj c)` and
  `s ∈ [0,1]` with `2W ≤ D`, the Cassini product does not increase when
  `z` is pulled toward the focus along the segment:

    `W²(W² − 2x + D²) − s²W²(s²W² − 2sx + D²)
       = W²·[G + 2(1 − s³)(WD − x)]`,
    `G = (1−s)·(D − W(1+s))·(D(1+s) − W(1+s²)) ≥ 0`,

  each factor being nonnegative from `2W ≤ D`, `0 ≤ s ≤ 1` and
  Cauchy–Schwarz `x ≤ WD`.  (Identity machine-checked with sympy and
  re-checked by `nlinarith`'s kernel certificate here.)

  Specializations close the quadratic cyclotomic case: `{|Φ₃| < C}` and
  `{|Φ₆| < C}` have exactly two path components for `0 < C < 3/4`, and
  `{|Φ₄| < C}` for `0 < C < 1` — component structure fully determined in
  the sub-threshold regime for all `n` with `φ(n) = 2`.

  ## Perspective within the family

  * Combined with OQ02OQ11 this settles the small-`C` component count for
    the complete quadratic case.  Still open: sharpness (connectivity for
    `C ≥ (|a−b|/2)²`, a through-the-neck path construction) and the quartic
    `φ(n) = 4` cases `n = 5, 8, 10, 12` (multi-focus, multi-petal).
  * The genuinely open driver (C > 1 labyrinth / bounded-length
    reachability of every boundary point) remains blocked on
    polynomial-lemniscate topology Mathlib lacks.

  Result status: 0 sorries, 0 axioms, no `native_decide` — axiom-free
  relative to Mathlib.  The deep `maclane_labyrinth` axiom of the parent
  is untouched.
-/
import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ11

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ12

open CyclotomicPolynomialsOQ02OQ11

/-! ## The ray-monotonicity certificate (real arithmetic) -/

/-- **Certificate lemma.** In the separated regime `2W ≤ D`, pulling toward the
focus does not increase the Cassini product: if `N₁² = W² − 2x + D²` and
`N₂² = s²W² − 2sx + D²` with `x ≤ WD` (Cauchy–Schwarz) and `s ∈ [0,1]`, then
`sW·N₂ ≤ W·N₁`.  Positivity certificate: the squared difference equals
`W²·[(1−s)(D−W(1+s))(D(1+s)−W(1+s²)) + 2(1−s³)(WD−x)]`. -/
private lemma cassini_certificate {W D x s N₁ N₂ : ℝ}
    (hW : 0 ≤ W) (hD : 0 ≤ D) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h2WD : 2 * W ≤ D) (hCS : x ≤ W * D)
    (hE₁ : N₁ ^ 2 = W ^ 2 - 2 * x + D ^ 2)
    (hE₂ : N₂ ^ 2 = s ^ 2 * W ^ 2 - 2 * (s * x) + D ^ 2) :
    s * W * N₂ ≤ W * N₁ := by
  have h1ms : 0 ≤ 1 - s := by linarith
  have hf1 : 0 ≤ D - W * (1 + s) := by nlinarith
  have hf2 : 0 ≤ D * (1 + s) - W * (1 + s ^ 2) := by nlinarith
  have h1ms3 : 0 ≤ 1 - s ^ 3 := by nlinarith
  have hWDx : 0 ≤ W * D - x := by linarith
  have hG : 0 ≤ (1 - s) * (D - W * (1 + s)) * (D * (1 + s) - W * (1 + s ^ 2)) :=
    mul_nonneg (mul_nonneg h1ms hf1) hf2
  have hsq : (s * W) ^ 2 * N₂ ^ 2 ≤ W ^ 2 * N₁ ^ 2 := by
    rw [hE₁, hE₂]
    nlinarith [mul_nonneg (sq_nonneg W) hG,
      mul_nonneg (sq_nonneg W) (mul_nonneg h1ms3 hWDx)]
  have hL : 0 ≤ s * W * N₂ := mul_nonneg (mul_nonneg hs0 hW) hN₂
  have hR : 0 ≤ W * N₁ := mul_nonneg hW hN₁
  calc s * W * N₂ = Real.sqrt ((s * W * N₂) ^ 2) := (Real.sqrt_sq hL).symm
    _ ≤ Real.sqrt ((W * N₁) ^ 2) := Real.sqrt_le_sqrt (by linarith [hsq])
    _ = W * N₁ := Real.sqrt_sq hR

/-! ## The complex segment lemma -/

/-- **Segment monotonicity**: in the separated regime `2‖z − a‖ ≤ ‖b − a‖`,
sliding `z` toward the focus `a` along the segment (`s ∈ [0,1]`) does not
increase the Cassini product `‖(·−a)(·−b)‖`. -/
theorem cassini_segment_le {a b z : ℂ} (h : 2 * ‖z - a‖ ≤ ‖b - a‖) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(s • (z - a)) * (a + s • (z - a) - b)‖ ≤ ‖(z - a) * (z - b)‖ := by
  set w := z - a with hw
  set c := b - a with hc
  have hzb : z - b = w - c := by rw [hw, hc]; ring
  have hsegb : a + s • w - b = s • w - c := by
    rw [hc, real_smul]; ring
  rw [hsegb, hzb, norm_mul, norm_mul, norm_smul, Real.norm_of_nonneg hs0]
  have hsmulSq : normSq (s • w) = s ^ 2 * normSq w := by
    rw [real_smul, normSq_mul, normSq_ofReal]; ring
  have hre : ((s • w) * (starRingEnd ℂ) c).re = s * (w * (starRingEnd ℂ) c).re := by
    rw [real_smul, mul_assoc, re_ofReal_mul]
  have hE₁ : ‖w - c‖ ^ 2 = ‖w‖ ^ 2 - 2 * (w * (starRingEnd ℂ) c).re + ‖c‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_sub, normSq_eq_norm_sq w, normSq_eq_norm_sq c]
    ring
  have hE₂ : ‖s • w - c‖ ^ 2
      = s ^ 2 * ‖w‖ ^ 2 - 2 * (s * (w * (starRingEnd ℂ) c).re) + ‖c‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_sub, hre, hsmulSq, normSq_eq_norm_sq w,
      normSq_eq_norm_sq c]
    ring
  have hCS : (w * (starRingEnd ℂ) c).re ≤ ‖w‖ * ‖c‖ :=
    (re_le_norm _).trans (by rw [norm_mul, norm_conj])
  exact cassini_certificate (norm_nonneg w) (norm_nonneg c) (norm_nonneg _)
    (norm_nonneg _) hs0 hs1 h hCS hE₁ hE₂

/-! ## Star-shaped petals -/

/-- **Each petal is star-shaped about its focus**: in the separated regime the
part of the quadratic lemniscate inside the focal ball `B(a, √C)` is
star-convex with center `a`. -/
theorem starConvex_petal {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    StarConvex ℝ a
      ({z : ℂ | ‖(z - a) * (z - b)‖ < C} ∩ Metric.ball a (Real.sqrt C)) := by
  intro y hy p q hp hq hpq
  obtain ⟨hylevel, hyball⟩ := hy
  rw [Set.mem_setOf_eq] at hylevel
  rw [Metric.mem_ball, dist_eq_norm] at hyball
  have hq1 : q ≤ 1 := by linarith
  have hpt : p • a + q • y = a + q • (y - a) := by
    have hp1 : p = 1 - q := by linarith
    simp only [real_smul, hp1]
    push_cast
    ring
  -- separated regime along the segment: `2‖y − a‖ ≤ ‖b − a‖`
  have hab : 0 < ‖a - b‖ := by
    rcases (norm_nonneg (a - b)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hsep; nlinarith
  have h2sqrt : 2 * Real.sqrt C < ‖b - a‖ := by
    rw [norm_sub_rev]
    have h4C : Real.sqrt (4 * C) < ‖a - b‖ := (Real.sqrt_lt' hab).mpr (by linarith)
    have h4eq : Real.sqrt (4 * C) = 2 * Real.sqrt C := by
      rw [show (4 : ℝ) * C = (2 * Real.sqrt C) ^ 2 by
        rw [mul_pow, Real.sq_sqrt hC.le]; ring]
      exact Real.sqrt_sq (by positivity)
    linarith [h4eq ▸ h4C]
  have h2W : 2 * ‖y - a‖ ≤ ‖b - a‖ := by linarith
  constructor
  · rw [Set.mem_setOf_eq, hpt, add_sub_cancel_left]
    exact lt_of_le_of_lt (cassini_segment_le h2W hq hq1) hylevel
  · rw [Metric.mem_ball, dist_eq_norm, hpt, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hq]
    calc q * ‖y - a‖ ≤ 1 * ‖y - a‖ :=
          mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
      _ = ‖y - a‖ := one_mul _
      _ < Real.sqrt C := hyball

/-- The focus belongs to its petal. -/
theorem focus_mem_petal {a b : ℂ} {C : ℝ} (hC : 0 < C) :
    a ∈ {z : ℂ | ‖(z - a) * (z - b)‖ < C} ∩ Metric.ball a (Real.sqrt C) := by
  constructor
  · simp only [Set.mem_setOf_eq, sub_self, zero_mul, norm_zero]
    exact hC
  · exact Metric.mem_ball_self (Real.sqrt_pos.mpr hC)

/-- **Each petal is path-connected** (star-shaped with nonempty center). -/
theorem isPathConnected_petal {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    IsPathConnected
      ({z : ℂ | ‖(z - a) * (z - b)‖ < C} ∩ Metric.ball a (Real.sqrt C)) :=
  (starConvex_petal hC hsep).isPathConnected (focus_mem_petal hC)

/-! ## Exactly two path components -/

/-- **Main result: the quadratic lemniscate has exactly two path components in
the separated regime `4C < ‖a − b‖²`** — every point is joined inside the set
to focus `a` or to focus `b` (so there are at most two components), and the
foci are not joined to each other (so there are at least two, sharpening
OQ02OQ11's disconnection). -/
theorem quadratic_lemniscate_two_path_components {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    (∀ z ∈ {z : ℂ | ‖(z - a) * (z - b)‖ < C},
        JoinedIn {z : ℂ | ‖(z - a) * (z - b)‖ < C} z a ∨
        JoinedIn {z : ℂ | ‖(z - a) * (z - b)‖ < C} z b) ∧
      ¬ JoinedIn {z : ℂ | ‖(z - a) * (z - b)‖ < C} a b := by
  have hSswap : {z : ℂ | ‖(z - b) * (z - a)‖ < C}
      = {z : ℂ | ‖(z - a) * (z - b)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mul_comm]
  have hsep' : 4 * C < ‖b - a‖ ^ 2 := by rwa [norm_sub_rev]
  constructor
  · intro z hz
    rcases quadratic_lemniscate_subset_union a b hC.le hz with hza | hzb
    · left
      have hpetal := isPathConnected_petal hC hsep
      exact (hpetal.joinedIn z ⟨hz, hza⟩ a (focus_mem_petal hC)).mono
        Set.inter_subset_left
    · right
      have hpetal := isPathConnected_petal (a := b) (b := a) hC hsep'
      rw [hSswap] at hpetal
      exact (hpetal.joinedIn z ⟨hz, hzb⟩ b
        (by rw [← hSswap]; exact focus_mem_petal hC)).mono Set.inter_subset_left
  · intro hJ
    obtain ⟨γ, hγ⟩ := hJ
    have hrange : Set.range γ ⊆
        Metric.ball a (Real.sqrt C) ∪ Metric.ball b (Real.sqrt C) := by
      rintro _ ⟨t, rfl⟩
      exact quadratic_lemniscate_subset_union a b hC.le (hγ t)
    have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
    obtain ⟨z, _, hz⟩ := hpre (Metric.ball a (Real.sqrt C))
      (Metric.ball b (Real.sqrt C)) Metric.isOpen_ball Metric.isOpen_ball hrange
      ⟨a, ⟨0, γ.source⟩, Metric.mem_ball_self (Real.sqrt_pos.mpr hC)⟩
      ⟨b, ⟨1, γ.target⟩, Metric.mem_ball_self (Real.sqrt_pos.mpr hC)⟩
    rw [sqrt_balls_disjoint hC hsep] at hz
    exact Set.notMem_empty z hz

/-- No point is joined to BOTH foci — the two components are genuinely
distinct, so the focus a point is joined to is unique. -/
theorem joined_focus_unique {a b z : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2)
    (hza : JoinedIn {z : ℂ | ‖(z - a) * (z - b)‖ < C} z a)
    (hzb : JoinedIn {z : ℂ | ‖(z - a) * (z - b)‖ < C} z b) : False :=
  (quadratic_lemniscate_two_path_components hC hsep).2 (hza.symm.trans hzb)

/-! ## Specialization `n = 3`: `Φ₃`, foci `ω, ω̄`, exactly two components for
`C < 3/4` -/

/-- **`{|Φ₃| < C}` has exactly two path components for `0 < C < 3/4`**: every
point joins to `ω` or `ω̄`, and the two primitive cube roots of unity are not
joined. -/
theorem levelSet_three_two_path_components {C : ℝ} (hC : 0 < C)
    (hC' : C < 3 / 4) :
    (∀ z ∈ Erdos1215.levelSet (cyclotomic 3 ℂ) C,
        JoinedIn (Erdos1215.levelSet (cyclotomic 3 ℂ) C) z omega3 ∨
        JoinedIn (Erdos1215.levelSet (cyclotomic 3 ℂ) C) z omega3') ∧
      ¬ JoinedIn (Erdos1215.levelSet (cyclotomic 3 ℂ) C) omega3 omega3' := by
  rw [levelSet_cyclotomic_three_eq]
  exact quadratic_lemniscate_two_path_components hC
    (by rw [norm_omega3_sub_sq]; linarith)

/-! ## Specialization `n = 4`: `Φ₄`, foci `± i`, exactly two components for
`C < 1` -/

/-- **`{|Φ₄| < C}` has exactly two path components for `0 < C < 1`** — the
widest exact-count regime among the quadratic cyclotomics. -/
theorem levelSet_four_two_path_components {C : ℝ} (hC : 0 < C) (hC' : C < 1) :
    (∀ z ∈ Erdos1215.levelSet (cyclotomic 4 ℂ) C,
        JoinedIn (Erdos1215.levelSet (cyclotomic 4 ℂ) C) z Complex.I ∨
        JoinedIn (Erdos1215.levelSet (cyclotomic 4 ℂ) C) z (-Complex.I)) ∧
      ¬ JoinedIn (Erdos1215.levelSet (cyclotomic 4 ℂ) C) Complex.I (-Complex.I) := by
  rw [levelSet_cyclotomic_four_eq]
  exact quadratic_lemniscate_two_path_components hC
    (by rw [norm_I_sub_neg_I_sq]; linarith)

/-! ## Specialization `n = 6`: `Φ₆`, foci `ζ, ζ̄`, exactly two components for
`C < 3/4` -/

/-- **`{|Φ₆| < C}` has exactly two path components for `0 < C < 3/4`.** -/
theorem levelSet_six_two_path_components {C : ℝ} (hC : 0 < C)
    (hC' : C < 3 / 4) :
    (∀ z ∈ Erdos1215.levelSet (cyclotomic 6 ℂ) C,
        JoinedIn (Erdos1215.levelSet (cyclotomic 6 ℂ) C) z zeta6 ∨
        JoinedIn (Erdos1215.levelSet (cyclotomic 6 ℂ) C) z zeta6') ∧
      ¬ JoinedIn (Erdos1215.levelSet (cyclotomic 6 ℂ) C) zeta6 zeta6' := by
  rw [levelSet_cyclotomic_six_eq]
  exact quadratic_lemniscate_two_path_components hC
    (by rw [norm_zeta6_sub_sq]; linarith)

end CyclotomicPolynomialsOQ02OQ12
