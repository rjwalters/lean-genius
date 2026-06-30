import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Geometric Series at the Boundary: Abel Summability

## What This Proves
The parent entry (`geometric-series-oq-01`) studies the geometric series ∑ rⁿ at
the critical boundary |r| = 1. There, ordinary convergence fails, but the
**Cesàro mean** of Grandi's series 1 − 1 + 1 − 1 + ⋯ still converges to 1/2.

This entry develops the **third regularization lens** at the boundary:
**Abel summability**. A sequence (aₙ) is Abel summable to L when the power
series A(x) = ∑ₙ aₙ xⁿ converges for x ∈ [0,1) and A(x) → L as x → 1⁻.

We prove:

1. **Grandi is Abel summable to 1/2.** The Abel function of (−1)ⁿ is
   ∑ₙ (−1)ⁿ xⁿ = 1/(1+x), whose left-limit at 1 is 1/2 — recovering Euler's
   value and agreeing with the Cesàro sum from the parent.

2. **r = 1 is NOT Abel summable.** The Abel function of the constant 1 is
   ∑ₙ xⁿ = 1/(1−x), which diverges to +∞ as x → 1⁻. So Abel summability still
   separates r = 1 (genuinely divergent) from r = −1 (summable to 1/2),
   refining the parent's blanket "|r| ≥ 1 ⇒ not summable".

3. **Abel summability is regular.** For |r| < 1 the Abel function
   ∑ₙ rⁿ xⁿ = 1/(1−rx) tends to 1/(1−r) as x → 1⁻ — exactly the ordinary sum.
   So Abel summation never contradicts ordinary convergence; it only extends it.

## Historical Context
Niels Henrik Abel proved (1826) that if ∑ aₙ converges to L then the power
series ∑ aₙ xⁿ tends to L as x → 1⁻ (Abel's theorem); the converse defines Abel
summation. Like Cesàro's method, Abel's is *regular* (consistent with ordinary
sums) and assigns 1/2 to Grandi's series. The two methods agree here, but Abel's
is strictly stronger in general (Abel summable ⊋ Cesàro summable, by Frobenius).

## Approach
- **Foundation (from Mathlib):** `hasSum_geometric_of_abs_lt_one` gives the
  closed form of each Abel function for |x| < 1.
- **Original Contributions:** the Abel-summability predicate at the boundary, the
  three boundary outcomes (Grandi → 1/2, r = 1 → divergent, |r| < 1 regular),
  with the left-limits computed by continuity / `tendsto_inv_nhdsGT_zero`.
-/

namespace GeometricSeriesOQ01OQ03

open Filter Topology

/-- Near `1` from below, points have absolute value `< 1`. -/
private theorem abs_lt_one_eventually : ∀ᶠ x in 𝓝[<] (1 : ℝ), |x| < 1 := by
  have h1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), x < 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx; exact hx
  have hopen : IsOpen {x : ℝ | (-1 : ℝ) < x} := isOpen_lt continuous_const continuous_id
  have h2 : ∀ᶠ x in 𝓝[<] (1 : ℝ), (-1 : ℝ) < x :=
    (hopen.eventually_mem (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with x hx1 hx2
  exact abs_lt.mpr ⟨hx2, hx1⟩

-- ============================================================
-- PART 0: The Abel-summability predicate
-- ============================================================

/-- A real sequence `a` is **Abel summable** to `L` when its power series
`A(x) = ∑ₙ aₙ xⁿ` converges for every `x ∈ [0,1)` and its value tends to `L`
as `x → 1⁻`. This is the boundary regularization studied here. -/
def AbelSummableTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ x : ℝ, 0 ≤ x → x < 1 → Summable (fun n => a n * x ^ n)) ∧
    Tendsto (fun x => ∑' n, a n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 L)

/-- The Abel sum is unique: a sequence cannot be Abel summable to two distinct
values (the left-neighborhood filter at `1` is nontrivial). -/
theorem abelSummableTo_unique {a : ℕ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : AbelSummableTo a L₁) (h₂ : AbelSummableTo a L₂) : L₁ = L₂ :=
  tendsto_nhds_unique h₁.2 h₂.2

-- ============================================================
-- PART 1: Grandi's series 1 − 1 + 1 − 1 + ⋯ is Abel summable to 1/2
-- ============================================================

/-- For `|x| < 1`, the Abel function of Grandi's series sums in closed form:
`∑ₙ (−1)ⁿ xⁿ = 1/(1+x)`. -/
theorem grandi_abel_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => (-1 : ℝ) ^ n * x ^ n) (1 + x)⁻¹ := by
  have key : HasSum (fun n => (-x) ^ n) (1 - (-x))⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by rwa [abs_neg])
  rw [sub_neg_eq_add] at key
  have e : (fun n => (-1 : ℝ) ^ n * x ^ n) = fun n => (-x) ^ n := by
    funext n; rw [← mul_pow, neg_one_mul]
  rw [e]; exact key

/-- The Abel function of Grandi's series tends to `1/2` as `x → 1⁻`:
the Abel sum of `1 − 1 + 1 − ⋯` is `1/2`, matching Euler and the Cesàro mean. -/
theorem grandi_abel_tendsto :
    Tendsto (fun x => ∑' n, (-1 : ℝ) ^ n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2)) := by
  have hcont : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2)) := by
    have htend : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝 (1 : ℝ)) (𝓝 (1 / 2)) := by
      have h2 : ((1 : ℝ) + 1)⁻¹ = 1 / 2 := by norm_num
      rw [← h2]
      exact ((continuous_const.add continuous_id).tendsto 1).inv₀ (by norm_num)
    exact htend.mono_left nhdsWithin_le_nhds
  refine hcont.congr' ?_
  filter_upwards [abs_lt_one_eventually] with x hx
  exact ((grandi_abel_hasSum hx).tsum_eq).symm

/-- Grandi's series `1 − 1 + 1 − 1 + ⋯` is Abel summable to `1/2`. -/
theorem grandi_abelSummableTo_half :
    AbelSummableTo (fun n => (-1 : ℝ) ^ n) (1 / 2) := by
  refine ⟨fun x hx0 hx1 => ?_, grandi_abel_tendsto⟩
  have hx : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  exact (grandi_abel_hasSum hx).summable

-- ============================================================
-- PART 2: r = 1 is NOT Abel summable (the Abel function diverges)
-- ============================================================

/-- The Abel function of the constant sequence `1` diverges to `+∞` as `x → 1⁻`:
`∑ₙ xⁿ = 1/(1−x) → +∞`. -/
theorem one_abel_tendsto_atTop :
    Tendsto (fun x => ∑' n, (1 : ℝ) ^ n * x ^ n) (𝓝[<] (1 : ℝ)) atTop := by
  have hbase : Tendsto (fun x : ℝ => (1 - x)⁻¹) (𝓝[<] (1 : ℝ)) atTop := by
    have h0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto (fun x : ℝ => (1 : ℝ) - x) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Iio] at hx
        simp only [Set.mem_Ioi]; linarith
    exact h0.inv_tendsto_nhdsGT_zero
  refine hbase.congr' ?_
  filter_upwards [abs_lt_one_eventually] with x hx
  have hs : HasSum (fun n => (1 : ℝ) ^ n * x ^ n) (1 - x)⁻¹ := by
    have key : HasSum (fun n => x ^ n) (1 - x)⁻¹ := hasSum_geometric_of_abs_lt_one hx
    simpa using key
  exact hs.tsum_eq.symm

/-- The constant sequence `1` (i.e. `r = 1`) is not Abel summable to any value:
its Abel function diverges, so no finite limit exists. -/
theorem one_not_abelSummable : ¬ ∃ L, AbelSummableTo (fun _ => (1 : ℝ)) L := by
  rintro ⟨L, _, hL⟩
  have hAt : Tendsto (fun x => ∑' n, (1 : ℝ) * x ^ n) (𝓝[<] (1 : ℝ)) atTop := by
    refine one_abel_tendsto_atTop.congr ?_
    intro x; simp
  have : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
  exact not_tendsto_nhds_of_tendsto_atTop hAt L hL

-- ============================================================
-- PART 3: Abel summability is regular (|r| < 1 ⇒ Abel sum = ordinary sum)
-- ============================================================

/-- For `|r·x| < 1`, the Abel function of the geometric sequence `rⁿ` sums to
`1/(1−r·x)`. -/
theorem geom_abel_hasSum {r x : ℝ} (h : |r * x| < 1) :
    HasSum (fun n => r ^ n * x ^ n) (1 - r * x)⁻¹ := by
  have key : HasSum (fun n => (r * x) ^ n) (1 - r * x)⁻¹ :=
    hasSum_geometric_of_abs_lt_one h
  have e : (fun n => r ^ n * x ^ n) = fun n => (r * x) ^ n := by
    funext n; rw [mul_pow]
  rw [e]; exact key

/-- For `|r| < 1`, the Abel function of `rⁿ` tends to `1/(1−r)` as `x → 1⁻`. -/
theorem geom_abel_tendsto {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun x => ∑' n, r ^ n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 (1 - r)⁻¹) := by
  have hr1 : r < 1 := (abs_lt.mp hr).2
  have hcont : Tendsto (fun x : ℝ => (1 - r * x)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (1 - r)⁻¹) := by
    have hpos : (0 : ℝ) < 1 - r * 1 := by rw [mul_one]; linarith
    have htend : Tendsto (fun x : ℝ => (1 - r * x)⁻¹) (𝓝 (1 : ℝ))
        (𝓝 (1 - r * 1)⁻¹) :=
      ((continuous_const.sub (continuous_const.mul continuous_id)).tendsto 1).inv₀ hpos.ne'
    rw [mul_one] at htend
    exact htend.mono_left nhdsWithin_le_nhds
  refine hcont.congr' ?_
  filter_upwards [abs_lt_one_eventually] with x hx
  have hrx : |r * x| < 1 := by
    rw [abs_mul]
    calc |r| * |x| ≤ |r| * 1 := mul_le_mul_of_nonneg_left (le_of_lt hx) (abs_nonneg r)
      _ = |r| := mul_one _
      _ < 1 := hr
  exact ((geom_abel_hasSum hrx).tsum_eq).symm

/-- For `|r| < 1`, the geometric sequence `rⁿ` is Abel summable to `1/(1−r)`. -/
theorem geom_abelSummableTo {r : ℝ} (hr : |r| < 1) :
    AbelSummableTo (fun n => r ^ n) (1 - r)⁻¹ := by
  refine ⟨fun x hx0 hx1 => ?_, geom_abel_tendsto hr⟩
  have hrx : |r * x| < 1 := by
    rw [abs_mul]
    have hx : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact le_of_lt hx1
    calc |r| * |x| ≤ |r| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg r)
      _ = |r| := mul_one _
      _ < 1 := hr
  exact (geom_abel_hasSum hrx).summable

/-- **Regularity of Abel summation.** For `|r| < 1` the Abel sum of `rⁿ` equals
its *ordinary* sum `∑ₙ rⁿ`. Abel summation extends ordinary convergence without
ever contradicting it. -/
theorem geom_abel_regular {r : ℝ} (hr : |r| < 1) :
    AbelSummableTo (fun n => r ^ n) (∑' n, r ^ n) := by
  have h : (∑' n, r ^ n) = (1 - r)⁻¹ := (hasSum_geometric_of_abs_lt_one hr).tsum_eq
  rw [h]; exact geom_abelSummableTo hr

end GeometricSeriesOQ01OQ03
