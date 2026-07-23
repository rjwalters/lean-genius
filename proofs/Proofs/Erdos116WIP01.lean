/-
# Erdős Problem #116 (Measure of Polynomial Sublevel Sets) — Topology of the lemniscate

Axiom-free foundational scaffolding for the objects defined in
`Proofs/Erdos116Problem.lean` (gallery `erdos-116`, the Erdős–Herzog–Piranian
conjecture, PROVED by Krishnapur–Lundberg–Ramachandran: for a monic degree-`n`
polynomial `p(z) = ∏(z - zᵢ)` with all roots in the closed unit disk, the
sublevel set `Sₚ = {z : |p(z)| < 1}` has area `≥ c/log n`).

The deep quantitative bounds (Pommerenke `c/n⁴`, KLR `c/log n`, KLR `C/log log n`,
Pólya `π`) rest on logarithmic-potential machinery not in Mathlib and stay in the
parent's header prose.  This file discharges **Key lemma 1** of the research task
— that the lemniscate `Sₚ` is *open* (hence measurable) and *bounded* — directly
from the root factorization, with no axioms and no `sorry`:

* `continuous_eval` — `z ↦ p(z) = ∏(z - zᵢ)` is continuous (a finite product of
  continuous factors);
* `isOpen_sublevelSet` — `Sₚ` is the preimage of the open ray `[0,1)` under the
  continuous map `z ↦ ‖p(z)‖`, hence open;
* `measurableSet_sublevelSet` — an open set is measurable;
* `sublevelSet_subset_closedBall` — `Sₚ ⊆ closedBall 0 2`: if `‖z‖ > 2` then each
  factor `‖z - zᵢ‖ ≥ ‖z‖ - 1 > 1`, so `‖p(z)‖ = ∏‖z - zᵢ‖ ≥ 1` and `z ∉ Sₚ`;
* `isBounded_sublevelSet` — hence `Sₚ` is bounded (`Bornology.IsBounded`).

These give exactly the well-definedness the parent's `sublevelMeasure` needs: `Sₚ`
is a bounded measurable set, so its 2D Lebesgue measure is finite.  The remaining
open content — the `c/log n` lower bound and the `1/log n` vs `1/log log n` gap —
is the genuinely deep KLR input, cleanly isolated.

All results are `0`-axiom / `0`-sorry.

Reference: <https://erdosproblems.com/116>
-/

import Proofs.Erdos116Problem

open MeasureTheory Metric

namespace UnitDiskPoly

variable {n : ℕ}

/-! ## Continuity of the polynomial map -/

/-- The evaluation map `z ↦ p(z) = ∏(z - zᵢ)` is continuous: it is a finite
product of the continuous factors `z ↦ z - zᵢ`. -/
theorem continuous_eval (P : UnitDiskPoly n) : Continuous P.eval := by
  unfold UnitDiskPoly.eval
  exact continuous_finsetProd _ (fun i _ => continuous_id.sub continuous_const)

/-! ## Openness and measurability of the sublevel set -/

/-- The sublevel set `Sₚ = {z : |p(z)| < 1}` is the preimage of the open ray
`Set.Iio 1` under the continuous map `z ↦ ‖p(z)‖`. -/
theorem sublevelSet_eq_preimage (P : UnitDiskPoly n) :
    P.sublevelSet = (fun z => ‖P.eval z‖) ⁻¹' Set.Iio 1 := by
  ext z
  simp only [UnitDiskPoly.sublevelSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
  rfl

/-- **`Sₚ` is open.**  It is the continuous preimage of the open set `[0, 1)`. -/
theorem isOpen_sublevelSet (P : UnitDiskPoly n) : IsOpen P.sublevelSet := by
  rw [P.sublevelSet_eq_preimage]
  exact isOpen_Iio.preimage (continuous_norm.comp P.continuous_eval)

/-- **`Sₚ` is measurable.**  An open set is measurable. -/
theorem measurableSet_sublevelSet (P : UnitDiskPoly n) :
    MeasurableSet P.sublevelSet :=
  P.isOpen_sublevelSet.measurableSet

/-! ## Boundedness of the sublevel set -/

/-- **`Sₚ ⊆ closedBall 0 2`.**  If `‖z‖ > 2` then, since every root has
`‖zᵢ‖ ≤ 1`, each factor satisfies `‖z - zᵢ‖ ≥ ‖z‖ - ‖zᵢ‖ ≥ ‖z‖ - 1 > 1`, so
`‖p(z)‖ = ∏ᵢ ‖z - zᵢ‖ ≥ 1` (product of factors each `≥ 1`) and `z ∉ Sₚ`.
The bound holds for every degree, including `n = 0` where `Sₚ = ∅`. -/
theorem sublevelSet_subset_closedBall (P : UnitDiskPoly n) :
    P.sublevelSet ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro z hz
  by_contra hout
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hout
  -- `hout : 2 < ‖z‖`; `hz : ‖p(z)‖ < 1`
  have hz' : ‖P.eval z‖ < 1 := hz
  have hge : (1 : ℝ) ≤ ‖P.eval z‖ := by
    rw [UnitDiskPoly.eval, norm_prod]
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ ∏ i : Fin n, ‖z - P.roots i‖ := by
          refine Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => ?_)
          have hri : ‖P.roots i‖ ≤ 1 := P.roots_in_disk i
          have hlow : ‖z‖ - ‖P.roots i‖ ≤ ‖z - P.roots i‖ :=
            norm_sub_norm_le z (P.roots i)
          linarith
  linarith

/-- **`Sₚ` is bounded** (`Bornology.IsBounded`): it sits inside `closedBall 0 2`. -/
theorem isBounded_sublevelSet (P : UnitDiskPoly n) :
    Bornology.IsBounded P.sublevelSet :=
  (Metric.isBounded_closedBall).subset P.sublevelSet_subset_closedBall

/-! ## Finiteness of the 2D Lebesgue measure

`Sₚ` is bounded and measurable, so its planar Lebesgue measure is finite.  This is
exactly the well-definedness the parent's `sublevelMeasure` needs: it is defined as the
`.toReal` of a `volume`, which is a faithful value (rather than the `⊤ ↦ 0` truncation)
only when that `volume` is finite. -/

/-- **`volume Sₚ < ⊤`** (`ℂ`-side).  `Sₚ ⊆ closedBall 0 2`, and a closed ball in the
proper space `ℂ` is compact, hence of finite volume. -/
theorem volume_sublevelSet_lt_top (P : UnitDiskPoly n) :
    volume P.sublevelSet < ⊤ :=
  measure_lt_top_of_subset P.sublevelSet_subset_closedBall
    (isCompact_closedBall (0 : ℂ) 2).measure_lt_top.ne

/-- The parent's `ℝ × ℝ` sublevel set is the preimage of `Sₚ ⊆ ℂ` under the measurable
equivalence `ℂ ≃ᵐ ℝ × ℝ` (its inverse `(a, b) ↦ a + b·I`). -/
theorem realProd_sublevelSet_eq_preimage (P : UnitDiskPoly n) :
    {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1}
      = Complex.measurableEquivRealProd.symm ⁻¹' P.sublevelSet := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage,
    Complex.measurableEquivRealProd_symm_apply]
  rfl

/-- **`sublevelMeasure` is well-defined: the parent's `ℝ × ℝ` measure is finite.**  Via
the volume-preserving equivalence `ℂ ≃ᵐ ℝ × ℝ`, the planar measure of the parent's
sublevel set equals `volume Sₚ`, which is finite by `volume_sublevelSet_lt_top`.  Hence
`sublevelMeasure P = (that volume).toReal` faithfully records the area of the lemniscate. -/
theorem volume_realProd_sublevelSet_lt_top (P : UnitDiskPoly n) :
    volume {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1} < ⊤ := by
  rw [P.realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage P.measurableSet_sublevelSet.nullMeasurableSet]
  exact P.volume_sublevelSet_lt_top

/-! ## Positivity of the 2D Lebesgue measure

For positive degree, `Sₚ` is a *nonempty open* set (it contains every root), and a
nonempty open set in the plane has strictly positive Lebesgue measure.  Combined with
finiteness this pins the volume in `(0, ⊤)`, so the parent's `sublevelMeasure` (a
`.toReal`) is not merely well-defined but genuinely **positive** — the lemniscate area
is a real nonzero quantity, never the `⊤ ↦ 0` truncation nor a degenerate `0`. -/

/-- **`0 < volume Sₚ`** (`ℂ`-side) for positive degree.  `Sₚ` is open
(`isOpen_sublevelSet`) and nonempty (`sublevelSet_nonempty`, it contains a root); a
nonempty open set has positive volume (`volume` is an open-positive measure on `ℂ`). -/
theorem volume_sublevelSet_pos (P : UnitDiskPoly n) (hn : 0 < n) :
    0 < volume P.sublevelSet :=
  (isOpen_sublevelSet P).measure_pos volume (P.sublevelSet_nonempty hn)

/-- **`0 < volume` of the parent's `ℝ × ℝ` sublevel set** for positive degree,
transported from the `ℂ`-side positivity across the volume-preserving equivalence
`ℂ ≃ᵐ ℝ × ℝ` (mirror of `volume_realProd_sublevelSet_lt_top`). -/
theorem volume_realProd_sublevelSet_pos (P : UnitDiskPoly n) (hn : 0 < n) :
    0 < volume {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1} := by
  rw [P.realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage P.measurableSet_sublevelSet.nullMeasurableSet]
  exact P.volume_sublevelSet_pos hn

/-- **The lemniscate area is strictly positive.**  For a positive-degree polynomial the
parent's `sublevelMeasure` — the `.toReal` of the planar volume of `{|p| < 1}` — is
`> 0`: the volume is positive (`volume_realProd_sublevelSet_pos`) and finite
(`volume_realProd_sublevelSet_lt_top`), so its `.toReal` is a genuine positive real.
Together with `sublevelMeasure_nonneg` this shows `0 < sublevelMeasure P` sharply. -/
theorem sublevelMeasure_pos (P : UnitDiskPoly n) (hn : 0 < n) :
    0 < sublevelMeasure P := by
  rw [sublevelMeasure]
  exact ENNReal.toReal_pos (P.volume_realProd_sublevelSet_pos hn).ne'
    (P.volume_realProd_sublevelSet_lt_top).ne

/-! ## Exact areas: the extremal configuration `p(z) = zⁿ` and degree one

The Erdős–Herzog–Piranian extremal candidate puts all `n` roots at the origin,
`p(z) = zⁿ`.  Its lemniscate is *exactly* the open unit disk — `‖zⁿ‖ = ‖z‖ⁿ < 1`
iff `‖z‖ < 1` — so its area is exactly `π` (`Complex.volume_ball`).  At degree
one every lemniscate is a unit disk `ball z₀ 1`, so the area is identically `π`
wherever the root sits.  These are the first *exact* area values in this
development: everything before only pinned `0 < area < ∞`.  In particular the
value `π` of the conjectured maximizer is attained at every degree `n ≥ 1`
(`exists_sublevelMeasure_eq_pi`), which is the "attainment" half of the sharp
Pólya-type upper bound `sublevelMeasure P ≤ π` (the other half is the deep
open content and stays out of this file). -/

/-- The extremal candidate: all `n` roots at the origin, so `p(z) = zⁿ`. -/
noncomputable def allRootsZero (n : ℕ) : UnitDiskPoly n :=
  ⟨fun _ => (0 : ℂ), fun _ => by simp [Complex.abs]⟩

/-- The extremal candidate evaluates to `p(z) = zⁿ`: a product of `n` copies of
the single factor `z - 0 = z`. -/
theorem eval_allRootsZero (n : ℕ) (z : ℂ) : (allRootsZero n).eval z = z ^ n := by
  simp [UnitDiskPoly.eval, allRootsZero, Finset.prod_const]

/-- **The extremal lemniscate is exactly the open unit disk.**  For `n ≠ 0`,
`{z : ‖zⁿ‖ < 1} = ball 0 1`, since `‖zⁿ‖ = ‖z‖ⁿ` and, for a nonnegative base,
`‖z‖ⁿ < 1 ↔ ‖z‖ < 1`. -/
theorem sublevelSet_allRootsZero (hn : n ≠ 0) :
    (allRootsZero n).sublevelSet = Metric.ball (0 : ℂ) 1 := by
  ext z
  constructor
  · intro hz
    have h1 : ‖(allRootsZero n).eval z‖ < 1 := hz
    rw [eval_allRootsZero, norm_pow] at h1
    rw [Metric.mem_ball, dist_zero_right]
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg z) hn).mp h1
  · intro hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    show ‖(allRootsZero n).eval z‖ < 1
    rw [eval_allRootsZero, norm_pow]
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg z) hn).mpr hz

/-- **`volume Sₚ = π` for the extremal candidate** (`ℂ`-side): the lemniscate is
the unit ball, whose planar volume is `π` (`Complex.volume_ball`). -/
theorem volume_sublevelSet_allRootsZero (hn : n ≠ 0) :
    volume ((allRootsZero n).sublevelSet) = NNReal.pi := by
  rw [sublevelSet_allRootsZero hn, Complex.volume_ball]
  simp

/-- The parent's `ℝ × ℝ` volume of the extremal lemniscate is `π`, transported
across the volume-preserving equivalence `ℂ ≃ᵐ ℝ × ℝ` (same route as
`volume_realProd_sublevelSet_lt_top`). -/
theorem volume_realProd_sublevelSet_allRootsZero (hn : n ≠ 0) :
    volume {p : ℝ × ℝ | Complex.abs ((allRootsZero n).eval ⟨p.1, p.2⟩) < 1}
      = NNReal.pi := by
  rw [(allRootsZero n).realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage (allRootsZero n).measurableSet_sublevelSet.nullMeasurableSet]
  exact volume_sublevelSet_allRootsZero hn

/-- **The conjectured maximizer has lemniscate area exactly `π`.**  The parent's
`sublevelMeasure` of `p(z) = zⁿ` is `π` on the nose for every `n ≠ 0` — the
first exact value of `sublevelMeasure` in this development. -/
theorem sublevelMeasure_allRootsZero (hn : n ≠ 0) :
    sublevelMeasure (allRootsZero n) = Real.pi := by
  rw [sublevelMeasure, volume_realProd_sublevelSet_allRootsZero hn]
  simp [NNReal.coe_real_pi]

/-- The degree-`1` polynomial `p(z) = z - z₀` with its single root `z₀` in the
closed unit disk. -/
noncomputable def singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) : UnitDiskPoly 1 :=
  ⟨fun _ => z₀, fun _ => hz₀⟩

/-- The degree-`1` polynomial evaluates to `z - z₀`. -/
theorem eval_singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) (z : ℂ) :
    (singleRoot z₀ hz₀).eval z = z - z₀ := by
  simp [UnitDiskPoly.eval, singleRoot]

/-- **Every degree-`1` lemniscate is a unit disk**: `{z : ‖z - z₀‖ < 1} = ball z₀ 1`. -/
theorem sublevelSet_singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) :
    (singleRoot z₀ hz₀).sublevelSet = Metric.ball z₀ 1 := by
  ext z
  constructor
  · intro hz
    have h1 : ‖(singleRoot z₀ hz₀).eval z‖ < 1 := hz
    rw [eval_singleRoot] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    exact h1
  · intro hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    show ‖(singleRoot z₀ hz₀).eval z‖ < 1
    rw [eval_singleRoot]
    exact hz

/-- `volume Sₚ = π` at degree `1` (`ℂ`-side), independent of the root. -/
theorem volume_sublevelSet_singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) :
    volume ((singleRoot z₀ hz₀).sublevelSet) = NNReal.pi := by
  rw [sublevelSet_singleRoot, Complex.volume_ball]
  simp

/-- The parent's `ℝ × ℝ` volume at degree `1` is `π`, transported across
`ℂ ≃ᵐ ℝ × ℝ` as above. -/
theorem volume_realProd_sublevelSet_singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) :
    volume {p : ℝ × ℝ | Complex.abs ((singleRoot z₀ hz₀).eval ⟨p.1, p.2⟩) < 1}
      = NNReal.pi := by
  rw [(singleRoot z₀ hz₀).realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage (singleRoot z₀ hz₀).measurableSet_sublevelSet.nullMeasurableSet]
  exact volume_sublevelSet_singleRoot z₀ hz₀

/-- **At degree `1` the lemniscate area is identically `π`**, wherever the root
sits in the closed unit disk: `sublevelMeasure (z - z₀) = π` for all `‖z₀‖ ≤ 1`.
So at degree one the area functional is *constant* — the extremal problem only
becomes nontrivial from degree `2` on. -/
theorem sublevelMeasure_singleRoot (z₀ : ℂ) (hz₀ : Complex.abs z₀ ≤ 1) :
    sublevelMeasure (singleRoot z₀ hz₀) = Real.pi := by
  rw [sublevelMeasure, volume_realProd_sublevelSet_singleRoot z₀ hz₀]
  simp [NNReal.coe_real_pi]

/-- **The conjectured extremal value `π` is attained at every degree `n ≥ 1`:**
some `UnitDiskPoly n` has lemniscate area exactly `π` (namely `p(z) = zⁿ`).
So the supremum of the area functional over `UnitDiskPoly n` is at least `π`,
and if the deep sharp upper bound `sublevelMeasure P ≤ π` holds, that supremum
equals `π` and is achieved. -/
theorem exists_sublevelMeasure_eq_pi (hn : n ≠ 0) :
    ∃ P : UnitDiskPoly n, sublevelMeasure P = Real.pi :=
  ⟨allRootsZero n, sublevelMeasure_allRootsZero hn⟩

/-! ## An explicit (exponentially weak) quantitative lower bound

Everything so far pins `0 < sublevelMeasure P < ∞` and the exact values of two
special families.  This section upgrades positivity to an *explicit* bound: the
lemniscate contains a disk of explicit radius around each root.

For `z` within `r ≤ 1` of a root `z₁`, every factor obeys
`‖z − zᵢ‖ ≤ ‖z − z₁‖ + ‖z₁‖ + ‖zᵢ‖ ≤ r + 2 ≤ 3`, while the distinguished factor is
`‖z − z₁‖ < r`.  Hence `‖p(z)‖ < r·3^{n−1}`, and the choice `r = 1/(2·3^{n−1})`
gives `‖p(z)‖ < 1/2`.  So `ball z₁ r ⊆ Sₚ` and

    `sublevelMeasure P ≥ π r² = π / (4·9^{n−1})`.

This is exponentially far from the deep Krishnapur–Lundberg–Ramachandran truth
`c / log n` (which stays open here), but it is the development's first
*quantitative* lower bound, and the containment `ball z₁ r ⊆ Sₚ` is of independent
use: the lemniscate has nonempty interior around every root, uniformly in the
configuration. -/

/-- **Near a root the polynomial is small.**  If `z` is within `1/(2·3^m)` of the
root `z₁ = P.roots 0` of a degree-`(m+1)` polynomial, then `‖p(z)‖ < 1/2`: the
distinguished factor is `< 1/(2·3^m)` and each of the other `m` factors is `≤ 3`. -/
theorem norm_eval_lt_half_of_mem_ball (P : UnitDiskPoly (m + 1)) {z : ℂ}
    (hz : z ∈ Metric.ball (P.roots 0) (1 / (2 * 3 ^ m))) :
    ‖P.eval z‖ < 1 / 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have heval : P.eval z = (z - P.roots 0) * ∏ i : Fin m, (z - P.roots i.succ) := by
    simp only [UnitDiskPoly.eval]
    exact Fin.prod_univ_succ _
  have hfac : ∀ i : Fin m, ‖z - P.roots i.succ‖ ≤ 3 := by
    intro i
    have h0 : ‖P.roots 0‖ ≤ 1 := P.roots_in_disk 0
    have hi : ‖P.roots i.succ‖ ≤ 1 := P.roots_in_disk i.succ
    have hrsmall : (1 : ℝ) / (2 * 3 ^ m) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h1 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      linarith
    calc ‖z - P.roots i.succ‖
        = ‖(z - P.roots 0) + (P.roots 0 - P.roots i.succ)‖ := by congr 1; ring
      _ ≤ ‖z - P.roots 0‖ + ‖P.roots 0 - P.roots i.succ‖ := norm_add_le _ _
      _ ≤ 1 / (2 * 3 ^ m) + (‖P.roots 0‖ + ‖P.roots i.succ‖) :=
          add_le_add hz.le (norm_sub_le _ _)
      _ ≤ 1 + (1 + 1) := add_le_add hrsmall (add_le_add h0 hi)
      _ = 3 := by norm_num
  have hprod : ‖∏ i : Fin m, (z - P.roots i.succ)‖ ≤ 3 ^ m := by
    rw [norm_prod]
    calc ∏ i : Fin m, ‖z - P.roots i.succ‖
        ≤ ∏ _i : Fin m, (3 : ℝ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hfac i)
      _ = 3 ^ m := by simp
  rw [heval, norm_mul]
  calc ‖z - P.roots 0‖ * ‖∏ i : Fin m, (z - P.roots i.succ)‖
      ≤ ‖z - P.roots 0‖ * 3 ^ m :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ < (1 / (2 * 3 ^ m)) * 3 ^ m :=
        mul_lt_mul_of_pos_right hz (by positivity)
    _ = 1 / 2 := by field_simp

/-- **The lemniscate contains an explicit disk around the first root**:
`ball z₁ (1/(2·3^m)) ⊆ Sₚ` for every degree-`(m+1)` configuration. -/
theorem ball_subset_sublevelSet (P : UnitDiskPoly (m + 1)) :
    Metric.ball (P.roots 0) (1 / (2 * 3 ^ m)) ⊆ P.sublevelSet := by
  intro z hz
  show ‖P.eval z‖ < 1
  exact lt_trans (norm_eval_lt_half_of_mem_ball P hz) (by norm_num)

/-- **Explicit volume lower bound (`ℂ`-side)**: the lemniscate's planar volume is at
least that of the contained disk, `π·(1/(2·3^m))²` (`Complex.volume_ball`). -/
theorem volume_sublevelSet_ge (P : UnitDiskPoly (m + 1)) :
    ENNReal.ofReal (1 / (2 * 3 ^ m) : ℝ) ^ 2 * NNReal.pi ≤ volume P.sublevelSet := by
  calc (ENNReal.ofReal (1 / (2 * 3 ^ m) : ℝ) ^ 2 * NNReal.pi : ℝ≥0∞)
      = volume (Metric.ball (P.roots 0) (1 / (2 * 3 ^ m))) := by
        rw [Complex.volume_ball]
    _ ≤ volume P.sublevelSet := measure_mono (ball_subset_sublevelSet P)

/-- The parent's `ℝ × ℝ` volume obeys the same explicit lower bound, transported
across the volume-preserving equivalence `ℂ ≃ᵐ ℝ × ℝ` (same route as
`volume_realProd_sublevelSet_lt_top`). -/
theorem volume_realProd_sublevelSet_ge (P : UnitDiskPoly (m + 1)) :
    ENNReal.ofReal (1 / (2 * 3 ^ m) : ℝ) ^ 2 * NNReal.pi
      ≤ volume {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1} := by
  rw [P.realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage P.measurableSet_sublevelSet.nullMeasurableSet]
  exact volume_sublevelSet_ge P

/-- **The first quantitative lower bound on the lemniscate area:**
`sublevelMeasure P ≥ π / (4·9^m)` for every degree-`(m+1)` configuration.
Exponentially weaker than the deep KLR bound `c / log n`, but fully elementary
and explicit. -/
theorem sublevelMeasure_ge (P : UnitDiskPoly (m + 1)) :
    Real.pi / (4 * 9 ^ m) ≤ sublevelMeasure P := by
  have h9 : ((3 : ℝ) ^ m) ^ 2 = 9 ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
  have hr2 : (1 / (2 * 3 ^ m) : ℝ) ^ 2 = 1 / (4 * 9 ^ m) := by
    rw [div_pow, one_pow, mul_pow, h9]; norm_num
  have hle := volume_realProd_sublevelSet_ge P
  have hfin := P.volume_realProd_sublevelSet_lt_top
  have h1 := ENNReal.toReal_mono hfin.ne hle
  rw [sublevelMeasure]
  refine le_trans (le_of_eq ?_) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.coe_toReal, NNReal.coe_real_pi, hr2]
  ring

/-- `sublevelMeasure_ge` in `n ≠ 0` form: `sublevelMeasure P ≥ π / (4·9^{n−1})`. -/
theorem sublevelMeasure_ge' (P : UnitDiskPoly n) (hn : n ≠ 0) :
    Real.pi / (4 * 9 ^ (n - 1)) ≤ sublevelMeasure P := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa using sublevelMeasure_ge P

end UnitDiskPoly
