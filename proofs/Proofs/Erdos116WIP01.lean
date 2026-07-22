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

/-! ## First quantitative bounds: `π / 9 ^ n ≤ sublevelMeasure P ≤ 4 · π`

Everything above pins `0 < sublevelMeasure P < ∞` and computes exact values at
special configurations, but gives no quantitative control for an *arbitrary*
`P : UnitDiskPoly n`.  This section proves the first two-sided quantitative
bounds — the same shape as the deep targets, with elementary constants:

* **Upper bound `4π`** (weak Pólya): `Sₚ ⊆ closedBall 0 2`
  (`sublevelSet_subset_closedBall`), and the disk of radius `2` has area `4π`.
  Pólya's sharp constant `π` needs potential theory and stays open here.
* **Lower bound `π/9ⁿ`** (weak Pommerenke): the ball of radius `3⁻ⁿ` around any
  root lies inside the lemniscate — for `z` in that ball the distinguished
  factor is `< 3⁻ⁿ`, while each of the `n - 1` other factors satisfies
  `‖z - zⱼ‖ ≤ ‖z - zᵢ‖ + ‖zᵢ - zⱼ‖ < 3⁻ⁿ + 2 ≤ 3`, so
  `‖p(z)‖ < 3⁻ⁿ · 3^(n-1) = 1/3 < 1`.  Hence `μ(Sₚ) ≥ π · 9⁻ⁿ`.

Pommerenke's `c/n⁴` and KLR's sharp `c/log n` require logarithmic potential
theory; `π/9ⁿ` is what the bare triangle inequality yields, and it is the first
positive quantitative lower bound in this development. -/

/-- **`sublevelMeasure` is the `toReal` of the `ℂ`-side lemniscate volume.**  The
parent's `ℝ × ℝ` sublevel set is the volume-preserving image of `Sₚ` under
`ℂ ≃ᵐ ℝ × ℝ`, so its measure agrees with `volume Sₚ`.  Deduplicates the transport
used in the exact-area computations above and lets the quantitative bounds below
work entirely on the `ℂ` side. -/
theorem sublevelMeasure_eq_toReal_volume (P : UnitDiskPoly n) :
    sublevelMeasure P = (volume P.sublevelSet).toReal := by
  rw [sublevelMeasure, P.realProd_sublevelSet_eq_preimage]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  rw [hmp.measure_preimage P.measurableSet_sublevelSet.nullMeasurableSet]

/-- **Weak Pólya upper bound: `sublevelMeasure P ≤ 4π`.**  The lemniscate sits
inside `closedBall 0 2` (`sublevelSet_subset_closedBall`), whose area is `4π`.
This is the first quantitative upper bound valid for every `P`; Pólya's sharp
constant `π` (attained by `zⁿ`, see `sublevelMeasure_allRootsZero`) is the deep
open content. -/
theorem sublevelMeasure_le_four_pi (P : UnitDiskPoly n) :
    sublevelMeasure P ≤ 4 * Real.pi := by
  rw [P.sublevelMeasure_eq_toReal_volume]
  have hfin : volume (Metric.closedBall (0 : ℂ) 2) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℂ) 2).measure_lt_top.ne
  have hmono : volume P.sublevelSet ≤ volume (Metric.closedBall (0 : ℂ) 2) :=
    measure_mono P.sublevelSet_subset_closedBall
  calc (volume P.sublevelSet).toReal
      ≤ (volume (Metric.closedBall (0 : ℂ) 2)).toReal := ENNReal.toReal_mono hfin hmono
    _ = 4 * Real.pi := by
        rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2), ENNReal.coe_toReal,
          NNReal.coe_real_pi]
        ring

/-- **A ball of radius `3⁻ⁿ` around any root lies inside the lemniscate.**  For
`z ∈ ball zᵢ 3⁻ⁿ`, split off the distinguished factor `‖z - zᵢ‖ < 3⁻ⁿ`; each of
the `n - 1` remaining factors satisfies
`‖z - zⱼ‖ ≤ ‖z - zᵢ‖ + ‖zᵢ - zⱼ‖ < 3⁻ⁿ + 2 ≤ 3`, so
`‖p(z)‖ < 3⁻ⁿ · 3^(n-1) = 1/3 < 1`.  (The argument `i : Fin n` forces `n ≥ 1`.) -/
theorem ball_subset_sublevelSet (P : UnitDiskPoly n) (i : Fin n) :
    Metric.ball (P.roots i) (1 / 3 ^ n) ⊆ P.sublevelSet := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  show ‖P.eval z‖ < 1
  rw [UnitDiskPoly.eval, norm_prod,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hrpos : (0:ℝ) < 3 ^ (m + 1) := by positivity
  have hr1 : (1:ℝ) / 3 ^ (m + 1) ≤ 1 := by
    rw [div_le_one hrpos]
    exact one_le_pow₀ (by norm_num)
  have hrest : ∏ j ∈ Finset.univ.erase i, ‖z - P.roots j‖ ≤ 3 ^ m := by
    have hcard : (Finset.univ.erase i).card = m := by
      simp [Finset.card_erase_of_mem]
    calc ∏ j ∈ Finset.univ.erase i, ‖z - P.roots j‖
        ≤ ∏ _j ∈ Finset.univ.erase i, (3:ℝ) := by
          refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
          have hij : ‖P.roots i - P.roots j‖ ≤ 2 := by
            have h1 : ‖P.roots i‖ ≤ 1 := P.roots_in_disk i
            have h2 : ‖P.roots j‖ ≤ 1 := P.roots_in_disk j
            calc ‖P.roots i - P.roots j‖
                ≤ ‖P.roots i‖ + ‖P.roots j‖ := norm_sub_le _ _
              _ ≤ 2 := by linarith
          calc ‖z - P.roots j‖
              = ‖(z - P.roots i) + (P.roots i - P.roots j)‖ := by
                rw [sub_add_sub_cancel]
            _ ≤ ‖z - P.roots i‖ + ‖P.roots i - P.roots j‖ := norm_add_le _ _
            _ ≤ 3 := by linarith
      _ = 3 ^ m := by rw [Finset.prod_const, hcard]
  have h3m : (0:ℝ) < 3 ^ m := by positivity
  calc ‖z - P.roots i‖ * ∏ j ∈ Finset.univ.erase i, ‖z - P.roots j‖
      ≤ ‖z - P.roots i‖ * 3 ^ m := mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
    _ < 1 / 3 ^ (m + 1) * 3 ^ m := mul_lt_mul_of_pos_right hz h3m
    _ = 1 / 3 := by
        have h3m' : (3:ℝ) ^ m ≠ 0 := ne_of_gt h3m
        rw [pow_succ]
        field_simp
    _ < 1 := by norm_num

/-- **Weak Pommerenke lower bound: `π / 9 ^ n ≤ sublevelMeasure P`.**  The
lemniscate contains a ball of radius `3⁻ⁿ` around each root
(`ball_subset_sublevelSet`), and that ball has area `π · 9⁻ⁿ`.  This is the
first positive quantitative lower bound valid for every `P` — exponentially
weaker than Pommerenke's `c/n⁴` and KLR's sharp `c/log n` (both requiring
potential theory), but fully machine-checked. -/
theorem pi_div_pow_le_sublevelMeasure (P : UnitDiskPoly n) (hn : 0 < n) :
    Real.pi / 9 ^ n ≤ sublevelMeasure P := by
  rw [P.sublevelMeasure_eq_toReal_volume]
  have hmono : volume (Metric.ball (P.roots ⟨0, hn⟩) (1 / 3 ^ n)) ≤ volume P.sublevelSet :=
    measure_mono (P.ball_subset_sublevelSet ⟨0, hn⟩)
  have hfin : volume P.sublevelSet ≠ ⊤ := P.volume_sublevelSet_lt_top.ne
  have hle := ENNReal.toReal_mono hfin hmono
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / 3 ^ n), ENNReal.coe_toReal,
    NNReal.coe_real_pi] at hle
  refine le_trans (le_of_eq ?_) hle
  have h32 : ((3:ℝ) ^ n) ^ 2 = 9 ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [div_pow, one_pow, h32]
  ring

/-- **First two-sided quantitative control of the lemniscate area:**
`π / 9ⁿ ≤ sublevelMeasure P ≤ 4π` for every degree-`n ≥ 1` polynomial with
roots in the closed unit disk.  The deep content of Erdős #116 is narrowing
this window to `[c / log n, π]` (KLR lower bound + Pólya upper bound). -/
theorem sublevelMeasure_mem_Icc (P : UnitDiskPoly n) (hn : 0 < n) :
    sublevelMeasure P ∈ Set.Icc (Real.pi / 9 ^ n) (4 * Real.pi) :=
  ⟨P.pi_div_pow_le_sublevelMeasure hn, P.sublevelMeasure_le_four_pi⟩

end UnitDiskPoly
