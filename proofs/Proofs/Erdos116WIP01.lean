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

end UnitDiskPoly
