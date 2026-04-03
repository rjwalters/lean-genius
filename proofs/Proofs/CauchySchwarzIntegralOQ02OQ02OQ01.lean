/-
Cauchy-Schwarz Integral Chain — ENNReal rpow Division Step (OQ-02-OQ-02-OQ-01)

## Research Question

The Hölder → Minkowski derivation in OQ-02-OQ-02 uses
  `ENNReal.lintegral_Lp_add_le` as a black box for the final step:

  From:  ∫(f+g)^p ≤ (‖f‖_p + ‖g‖_p) · (∫(f+g)^p)^{(p-1)/p}
  Get:   (∫(f+g)^p)^{1/p} ≤ ‖f‖_p + ‖g‖_p

Can this "rpow division" step be proved explicitly?

## Answer

YES. The key is an abstract ENNReal cancellation lemma:

  If X ≤ C · X^q  with 0 ≤ q < 1 and X ≠ ⊤, then X^{1-q} ≤ C.

Proof: X = X^{1-q} · X^q (by rpow_add), so X^{1-q} · X^q ≤ C · X^q.
Cancel X^q (which is positive and finite since X ∈ (0, ⊤)).

Setting q = (p-1)/p gives 1 - q = 1/p, which is exactly the Minkowski step.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ENNReal
open scoped ENNReal NNReal

namespace CancellationStep

/-! ## Core Cancellation Lemma -/

/-- **ENNReal rpow cancellation** (the division step):
    If X ≤ C · X^q with 0 ≤ q < 1 and X ≠ ⊤, then X^{1-q} ≤ C.

    This is the abstract form of the final step in the Minkowski factoring trick:
    from ‖f+g‖_p^p ≤ (‖f‖_p + ‖g‖_p) · ‖f+g‖_p^{p-1}, conclude ‖f+g‖_p ≤ ‖f‖_p + ‖g‖_p.

    Proof: factor X = X^{1-q} · X^q, then cancel X^q from both sides. -/
theorem ennreal_rpow_cancel {X C : ℝ≥0∞} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hXfin : X ≠ ⊤)
    (h : X ≤ C * X ^ q) : X ^ (1 - q) ≤ C := by
  -- Case X = 0: 0^{1-q} = 0 ≤ C since 1-q > 0
  rcases eq_or_ne X 0 with rfl | hX0
  · simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < 1 - q)]
  -- Case 0 < X < ⊤
  have hXpos : 0 < X := lt_of_le_of_ne (zero_le X) (Ne.symm hX0)
  -- X^q is positive: using rpow_pos which needs both 0 < X and X ≠ ⊤
  have hXq_pos : 0 < X ^ q := ENNReal.rpow_pos hXpos hXfin
  -- X^q is finite: X ≠ 0, X ≠ ⊤ imply X^q ≠ ⊤ for any q
  have hXq_fin : X ^ q ≠ ⊤ := by
    intro heq
    simp [ENNReal.rpow_eq_top_iff, hX0, hXfin] at heq
  -- X^{1-q} · X^q = X (by rpow_add with explicit exponents)
  have key : X ^ (1 - q) * X ^ q = X := by
    have hrw : (1 : ℝ) - q + q = 1 := by ring
    rw [← ENNReal.rpow_add (1 - q) q hX0 hXfin, hrw, ENNReal.rpow_one]
  -- From key and h: X^{1-q} · X^q ≤ C · X^q
  have step : X ^ (1 - q) * X ^ q ≤ C * X ^ q := by
    calc X ^ (1 - q) * X ^ q = X := key
      _ ≤ C * X ^ q := h
  -- Cancel X^q from the right (it's nonzero and finite)
  exact (ENNReal.mul_le_mul_iff_left hXq_pos.ne' hXq_fin).mp step

/-! ## Application: Minkowski Division Step -/

/-- **Minkowski cancellation step**: Apply the abstract cancellation with q = (p-1)/p.

    In the Hölder → Minkowski derivation:
    - Let X = ∫(f+g)^p, A = (∫f^p)^{1/p}, B = (∫g^p)^{1/p}
    - The Hölder bound gives: X ≤ (A + B) · X^{(p-1)/p}
    - Cancellation gives:     X^{1/p} ≤ A + B

    The exponent identity: 1 - (p-1)/p = 1/p is the key arithmetic fact. -/
theorem minkowski_cancellation_step
    {p : ℝ} (hp : 1 < p)
    {X A B : ℝ≥0∞} (hXfin : X ≠ ⊤)
    (hbound : X ≤ (A + B) * X ^ ((p - 1) / p)) :
    X ^ (1 / p) ≤ A + B := by
  have hq0 : 0 ≤ (p - 1) / p := div_nonneg (by linarith) (by linarith)
  have hq1 : (p - 1) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  -- The exponent identity: 1 - (p-1)/p = 1/p
  have hexp : (1 : ℝ) - (p - 1) / p = 1 / p := by
    field_simp
    ring
  rw [← hexp]
  exact ennreal_rpow_cancel hq0 hq1 hXfin hbound

/-! ## Concrete verification -/

/-- The exponent identity that drives the Minkowski division step:
    1 - (p-1)/p = 1/p for p ≠ 0. -/
theorem minkowski_exponent_identity {p : ℝ} (hp : p ≠ 0) :
    (1 : ℝ) - (p - 1) / p = 1 / p := by
  field_simp [hp]; ring

/-- For p = 2: 1 - 1/2 = 1/2. -/
example : (1 : ℝ) - (2 - 1) / 2 = 1 / 2 := by norm_num

/-- For p = 3: 1 - 2/3 = 1/3. -/
example : (1 : ℝ) - (3 - 1) / 3 = 1 / 3 := by norm_num

end CancellationStep

end
