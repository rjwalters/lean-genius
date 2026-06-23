/-
  Differential Entropy of the Uniform[a,b] Distribution

  OQ01-OQ01 from Shannon Entropy gallery (child of ShannonEntropyOQ01.lean,
  "Differential Entropy: Gibbs Inequality and Gaussian Maximum Entropy"):

  "Formalize the differential entropy of the Uniform[a,b] distribution:
   h = ln(b - a)."

  This is the textbook counterpart to the Gaussian computation in the parent
  file. The uniform density on [a,b] is f(x) = 1/(b-a) for x ∈ [a,b] and 0
  otherwise, encoded here as `Set.indicator (Set.Icc a b) (fun _ => 1/(b-a))`.

  Differential entropy (parent definition):
      h(f) = -∫ f(x) ln f(x) dx.

  The integrand f·ln f equals the constant (1/(b-a))·ln(1/(b-a)) on [a,b] and
  0 off it (the 0·ln 0 = 0 convention is automatic since Real.log 0 = 0).
  Integrating the constant over [a,b] (Lebesgue length b-a) gives
      ∫ f ln f = (b-a) · (1/(b-a)) · ln(1/(b-a)) = ln(1/(b-a)) = -ln(b-a),
  hence h = -(-ln(b-a)) = ln(b-a).

  In particular h < 0 for b - a < 1, illustrating that differential entropy
  (unlike discrete Shannon entropy) can be negative — the contrast noted in
  the parent file's preamble.

  Axioms: 0
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonEntropyOQ01

namespace DifferentialEntropy

open MeasureTheory Real Set

/-- Probability density of the Uniform[a,b] distribution:
    `f(x) = 1/(b-a)` on `[a,b]` and `0` elsewhere. -/
noncomputable def uniformPDF (a b : ℝ) (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc a b) (fun _ => 1 / (b - a)) x

/-- The uniform density integrates to 1, i.e. it is a genuine probability
    density. -/
theorem uniformPDF_integral_eq_one {a b : ℝ} (hab : a < b) :
    ∫ x, uniformPDF a b x = 1 := by
  have hpos : (0 : ℝ) < b - a := by linarith
  have hne : b - a ≠ 0 := ne_of_gt hpos
  unfold uniformPDF
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal hpos.le, smul_eq_mul, mul_one_div,
      div_self hne]

/-- Differential entropy of the Uniform[a,b] distribution is `ln(b - a)`. -/
theorem uniformDifferentialEntropy {a b : ℝ} (hab : a < b) :
    differentialEntropy (uniformPDF a b) = Real.log (b - a) := by
  have hpos : (0 : ℝ) < b - a := by linarith
  have hne : b - a ≠ 0 := ne_of_gt hpos
  -- The integrand `f·ln f` collapses to a constant supported on [a,b].
  have hkey :
      (fun x => uniformPDF a b x * Real.log (uniformPDF a b x))
        = Set.indicator (Set.Icc a b)
            (fun _ => (1 / (b - a)) * Real.log (1 / (b - a))) := by
    funext x
    unfold uniformPDF
    by_cases hx : x ∈ Set.Icc a b
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  -- Integrate the constant over [a,b] of Lebesgue length (b-a).
  have hint :
      ∫ x, uniformPDF a b x * Real.log (uniformPDF a b x) = -Real.log (b - a) := by
    rw [hkey, MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
        Real.volume_Icc, ENNReal.toReal_ofReal hpos.le, smul_eq_mul, one_div,
        Real.log_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  unfold differentialEntropy
  rw [hint, neg_neg]

/-- The uniform density is nonnegative. -/
theorem uniformPDF_nonneg {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 ≤ uniformPDF a b x := by
  have hpos : (0 : ℝ) < b - a := by linarith
  unfold uniformPDF
  rw [Set.indicator_apply]
  split_ifs with hx
  · positivity
  · exact le_refl 0

end DifferentialEntropy
