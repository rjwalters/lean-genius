/-
  Erdős Problem #1040, open question oq-03:
  Can the EHP (Erdős–Herzog–Piranian, 1958) result for discs and line segments
  be extended to convex sets, or to sets whose sublevel sets are well behaved?

  Source: https://erdosproblems.com/1040
  Parent status: OPEN

  Recall the setup (see Erdos1040Problem.lean). For a closed infinite F ⊆ ℂ,
      μ(F) = inf over monic polynomials f with roots in F of |{z : |f(z)| < 1}|,
  and the open conjecture asks whether μ(F) is governed by the transfinite
  diameter of F. The EHP answer is YES for line segments and discs.

  The "extend to convex sets" direction (oq-03) immediately runs into two
  concrete, fully verifiable facts, isolated here as base cases / obstructions:

  1. DEGREE-1 BASE CASE. The sublevel set of a linear polynomial z - a is
     exactly the open unit disc B(a, 1): it is convex and has Lebesgue measure
     π. Picking any root a ∈ F therefore yields the universal upper bound
         μ(F) ≤ π          for every nonempty F.
     This is the only degree at which the sublevel set is itself convex.

  2. DEGREE-2 OBSTRUCTION. Even when the roots lie in a *convex* set, the
     sublevel set need not be convex. For the polynomial (z-1)(z+1) = z² - 1,
     whose roots ±1 lie in the convex segment [-1, 1], both ±1 lie in the
     sublevel set while their midpoint 0 does not (|0² - 1| = 1 ≥ 1). Hence the
     sublevel set is genuinely non-convex. Any extension of the EHP argument to
     convex F must cope with non-convex sublevel sets already in degree 2.

  Everything below is elementary, axiom-free and sorry-free. The definitions are
  copied from Erdos1040Problem.lean to keep this file self-contained.
-/

import Mathlib

open scoped ENNReal NNReal
open MeasureTheory

namespace Erdos1040

/-
## Definitions (copied from Erdos1040Problem.lean for self-containment)
-/

/-- A polynomial f(z) = ∏ (z - rᵢ) with all roots in F. -/
structure PolynomialInF (F : Set ℂ) where
  /-- The degree (number of roots). -/
  degree : ℕ
  /-- The roots. -/
  roots : Fin degree → ℂ
  /-- All roots lie in F. -/
  roots_in_F : ∀ i, roots i ∈ F

variable {F : Set ℂ}

/-- Evaluate the polynomial at z. -/
noncomputable def PolynomialInF.eval (p : PolynomialInF F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet (p : PolynomialInF F) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/-- The Lebesgue measure of the sublevel set. -/
noncomputable def sublevelMeasure (p : PolynomialInF F) : ℝ≥0∞ :=
  volume (sublevelSet p)

/-- μ(F) restricted to polynomials of degree ≥ 1 (the mathematically correct
    definition; degree-0 polynomials give the empty sublevel set). -/
noncomputable def muPosDeg (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F) (_ : p.degree ≥ 1), sublevelMeasure p

/-
## Degree-1 base case: the sublevel set is the unit disc B(a, 1)
-/

/-- The linear polynomial with single root `a ∈ F`. -/
def linPoly (F : Set ℂ) (a : ℂ) (ha : a ∈ F) : PolynomialInF F where
  degree := 1
  roots := fun _ => a
  roots_in_F := fun _ => ha

@[simp] theorem linPoly_degree (a : ℂ) (ha : a ∈ F) :
    (linPoly F a ha).degree = 1 := rfl

/-- A linear polynomial evaluates to `z - a`. -/
theorem linPoly_eval (a : ℂ) (ha : a ∈ F) (z : ℂ) :
    (linPoly F a ha).eval z = z - a := by
  simp [PolynomialInF.eval, linPoly]

/-- The sublevel set of `z - a` is exactly the open unit disc centred at `a`. -/
theorem linPoly_sublevelSet (a : ℂ) (ha : a ∈ F) :
    sublevelSet (linPoly F a ha) = Metric.ball a 1 := by
  ext z
  simp only [sublevelSet, Set.mem_setOf_eq, linPoly_eval, Metric.mem_ball,
    dist_eq_norm]

/-- That sublevel set is convex (it is a metric ball). This is the *only*
    degree at which the sublevel set is guaranteed convex; see
    `quad_sublevelSet_not_convex`. -/
theorem linPoly_sublevelSet_convex (a : ℂ) (ha : a ∈ F) :
    Convex ℝ (sublevelSet (linPoly F a ha)) := by
  rw [linPoly_sublevelSet]
  exact convex_ball a 1

/-- The sublevel set of a linear polynomial has measure exactly π. -/
theorem linPoly_measure (a : ℂ) (ha : a ∈ F) :
    sublevelMeasure (linPoly F a ha) = (NNReal.pi : ℝ≥0∞) := by
  rw [sublevelMeasure, linPoly_sublevelSet, Complex.volume_ball]
  simp

/-- **Universal upper bound.** For any nonempty `F`, the degree-1 polynomial
    with a root in `F` witnesses `μ(F) ≤ π`. In particular `μ(F)` is always
    finite, independent of the transfinite diameter of `F`. -/
theorem muPosDeg_le_pi (hF : F.Nonempty) :
    muPosDeg F ≤ (NNReal.pi : ℝ≥0∞) := by
  obtain ⟨a, ha⟩ := hF
  have hdeg : (linPoly F a ha).degree ≥ 1 := by simp [linPoly_degree]
  calc muPosDeg F ≤ sublevelMeasure (linPoly F a ha) :=
        iInf₂_le (linPoly F a ha) hdeg
    _ = (NNReal.pi : ℝ≥0∞) := linPoly_measure a ha

/-
## Degree-2 obstruction: sublevel set is non-convex even for convex root sets

The roots ±1 lie in the convex segment [-1, 1] ⊆ ℂ, yet the sublevel set of
(z-1)(z+1) is not convex.
-/

/-- The quadratic `(z-1)(z+1) = z² - 1`, whose roots `±1` lie in the convex
    segment `[-1, 1]`. -/
def quadPoly : PolynomialInF (segment ℝ (-1 : ℂ) 1) where
  degree := 2
  roots := ![1, -1]
  roots_in_F := by
    intro i
    fin_cases i
    · simpa using right_mem_segment ℝ (-1 : ℂ) 1
    · simpa using left_mem_segment ℝ (-1 : ℂ) 1

/-- The quadratic evaluates to `(z - 1)(z + 1)`. -/
theorem quad_eval (z : ℂ) : quadPoly.eval z = (z - 1) * (z + 1) := by
  simp only [PolynomialInF.eval, quadPoly, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Both roots `±1` lie in the sublevel set (the value there is `0`). -/
theorem one_mem_quad_sublevel : (1 : ℂ) ∈ sublevelSet quadPoly := by
  show ‖quadPoly.eval 1‖ < 1
  rw [quad_eval]
  have : ((1 : ℂ) - 1) * (1 + 1) = 0 := by ring
  rw [this, norm_zero]; norm_num

theorem negOne_mem_quad_sublevel : (-1 : ℂ) ∈ sublevelSet quadPoly := by
  show ‖quadPoly.eval (-1)‖ < 1
  rw [quad_eval]
  have : ((-1 : ℂ) - 1) * (-1 + 1) = 0 := by ring
  rw [this, norm_zero]; norm_num

/-- The midpoint `0` of the two roots is **not** in the sublevel set
    (the value there is `-1`, of norm `1`). -/
theorem zero_not_mem_quad_sublevel : (0 : ℂ) ∉ sublevelSet quadPoly := by
  show ¬ ‖quadPoly.eval 0‖ < 1
  rw [quad_eval]
  have : ((0 : ℂ) - 1) * (0 + 1) = -1 := by ring
  rw [this]
  simp

/-- **Non-convexity obstruction.** Although the roots `±1` lie in the convex
    set `[-1, 1]`, the sublevel set `{z : |(z-1)(z+1)| < 1}` is not convex:
    it contains `±1` but not their midpoint `0`. -/
theorem quad_sublevelSet_not_convex :
    ¬ Convex ℝ (sublevelSet quadPoly) := by
  intro hconv
  -- Convexity would force the midpoint of `1` and `-1` into the set.
  have hmid := hconv one_mem_quad_sublevel negOne_mem_quad_sublevel
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hzero : ((1 / 2 : ℝ) • (1 : ℂ) + (1 / 2 : ℝ) • (-1 : ℂ)) = 0 := by
    simp [Complex.real_smul]
  rw [hzero] at hmid
  exact zero_not_mem_quad_sublevel hmid

end Erdos1040
