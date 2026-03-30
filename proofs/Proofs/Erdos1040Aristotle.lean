/-
  Aristotle targets for Erdős Problem #1040
  Routine supporting lemmas for automated proof search.
  See Erdos1040Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, non-negativity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos1040

/-
## Definitions (copied from Erdos1040Problem.lean for self-containment)
-/

/-- The n-th diameter of a set F.
    The product is over all pairs (i, j) with j < i < n. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ (pts : Fin n → ℂ), (∀ i, pts i ∈ F) ∧
    x = (∏ i : Fin n, (Finset.Iio i).prod fun j =>
      ‖pts i - pts j‖) ^ (2 / (n * (n - 1 : ℝ)))}

/-- The transfinite diameter (logarithmic capacity) of F. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  ⨅ n : ℕ, nthDiameter F n

/-- A polynomial with roots in F. -/
structure PolynomialInF (F : Set ℂ) where
  degree : ℕ
  roots : Fin degree → ℂ
  roots_in_F : ∀ i, roots i ∈ F

variable {F : Set ℂ}

noncomputable def PolynomialInF.eval (p : PolynomialInF F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

def sublevelSet (p : PolynomialInF F) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

noncomputable def sublevelMeasure (p : PolynomialInF F) : ENNReal :=
  MeasureTheory.volume (sublevelSet p)

noncomputable def mu (F : Set ℂ) : ENNReal :=
  ⨅ (p : PolynomialInF F), sublevelMeasure p

/-- Corrected μ(F): infimum over polynomials of degree ≥ 1. -/
noncomputable def muPosDeg (F : Set ℂ) : ENNReal :=
  ⨅ (p : PolynomialInF F) (_ : p.degree ≥ 1), sublevelMeasure p

/-
PROBLEM
## Aristotle targets: basic properties of transfinite diameter

These are standard results in potential theory (Fekete 1923, Ransford 1995).

Each nthDiameter is non-negative: sSup of non-negative reals ≥ 0.

PROVIDED SOLUTION
Unfold nthDiameter. It's sSup of a set of reals. If the set is empty or not bounded above, sSup returns 0, which is ≥ 0. If nonempty and bounded above, each element is rpow of a product of norms (nonneg), so nonneg, and sSup of nonneg set is nonneg. Use Real.sSup_nonneg or csSup_nonneg.
-/
theorem nthDiameter_nonneg (F : Set ℂ) (n : ℕ) : 0 ≤ nthDiameter F n := by
  apply_rules [ Real.sSup_nonneg ];
  rintro x ⟨ pts, hpts, rfl ⟩ ; exact Real.rpow_nonneg ( Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _ ) _;

/-
PROBLEM
Transfinite diameter is non-negative: iInf of non-negative values ≥ 0.

PROVIDED SOLUTION
Unfold transfiniteDiameter. It's iInf of nthDiameter values which are all nonneg by nthDiameter_nonneg. Use le_ciInf or Real.iInf_nonneg or similar.
-/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  exact le_ciInf fun n => nthDiameter_nonneg F n |> le_trans ( by norm_num ) |> le_trans <| le_rfl;

/-
PROBLEM
The uncorrected mu is always 0 (degree-0 bug: constant polynomial 1 has empty sublevel set).
    This makes mu_infimum trivially true. The meaningful version uses muPosDeg (degree ≥ 1).

PROVIDED SOLUTION
Construct the degree-0 polynomial p0 := ⟨0, Fin.elim0, fun i => i.elim0⟩. Then mu F ≤ sublevelMeasure p0 by iInf_le. The sublevel set of p0 is {z | ‖∏ i : Fin 0, ...‖ < 1} = {z | ‖1‖ < 1} = ∅ since ‖1‖ = 1 and 1 < 1 is false. So sublevelMeasure p0 = volume ∅ = 0. Combined with 0 ≤ mu F (bot_le), we get mu F = 0.
-/
theorem mu_eq_zero (F : Set ℂ) : mu F = 0 := by
  refine' le_antisymm _ _;
  · refine' le_trans ( ciInf_le _ _ ) _ <;> norm_num;
    refine' ⟨ 0, fun _ => 0, _ ⟩;
    all_goals norm_num [ sublevelMeasure, sublevelSet ];
    unfold PolynomialInF.eval; norm_num;
  · exact zero_le _

/-
PROBLEM
μ(F) is achieved or approached for infinite F.
    Trivially true because mu F = 0 (degree-0 bug).

PROVIDED SOLUTION
Rewrite mu F to 0 using mu_eq_zero. Then we need to find p with sublevelMeasure p < ε. Use the degree-0 polynomial p0 := ⟨0, Fin.elim0, fun i => i.elim0⟩. Its sublevel measure is 0 (same argument as in mu_eq_zero). 0 < ε follows from hε after appropriate coercion (zero_add, and the fact that (0 : ENNReal) < ε when ε > 0).
-/
theorem mu_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε > 0, ∃ (p : PolynomialInF F), sublevelMeasure p < mu F + ε := by
  intro ε hε_pos
  use ⟨0, Fin.elim0, fun i => by fin_cases i⟩;
  refine' lt_of_le_of_lt _ ( ENNReal.add_lt_add_left _ hε_pos );
  · unfold sublevelMeasure sublevelSet; norm_num;
    unfold PolynomialInF.eval; norm_num;
  · rw [ mu_eq_zero ] ; norm_num

end Erdos1040