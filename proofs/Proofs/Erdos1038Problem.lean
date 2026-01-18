/-
Erdős Problem #1038: Sublevel Sets of Monic Polynomials

Determine the infimum and supremum of |{x ∈ ℝ : |f(x)| < 1}| as f ranges over all
non-constant monic polynomials whose roots are all real and contained in [-1,1].

**Answer**:
  - Supremum = 2√2 ≈ 2.828 (proved by Tao, 2025)
  - Infimum: 2^(4/3) - 1 ≈ 1.519 ≤ inf ≤ 1.835 (bounds known, exact value open)

This problem was posed by Erdős, Herzog, and Piranian in 1958. They proved the
supremum bound under the restriction that roots lie in {-1, 1}, conjecturing it
is optimal for roots in [-1, 1]. Terence Tao confirmed this in December 2025.

References:
  - https://erdosproblems.com/1038
  - Erdős, Herzog, Piranian. Metric properties of polynomials. J. Analyse Math. (1958)
  - Tao. Sublevel Sets of Logarithmic Potentials. Terry Tao's Blog (Dec 2025)
-/

import Mathlib

open scoped Real ENNReal
open MeasureTheory Polynomial

namespace Erdos1038

/-
## Definitions

We study the Lebesgue measure of the sublevel set {x ∈ ℝ : |f(x)| < 1} for monic
polynomials with real roots in [-1, 1].
-/

/-- A monic polynomial with all roots real and in [-1, 1]. -/
def MonicRealRootedIn01 (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1)

/-- The sublevel set {x ∈ ℝ : |f(x)| < 1}. -/
def sublevelSet (f : Polynomial ℝ) : Set ℝ :=
  {x | |f.eval x| < 1}

/-- Measure of the sublevel set. -/
noncomputable def sublevelMeasure (f : Polynomial ℝ) : ℝ≥0∞ :=
  volume (sublevelSet f)

/-
## Supremum Result

The supremum equals 2√2, achieved in the limit by polynomials approaching
(x - 1)(x + 1). This was conjectured by Erdős-Herzog-Piranian (1958) and
proved by Terence Tao in December 2025.
-/

/-- The supremum of sublevel set measures for monic polynomials with roots in [-1,1]
    equals 2√2 ≈ 2.828. Proved by Tao (2025).

    Proof requires logarithmic potential theory beyond current Mathlib.
    See: Tao, "Sublevel Sets of Logarithmic Potentials" (2025) -/
axiom erdos_1038_supremum :
    (⨆ f : {f : Polynomial ℝ // f.Monic ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
      volume {x | |f.1.eval x| < 1}) = ENNReal.ofReal (2 * Real.sqrt 2)

/-
## Infimum Bounds

The exact infimum remains an open problem. Current best bounds:
  - Lower bound: 2^(4/3) - 1 ≈ 1.519
  - Upper bound: 1.835 (witnessed by specific polynomial constructions)
-/

/-- Lower bound on the infimum: at least 2^(4/3) - 1 ≈ 1.519.
    Proved using logarithmic potential theory. -/
axiom erdos_1038_inf_lowerBound :
    ENNReal.ofReal (2 ^ (4 / 3 : ℝ) - 1) ≤
      ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
        (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
        volume {x | |f.1.eval x| < 1}

/-- Upper bound on the infimum: less than 1.835.
    Witnessed by explicit polynomial constructions. -/
axiom erdos_1038_inf_upperBound :
    ⨅ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
      (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
      volume {x | |f.1.eval x| < 1} < ENNReal.ofReal 1.835

/-
## Concrete Examples

The polynomial (x+1)(x-1)^m for m ≥ 3 witnesses that the infimum is < 2.
This was noted in the original 1958 paper by Erdős-Herzog-Piranian.

The quadratic polynomial x² - 1 = (x-1)(x+1) has sublevel set
{x : |x² - 1| < 1} = {x : 0 < x² < 2} = (-√2, 0) ∪ (0, √2)
with measure 2√2, achieving the supremum.
-/

/-- The polynomial (x+1)(x-1)^m for m ≥ 3 witnesses that the infimum is < 2. -/
axiom infimum_less_than_two :
    ∃ f : Polynomial ℝ, f.Monic ∧ f ≠ 1 ∧
      (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1) ∧
      volume {x | |f.eval x| < 1} < 2

/-- The quadratic x² - 1 achieves sublevel measure 2√2. -/
axiom quadratic_achieves_supremum :
    volume {x : ℝ | |x^2 - 1| < 1} = ENNReal.ofReal (2 * Real.sqrt 2)

/-
## Numerical Bounds

The key numerical values:
  - 2^(4/3) - 1 ≈ 1.5198...
  - 2√2 ≈ 2.8284...
-/

end Erdos1038
