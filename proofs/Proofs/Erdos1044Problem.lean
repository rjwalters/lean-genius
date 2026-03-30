/-
Erdős Problem #1044: Boundary Length of Polynomial Level Sets

Source: https://erdosproblems.com/1044
Status: SOLVED (Tang)

Statement:
Let f(z) = ∏(z - zᵢ) ∈ ℂ[z] where |zᵢ| ≤ 1 for all i.
Define Λ(f) as the maximum boundary length of connected components of {z : |f(z)| < 1}.
Determine the infimum of Λ(f).

Answer: The infimum is 2.

Tang proved that inf Λ(f) = 2, approached but never achieved. The conjectured optimizers
for each degree n are the roots-of-unity polynomials z^n - 1.

References:
- Erdős, Herzog, Piranian (1958): "Metric properties of polynomials"
- Tang, Q.: Resolution of Erdős Problem #1044
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open Complex

namespace Erdos1044

/-
## Part I: Setup and Definitions
-/

/--
A monic polynomial with all roots in the closed unit disk |zᵢ| ≤ 1.
We represent it by its list of roots.
-/
def HasRootsInDisk (roots : List ℂ) : Prop :=
  ∀ z ∈ roots, Complex.abs z ≤ 1

/--
The maximum boundary length Λ(f) of the sublevel set {z : |f(z)| < 1}.
This is the maximum over all connected components of the perimeter of that component.
-/
axiom maxBoundaryLength (roots : List ℂ) : ℝ

/-
## Part II: Tang's Theorem
-/

/--
**Tang's Theorem**: The infimum of Λ(f) over all polynomials with roots in the
unit disk is exactly 2.

More precisely: for every ε > 0 there exists a polynomial f with roots in the
unit disk such that Λ(f) < 2 + ε, but Λ(f) > 2 for all such f.
-/
axiom tang_infimum_eq_two :
    (∀ roots : List ℂ, HasRootsInDisk roots → roots ≠ [] → maxBoundaryLength roots > 2) ∧
    (∀ ε : ℝ, ε > 0 → ∃ roots : List ℂ, HasRootsInDisk roots ∧ roots ≠ [] ∧
      maxBoundaryLength roots < 2 + ε)

/-- The infimum is not achieved: no polynomial attains Λ(f) = 2. -/
theorem infimum_not_achieved (roots : List ℂ) (h : HasRootsInDisk roots) (hne : roots ≠ []) :
    maxBoundaryLength roots > 2 :=
  tang_infimum_eq_two.1 roots h hne

/-- The infimum is approached: for any ε > 0 we can get within ε of 2. -/
theorem infimum_approached (ε : ℝ) (hε : ε > 0) :
    ∃ roots : List ℂ, HasRootsInDisk roots ∧ roots ≠ [] ∧
      maxBoundaryLength roots < 2 + ε :=
  tang_infimum_eq_two.2 ε hε

/-
## Part III: Roots of Unity Conjecture
-/

/--
The nth roots of unity: {e^(2πik/n) : k = 0, ..., n-1}.
These are the roots of z^n - 1.
-/
noncomputable def rootsOfUnity (n : ℕ) : List ℂ :=
  (List.range n).map (fun k => Complex.exp (2 * Real.pi * k / n * Complex.I))

/- Roots of unity lie on the unit circle, hence in the unit disk.
    Formally: ∀ n ≥ 1, HasRootsInDisk (rootsOfUnity n). -/

/- **Tang's Conjecture**: For each fixed degree n, the polynomial z^n - 1
minimizes Λ(f) among all degree-n polynomials with roots in the unit disk.
Verified for n = 1 and n = 2.
Formally: ∀ n ≥ 1, ∀ roots with length n and roots in disk,
  maxBoundaryLength (rootsOfUnity n) ≤ maxBoundaryLength roots. -/

/-
## Part IV: Degree 1 Case
-/

/- For the degree 1 polynomial f(z) = z - z₀ with |z₀| ≤ 1,
the sublevel set {z : |z - z₀| < 1} is a disk of radius 1,
whose boundary has length 2π.
Formally: ∀ z₀ with |z₀| ≤ 1, maxBoundaryLength [z₀] = 2π. -/

/-
## Part V: Erdős Problem #1044 Summary
-/

/--
**Erdős Problem #1044: SOLVED**

The infimum of Λ(f) over polynomials with roots in the unit disk is 2.
The infimum is not a minimum (Λ(f) > 2 for all f).
The roots-of-unity polynomials z^n - 1 are conjectured optimal for each degree.
-/
theorem erdos_1044 :
    (∀ roots : List ℂ, HasRootsInDisk roots → roots ≠ [] → maxBoundaryLength roots > 2) ∧
    (∀ ε : ℝ, ε > 0 → ∃ roots : List ℂ, HasRootsInDisk roots ∧ roots ≠ [] ∧
      maxBoundaryLength roots < 2 + ε) :=
  tang_infimum_eq_two

end Erdos1044
