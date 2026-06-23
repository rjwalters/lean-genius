/-
  Aristotle targets for Erdos Problem #1132
  Routine supporting lemmas for automated proof search.
  See Erdos1132Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.Analysis.Calculus.LagrangeInterpolation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic

open Real Finset

namespace Erdos1132Aristotle

/-- Lagrange basis polynomial (product form). -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i : Fin n, if i = k then 1 else (x - nodes i) / (nodes k - nodes i)

/-- **Partition of unity for Lagrange basis polynomials.**
Standard polynomial identity: the Lagrange interpolant of the constant
function 1 is identically 1. Proof outline: for n distinct nodes,
P(x) = Σₖ lₖ(x) is a polynomial of degree ≤ n-1 that equals 1 at all
n nodes. By uniqueness of interpolation, P ≡ 1. -/
theorem lagrangeBasis_sum_eq_one {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j) :
    ∑ k : Fin n, lagrangeBasis nodes k x = 1 := by sorry

end Erdos1132Aristotle
