import Mathlib

/-! # Edge census for a three-level eigenvector

Let a regular graph carry an eigenvector with values in `{-1,0,1}`.  Write
`P,N,Z` for its positive, negative, and zero levels.  The four displayed
hypotheses below are exactly the sums of the eigenvector equation over `P`
and `N`, followed by the degree equations on those two levels.  This file
packages the division-free arithmetic consequence used by the order-64
`mu = 1`, eight-support analysis.

The masses are *oriented*: `iP` and `iN` count twice the internal edges of
`P` and `N`, while `x` counts the `P`--`N` edges once.  Thus no division by
two is hidden in the generic theorem.
-/

namespace Erdos85

/-- Generic three-level eigenvector edge census.  Equal positive and negative
support sizes force equal internal oriented edge mass and equal boundary mass
to the zero level. -/
theorem threeLevelEigenvector_edgeCensus
    (k mu r iP iN x bP bN : ℤ)
    (hP : iP - x = mu * r)
    (hN : x - iN = -mu * r)
    (hdegP : iP + x + bP = k * r)
    (hdegN : iN + x + bN = k * r) :
    iP = iN ∧
      x = iP - mu * r ∧
      bP = bN ∧
      bP = (k + mu) * r - 2 * iP := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- At defect degree seven, eigenvalue one, and a `4+ / 4-` support split,
the entire edge census is controlled by the number `e` of internal positive
edges.  Simplicity gives `e ≤ 6`; nonnegativity of the cross mass gives
`e ≥ 2`. -/
theorem sevenRegular_muOne_fourFour_edgeCensus
    (iP iN x bP bN : ℤ)
    (hP : iP - x = 4)
    (hN : x - iN = -4)
    (hdegP : iP + x + bP = 28)
    (hdegN : iN + x + bN = 28)
    (hiPEven : Even iP)
    (hiPUpper : iP ≤ 12)
    (hxNonneg : 0 ≤ x) :
    ∃ e : ℤ, 2 ≤ e ∧ e ≤ 6 ∧
      iP = 2 * e ∧ iN = 2 * e ∧
      x = 2 * e - 4 ∧
      bP = 32 - 4 * e ∧ bN = 32 - 4 * e := by
  obtain ⟨e, he⟩ := hiPEven
  have hcensus := threeLevelEigenvector_edgeCensus
    7 1 4 iP iN x bP bN hP hN hdegP hdegN
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he] at hP
    omega
  · rw [he] at hiPUpper
    omega
  · omega
  · rcases hcensus with ⟨hI, -, -, -⟩
    omega
  · rcases hcensus with ⟨-, hX, -, -⟩
    norm_num at hX
    omega
  · rcases hcensus with ⟨-, -, -, hB⟩
    norm_num at hB
    omega
  · rcases hcensus with ⟨-, -, hBN, hB⟩
    norm_num at hB
    omega

/-- The five possible parameter rows of the `mu=1`, eight-support census.
This is the exact finite menu consumed by subsequent structural arguments. -/
theorem sevenRegular_muOne_fourFour_edgeCensus_five_cases
    (iP iN x bP bN : ℤ)
    (hP : iP - x = 4)
    (hN : x - iN = -4)
    (hdegP : iP + x + bP = 28)
    (hdegN : iN + x + bN = 28)
    (hiPEven : Even iP)
    (hiPUpper : iP ≤ 12)
    (hxNonneg : 0 ≤ x) :
    (iP = 4 ∧ iN = 4 ∧ x = 0 ∧ bP = 24 ∧ bN = 24) ∨
    (iP = 6 ∧ iN = 6 ∧ x = 2 ∧ bP = 20 ∧ bN = 20) ∨
    (iP = 8 ∧ iN = 8 ∧ x = 4 ∧ bP = 16 ∧ bN = 16) ∨
    (iP = 10 ∧ iN = 10 ∧ x = 6 ∧ bP = 12 ∧ bN = 12) ∨
    (iP = 12 ∧ iN = 12 ∧ x = 8 ∧ bP = 8 ∧ bN = 8) := by
  obtain ⟨e, heLower, heUpper, rfl, rfl, rfl, rfl, rfl⟩ :=
    sevenRegular_muOne_fourFour_edgeCensus
      iP iN x bP bN hP hN hdegP hdegN hiPEven hiPUpper hxNonneg
  interval_cases e <;> norm_num

end Erdos85

#print axioms Erdos85.threeLevelEigenvector_edgeCensus
#print axioms Erdos85.sevenRegular_muOne_fourFour_edgeCensus
#print axioms Erdos85.sevenRegular_muOne_fourFour_edgeCensus_five_cases
