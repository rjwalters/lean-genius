import Proofs.Erdos85CycleDefectMinpolyRegistry
import Proofs.Erdos85CycleDefectRootTransport

/-! # Uniform primary classification for H16 cycle roots -/

open Polynomial

namespace Erdos85

noncomputable section

/-- The complete list of rational and nonlinear minimal polynomials reached
from cycle orders occurring in a C4-free two-factor of order sixteen. -/
def OrderSixteenCycleDefectPrimaryClass (μ : AlgebraicClosure ℚ) : Prop :=
  minpoly ℚ μ = X - C 3 ∨
  minpoly ℚ μ = X - C 5 ∨
  minpoly ℚ μ = X - C 6 ∨
  minpoly ℚ μ = X - C 7 ∨
  minpoly ℚ μ = cycleDefectQuadraticFive.map (Int.castRingHom ℚ) ∨
  minpoly ℚ μ = cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ) ∨
  minpoly ℚ μ = cycleDefectCubicSeven.map (Int.castRingHom ℚ) ∨
  minpoly ℚ μ = cycleDefectCubicNine.map (Int.castRingHom ℚ) ∨
  minpoly ℚ μ = cycleDefectQuinticEleven.map (Int.castRingHom ℚ) ∨
  minpoly ℚ μ = cycleDefectSexticThirteen.map (Int.castRingHom ℚ)

/-- Exactly the cycle orders which occur among the twelve C4-free
partitions of sixteen. -/
def OrderSixteenCycleOrder (r : ℕ) : Prop :=
  r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨
  r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 13 ∨ r = 16

private theorem primaryClass_of_eq_three
    {μ : AlgebraicClosure ℚ} (hμ : μ = 3) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  subst μ
  left
  exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (3 : ℚ)

private theorem primaryClass_of_eq_five
    {μ : AlgebraicClosure ℚ} (hμ : μ = 5) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  subst μ
  right; left
  exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (5 : ℚ)

private theorem primaryClass_of_eq_six
    {μ : AlgebraicClosure ℚ} (hμ : μ = 6) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  subst μ
  right; right; left
  exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (6 : ℚ)

private theorem primaryClass_of_eq_seven
    {μ : AlgebraicClosure ℚ} (hμ : μ = 7) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  subst μ
  right; right; right; left
  exact minpoly.eq_X_sub_C (AlgebraicClosure ℚ) (7 : ℚ)

private theorem primaryClass_of_quadraticFive
    {μ : AlgebraicClosure ℚ} (hμ : μ ^ 2 - 11 * μ + 29 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; left
  exact (cycleDefectQuadraticFive_eq_minpoly μ hμ).symm

private theorem primaryClass_of_quadraticSixteen
    {μ : AlgebraicClosure ℚ} (hμ : μ ^ 2 - 10 * μ + 23 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; right; left
  exact (cycleDefectQuadraticSixteen_eq_minpoly μ hμ).symm

private theorem primaryClass_of_cubicSeven
    {μ : AlgebraicClosure ℚ}
    (hμ : μ ^ 3 - 16 * μ ^ 2 + 83 * μ - 139 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; right; right; left
  exact (cycleDefectCubicSeven_eq_minpoly μ hμ).symm

private theorem primaryClass_of_cubicNine
    {μ : AlgebraicClosure ℚ}
    (hμ : μ ^ 3 - 15 * μ ^ 2 + 72 * μ - 111 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; right; right; right; left
  exact (cycleDefectCubicNine_eq_minpoly μ hμ).symm

private theorem primaryClass_of_quinticEleven
    {μ : AlgebraicClosure ℚ}
    (hμ : μ ^ 5 - 26 * μ ^ 4 + 266 * μ ^ 3 - 1337 * μ ^ 2
      + 3298 * μ - 3191 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; right; right; right; right; left
  exact (cycleDefectQuinticEleven_eq_minpoly μ hμ).symm

private theorem primaryClass_of_sexticThirteen
    {μ : AlgebraicClosure ℚ}
    (hμ : μ ^ 6 - 31 * μ ^ 5 + 395 * μ ^ 4 - 2646 * μ ^ 3
      + 9821 * μ ^ 2 - 19138 * μ + 15289 = 0) :
    OrderSixteenCycleDefectPrimaryClass μ := by
  unfold OrderSixteenCycleDefectPrimaryClass
  right; right; right; right; right; right; right; right; right
  exact (cycleDefectSexticThirteen_eq_minpoly μ hμ).symm

theorem cycleThree_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 3).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleThree_defect_root α hα with hthree | hsix
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_eq_six hsix

theorem cycleFive_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 5).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleFive_defect_root α hα with hthree | hquadratic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_quadraticFive hquadratic

theorem cycleSix_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 6).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleSix_defect_root α hα with hthree | hsix
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_eq_six hsix

theorem cycleSeven_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 7).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleSeven_defect_root α hα with hthree | hcubic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_cubicSeven hcubic

theorem cycleEight_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 8).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleEight_defect_root α hα with hthree | hfive | hseven
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_eq_five hfive
  · exact primaryClass_of_eq_seven hseven

theorem cycleNine_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 9).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleNine_defect_root α hα with hthree | hsix | hcubic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_eq_six hsix
  · exact primaryClass_of_cubicNine hcubic

theorem cycleTen_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 10).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleTen_defect_root α hα with hthree | hquadratic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_quadraticFive hquadratic

theorem cycleEleven_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 11).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleEleven_defect_root α hα with hthree | hquintic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_quinticEleven hquintic

theorem cycleThirteen_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 13).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleThirteen_defect_root α hα with hthree | hsextic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_sexticThirteen hsextic

theorem cycleSixteen_defect_primary_class
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) 16).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases cycleSixteen_defect_root α hα with
    hthree | hfive | hseven | hquadratic
  · exact primaryClass_of_eq_three hthree
  · exact primaryClass_of_eq_five hfive
  · exact primaryClass_of_eq_seven hseven
  · exact primaryClass_of_quadraticSixteen hquadratic

/-- Uniform consumer form: every adjacency root belonging to any cycle
order in the order-sixteen census maps to one of the ten registered defect
primaries (four rational and six nonlinear). -/
theorem orderSixteenCycle_defect_primary_class
    {r : ℕ} (hr : OrderSixteenCycleOrder r)
    (α : AlgebraicClosure ℚ)
    (hα : (Chebyshev.C (AlgebraicClosure ℚ) (r : ℤ)).eval α = 2) :
    OrderSixteenCycleDefectPrimaryClass (7 - α ^ 2) := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cycleThree_defect_primary_class α hα
  · exact cycleFive_defect_primary_class α hα
  · exact cycleSix_defect_primary_class α hα
  · exact cycleSeven_defect_primary_class α hα
  · exact cycleEight_defect_primary_class α hα
  · exact cycleNine_defect_primary_class α hα
  · exact cycleTen_defect_primary_class α hα
  · exact cycleEleven_defect_primary_class α hα
  · exact cycleThirteen_defect_primary_class α hα
  · exact cycleSixteen_defect_primary_class α hα

end

end Erdos85
