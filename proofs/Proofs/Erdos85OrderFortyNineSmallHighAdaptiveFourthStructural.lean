import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFourthCubeSelectors
import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdStructural

/-!
# Residual census for the adaptive fourth split

The live third selectors lie in the five-element index set
`{2,4,5,6,7}`.  Splitting the high-`1` partition again at low vertices `21`
and `22` leaves a compact residual relation: the two new selectors are
distinct, avoid the old selectors, and the left one also avoids the fixed
matching mate of the old right selector.  This file records that exact
generator-facing census.  A graph-level C4 witness consumer is deliberately
kept separate.
-/

namespace Erdos85

/-- The five selector indices that survive the first adaptive C4 pruning. -/
def orderFortyNineThreeHighB1AdaptiveLiveIndex (i : Fin 8) : Bool :=
  i.val = 2 || 4 ≤ i.val

/-- The matching mate inside the two fixed high-`1` pairs.  Index `2` has no
mate in the live set and is sent to itself. -/
def orderFortyNineThreeHighB1AdaptiveLiveMate (i : Fin 8) : Fin 8 :=
  match i.val with
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | _ => i

/-- Exact fourth-level residue after the forced-C4 cells are removed. -/
def orderFortyNineThreeHighB1AdaptiveFourthResidual
    (li ri ai bi : Fin 8) : Bool :=
  orderFortyNineThreeHighB1AdaptiveResidual li ri &&
    orderFortyNineThreeHighB1AdaptiveLiveIndex ai &&
    orderFortyNineThreeHighB1AdaptiveLiveIndex bi &&
    ai ≠ bi && ai ≠ li && ai ≠ ri &&
    bi ≠ li && bi ≠ ri &&
    ai ≠ orderFortyNineThreeHighB1AdaptiveLiveMate ri

/-- Every live third cell has either four or six fourth-level residual
children. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthResidual_card_eq_four_or_six
    (li ri : Fin 8)
    (hres : orderFortyNineThreeHighB1AdaptiveResidual li ri = true) :
    let children :=
      ((Finset.univ : Finset (Fin 8)).product Finset.univ).filter fun p =>
        orderFortyNineThreeHighB1AdaptiveFourthResidual li ri p.1 p.2
    children.card = 4 ∨ children.card = 6 := by
  fin_cases li <;> fin_cases ri
  all_goals simp [orderFortyNineThreeHighB1AdaptiveResidual] at hres
  all_goals native_decide

/-- Across the sixteen live third cells, exactly eighty fourth-level cubes
remain after structural pruning. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthResidual_count :
    (((Finset.univ : Finset (Fin 8)).product Finset.univ).product
      ((Finset.univ : Finset (Fin 8)).product Finset.univ) |>.filter fun p =>
        orderFortyNineThreeHighB1AdaptiveFourthResidual
          p.1.1 p.1.2 p.2.1 p.2.2).card = 80 := by
  native_decide

/-- The fourth split reduces the `16 × 64` positive child grid by 944
cells. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthStructurallyDead_count :
    16 * 64 - 80 = 944 := by
  norm_num

end Erdos85
