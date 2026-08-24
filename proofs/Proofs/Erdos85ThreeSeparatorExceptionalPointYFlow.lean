import Proofs.Erdos85ThreeSeparatorPositiveSpikeLocationBalance

/-!
# Flow at a Y-located exceptional point

On the first non-endpoint slice, evaluating the positive-spike flow equation
at an exceptional point `c ∈ Y` gives
`deg_A(c,R) = 1 - deg_D(c,W)`.  We retain the stronger subtraction-free
form: the two nonnegative degrees sum to one.  This is B32 and is the input
that limits the overlap of the two fiber matchings in B32'.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic core of B32. -/
theorem exceptionalPoint_Y_flow_arithmetic
    (n r : ℕ) (hflow : n + r = 1) :
    n ≤ 1 ∧ r = 1 - n ∧
      ((n = 0 ∧ r = 1) ∨ (n = 1 ∧ r = 0)) := by
  omega

/-- Symmetric form of the B32 dichotomy, convenient when the R-degree is
the quantity already known. -/
theorem exceptionalPoint_Y_flow_cases
    (n r : ℕ) (hflow : n + r = 1) :
    (n = 0 ↔ r = 1) ∧ (n = 1 ↔ r = 0) := by
  omega

/-- Finset packaging of B32.  Instantiate `D` with the second-order defect
graph and `A` with the original graph. -/
theorem exceptionalPoint_Y_neighborFlow
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (c : V) (W R : Finset V)
    (hflow : (D.neighborFinset c ∩ W).card +
      (A.neighborFinset c ∩ R).card = 1) :
    (D.neighborFinset c ∩ W).card ≤ 1 ∧
      (A.neighborFinset c ∩ R).card =
        1 - (D.neighborFinset c ∩ W).card ∧
      (((D.neighborFinset c ∩ W).card = 0 ∧
          (A.neighborFinset c ∩ R).card = 1) ∨
        ((D.neighborFinset c ∩ W).card = 1 ∧
          (A.neighborFinset c ∩ R).card = 0)) := by
  exact exceptionalPoint_Y_flow_arithmetic _ _ hflow

/-- In particular there is at most one R-neighbor available to center an
edge common to the exceptional and residual fiber systems. -/
theorem exceptionalPoint_Y_R_neighbor_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (c : V) (W R : Finset V)
    (hflow : (D.neighborFinset c ∩ W).card +
      (A.neighborFinset c ∩ R).card = 1) :
    (A.neighborFinset c ∩ R).card ≤ 1 := by
  omega

end


end Erdos85


#print axioms Erdos85.exceptionalPoint_Y_flow_arithmetic
#print axioms Erdos85.exceptionalPoint_Y_flow_cases
#print axioms Erdos85.exceptionalPoint_Y_neighborFlow
#print axioms Erdos85.exceptionalPoint_Y_R_neighbor_card_le_one
