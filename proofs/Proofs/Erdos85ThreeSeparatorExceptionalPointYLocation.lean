import Proofs.Erdos85ThreeSeparatorPositiveSpikeWingDecomposition

/-!
# Exceptional point on the large shore

If the positive-spike exceptional point lies on `Y`, specializing the
boundary profile at that point and using looplessness leaves only one unit
of defect flow to the separator.  This is (B17Y).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-facing (B17Y), stated with the subtraction-free boundary profile.
The conclusion retains both the exact complementary incidence equation and
the separator-attachment bound used downstream. -/
theorem exceptionalPoint_Y_defect_attachment_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (Y W R : Finset V) (c : V)
    (hcY : c ∈ Y)
    (hprofile : ∀ y ∈ Y,
      (D.neighborFinset y ∩ W).card +
          (A.neighborFinset y ∩ R).card =
        1 + (if A.Adj c y then 1 else 0)) :
    (D.neighborFinset c ∩ W).card +
        (A.neighborFinset c ∩ R).card = 1 ∧
      (D.neighborFinset c ∩ W).card ≤ 1 := by
  have hc := hprofile c hcY
  have hloop : ¬ A.Adj c c := A.loopless.irrefl c
  rw [if_neg hloop, Nat.add_zero] at hc
  exact ⟨hc, by omega⟩

end

end Erdos85

#print axioms Erdos85.exceptionalPoint_Y_defect_attachment_le_one
