import Proofs.Erdos85MuNegFiveExplicitParameters
import Proofs.Erdos85SizeTwoMuNegThreeEightEightSectorParameterGrid

/-!
# Cycle-entry reduction for all canonical `mu = -5` endpoints

The explicit parameter ledger forces `r+k=5` whenever a shore has no cycle
entries.  None of the three negative-switch-orbit endpoints `h503`, `h504`,
or `h512` lies on that affine line.  Consequently the graph-facing sector
dichotomy puts both shores of every canonical `mu=-5` endpoint in the
all-cycle-entries-one (triangle-free) branch.
-/

namespace Erdos85

noncomputable section

/-- Generic form of the canonical endpoint reduction: away from `r+k=5`,
the zero side of the graph-facing sector dichotomy is impossible. -/
theorem MuNegFiveExplicitParameterLedger.cycleEntriesOne_of_sum_ne_five
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitParameterLedger N M f g k r)
    (hsum : r + k ≠ 5)
    (hsector : C8CycleEntriesZero N ∨ C8CycleEntriesOne N) :
    C8CycleEntriesOne N := by
  rcases hsector with hzero | hone
  · exact False.elim <| hsum
      (L.sum_eq_five_of_cycleZeros hzero.1 hzero.2)
  · exact hone

/-- The `h504 = (-5,0,4)` endpoint is all-cycle-entries-one. -/
theorem MuNegFiveExplicitParameterLedger.zeroFour_cycleEntriesOne
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitParameterLedger N M f g 0 4)
    (hsector : C8CycleEntriesZero N ∨ C8CycleEntriesOne N) :
    C8CycleEntriesOne N := by
  exact L.cycleEntriesOne_of_sum_ne_five (by norm_num) hsector

/-- The `h512 = (-5,1,2)` endpoint is all-cycle-entries-one. -/
theorem MuNegFiveExplicitParameterLedger.oneTwo_cycleEntriesOne
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitParameterLedger N M f g 1 2)
    (hsector : C8CycleEntriesZero N ∨ C8CycleEntriesOne N) :
    C8CycleEntriesOne N := by
  exact L.cycleEntriesOne_of_sum_ne_five (by norm_num) hsector

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitParameterLedger.cycleEntriesOne_of_sum_ne_five
#print axioms Erdos85.MuNegFiveExplicitParameterLedger.zeroFour_cycleEntriesOne
#print axioms Erdos85.MuNegFiveExplicitParameterLedger.oneTwo_cycleEntriesOne
