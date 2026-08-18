import Proofs.Erdos85OddFirstOrderSpectral
import Proofs.Erdos85SecondOrderStructure
import Proofs.Erdos85RamseyPlateau

/-!
# Clean odd-degree boundary closure

The historical second-order strict bound reaches the correct statement
through a parity-free Moore lemma carrying native-decision certificates.
For odd degree these certificates are unnecessary: the clean first-order
modular-trace bound leaves only the exact second-order cardinality, which the
clean one-regular antipodal argument excludes directly.
-/

namespace Erdos85

open SimpleGraph

/-- Clean-axiom version of the odd-degree strict Moore bound through the
second order. -/
theorem mul_pred_add_four_le_card_of_c4Free_minDegree_odd_clean
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G) :
    d * (d - 1) + 4 ≤ Fintype.card V := by
  have hbase : d * (d - 1) + 3 ≤ Fintype.card V :=
    mul_pred_add_three_le_card_of_c4Free_minDegree_odd
      G (by omega) hodd hmin hfree
  by_contra hnot
  have heq : Fintype.card V = d * (d - 1) + 3 := by omega
  exact hfree (containsC4_of_odd_secondOrder G hd hodd hmin heq)

/-- The exact second-order odd-degree plateau exclusion, re-exported beside
the clean strict bound as the complete odd-boundary interface. -/
theorem odd_secondOrder_boundary_package
    {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d) :
    minDegreeForC4 (d * (d - 1) + 3) ≤ d ∧
      ¬ C4PlateauCore (d * (d - 1) + 3) d := by
  exact ⟨minDegreeForC4_secondOrder_le_of_odd hd hodd,
    not_C4PlateauCore_secondOrder_of_odd hd hodd⟩

end Erdos85
