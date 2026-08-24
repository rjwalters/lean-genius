import Proofs.Erdos85ThreeSeparatorPositiveSpikeWingDecomposition

/-!
# Exact wing-routing degrees

The componentwise B6 identity says that the K-degree `k` and separator
attachment count `t` satisfy `k+t=2`.  The B25 two-walk count gives
`k+r=(3-t)+ι`, where `ι` records adjacency to the exceptional point.
Writing both equations without truncated subtraction makes the conclusion
`r=1+ι` immediate and safe over `ℕ`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Subtraction-safe arithmetic core of (B25). -/
theorem wingRouting_R_degree_of_K_attachment_balance
    (k r t i : ℕ)
    (hKt : k + t = 2)
    (hwalk : k + r = (3 - t) + i) :
    r = 1 + i := by
  omega

/-- Finset-degree form of the exact B25 routing rule. -/
theorem positiveSpike_exact_R_degree_of_wingRouting
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (K R W : Finset V) (c x : V)
    (hKt : (A.neighborFinset x ∩ K).card +
      (D.neighborFinset x ∩ W).card = 2)
    (hwalk : (A.neighborFinset x ∩ K).card +
        (A.neighborFinset x ∩ R).card =
      (3 - (D.neighborFinset x ∩ W).card) +
        (if x ∈ A.neighborFinset c then 1 else 0)) :
    (A.neighborFinset x ∩ R).card =
      1 + (if x ∈ A.neighborFinset c then 1 else 0) := by
  exact wingRouting_R_degree_of_K_attachment_balance
    (A.neighborFinset x ∩ K).card
    (A.neighborFinset x ∩ R).card
    (D.neighborFinset x ∩ W).card
    (if x ∈ A.neighborFinset c then 1 else 0) hKt hwalk

/-- The twice-attached specialization highlighted after B25: away from the
exceptional A-neighbor, a twice-attached X-point has no K-neighbor and
exactly one R-neighbor. -/
theorem positiveSpike_twiceAttached_K_zero_R_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (K R W : Finset V) (c x : V)
    (hKt : (A.neighborFinset x ∩ K).card +
      (D.neighborFinset x ∩ W).card = 2)
    (hwalk : (A.neighborFinset x ∩ K).card +
        (A.neighborFinset x ∩ R).card =
      (3 - (D.neighborFinset x ∩ W).card) +
        (if x ∈ A.neighborFinset c then 1 else 0))
    (htwo : (D.neighborFinset x ∩ W).card = 2)
    (hxnot : x ∉ A.neighborFinset c) :
    (A.neighborFinset x ∩ K).card = 0 ∧
      (A.neighborFinset x ∩ R).card = 1 := by
  have hR := positiveSpike_exact_R_degree_of_wingRouting
    A D K R W c x hKt hwalk
  simp [hxnot] at hR
  constructor
  · omega
  · exact hR

end

end Erdos85

#print axioms Erdos85.wingRouting_R_degree_of_K_attachment_balance
#print axioms Erdos85.positiveSpike_exact_R_degree_of_wingRouting
#print axioms Erdos85.positiveSpike_twiceAttached_K_zero_R_one
