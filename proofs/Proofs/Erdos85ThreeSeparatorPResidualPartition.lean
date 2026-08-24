import Proofs.Erdos85ThreeSeparatorPResidualBudget

/-!
# Structural P-to-R residual partition

The arithmetic B52 budget is fed by an exact partition inside one wing.
For a complementary P-center `p`, the candidate set `R_w` splits into
defect neighbors of `p`, points whose pair with `p` is resolved through X,
and points whose pair with `p` is resolved through Y.  This file records
that graph-facing partition and turns it into the subtraction-free equation
`d + s + f + 1 = n` used by `Pcenter_residual_degree_ge_n_sub_two`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact cardinality of the three classes in the B52 candidate partition. -/
theorem Pcenter_residual_candidate_partition_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (p : V) (Rw SX SY : Finset V)
    (hDX : Disjoint (D.neighborFinset p ∩ Rw) SX)
    (houter : Disjoint ((D.neighborFinset p ∩ Rw) ∪ SX) SY)
    (hpartition : ((D.neighborFinset p ∩ Rw) ∪ SX) ∪ SY = Rw) :
    (D.neighborFinset p ∩ Rw).card + SX.card + SY.card = Rw.card := by
  calc
    (D.neighborFinset p ∩ Rw).card + SX.card + SY.card =
        ((D.neighborFinset p ∩ Rw) ∪ SX).card + SY.card := by
      rw [Finset.card_union_of_disjoint hDX]
    _ = (((D.neighborFinset p ∩ Rw) ∪ SX) ∪ SY).card := by
      rw [Finset.card_union_of_disjoint houter]
    _ = Rw.card := congrArg Finset.card hpartition

/-- The structural partition supplies exactly the one-wing equation assumed
by B52.  Here `|R_w|+1=n` is the wing-size convention from (B8'). -/
theorem Pcenter_residual_partition_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (p : V) (Rw SX SY : Finset V) (n : ℕ)
    (hDX : Disjoint (D.neighborFinset p ∩ Rw) SX)
    (houter : Disjoint ((D.neighborFinset p ∩ Rw) ∪ SX) SY)
    (hpartition : ((D.neighborFinset p ∩ Rw) ∪ SX) ∪ SY = Rw)
    (hwing : Rw.card + 1 = n) :
    (D.neighborFinset p ∩ Rw).card + SX.card + SY.card + 1 = n := by
  have hcard := Pcenter_residual_candidate_partition_card
    D p Rw SX SY hDX houter hpartition
  omega

/-- If the two resolution classes are mutually exclusive indicators, the
structural partition yields the lower bound `n-2 ≤ deg_D(p,R_w)` directly. -/
theorem Pcenter_residual_partition_degree_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (p : V) (Rw SX SY : Finset V) (n : ℕ)
    (hDX : Disjoint (D.neighborFinset p ∩ Rw) SX)
    (houter : Disjoint ((D.neighborFinset p ∩ Rw) ∪ SX) SY)
    (hpartition : ((D.neighborFinset p ∩ Rw) ∪ SX) ∪ SY = Rw)
    (hwing : Rw.card + 1 = n)
    (hmutex : SX.card + SY.card ≤ 1) :
    n - 2 ≤ (D.neighborFinset p ∩ Rw).card := by
  apply Pcenter_residual_degree_ge_n_sub_two
    n (D.neighborFinset p ∩ Rw).card SX.card SY.card
  · exact Pcenter_residual_partition_equation
      D p Rw SX SY n hDX houter hpartition hwing
  · exact hmutex

end

end Erdos85

#print axioms Erdos85.Pcenter_residual_candidate_partition_card
#print axioms Erdos85.Pcenter_residual_partition_equation
#print axioms Erdos85.Pcenter_residual_partition_degree_lower
