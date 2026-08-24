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

/-- Three graph-facing candidate partitions imply the exact global B52′
budget.  The first summand is the total P-to-R defect incidence and the
second is the total number of X/Y resolutions. -/
theorem three_Pcenter_residual_partitions_global_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (p0 p1 p2 : V)
    (R0 R1 R2 X0 X1 X2 Y0 Y1 Y2 : Finset V)
    (q n0 n1 n2 : ℕ)
    (hDX0 : Disjoint (D.neighborFinset p0 ∩ R0) X0)
    (hDX1 : Disjoint (D.neighborFinset p1 ∩ R1) X1)
    (hDX2 : Disjoint (D.neighborFinset p2 ∩ R2) X2)
    (houter0 : Disjoint ((D.neighborFinset p0 ∩ R0) ∪ X0) Y0)
    (houter1 : Disjoint ((D.neighborFinset p1 ∩ R1) ∪ X1) Y1)
    (houter2 : Disjoint ((D.neighborFinset p2 ∩ R2) ∪ X2) Y2)
    (hpartition0 : ((D.neighborFinset p0 ∩ R0) ∪ X0) ∪ Y0 = R0)
    (hpartition1 : ((D.neighborFinset p1 ∩ R1) ∪ X1) ∪ Y1 = R1)
    (hpartition2 : ((D.neighborFinset p2 ∩ R2) ∪ X2) ∪ Y2 = R2)
    (hwing0 : R0.card + 1 = n0)
    (hwing1 : R1.card + 1 = n1)
    (hwing2 : R2.card + 1 = n2)
    (hnsum : n0 + n1 + n2 = q + 1) :
    (((D.neighborFinset p0 ∩ R0).card +
        (D.neighborFinset p1 ∩ R1).card +
        (D.neighborFinset p2 ∩ R2).card) +
      ((X0.card + Y0.card) + (X1.card + Y1.card) +
        (X2.card + Y2.card))) + 2 = q ∧
    ((D.neighborFinset p0 ∩ R0).card +
        (D.neighborFinset p1 ∩ R1).card +
        (D.neighborFinset p2 ∩ R2).card) +
      ((X0.card + Y0.card) + (X1.card + Y1.card) +
        (X2.card + Y2.card)) = q - 2 := by
  have h0 := Pcenter_residual_partition_equation
    D p0 R0 X0 Y0 n0 hDX0 houter0 hpartition0 hwing0
  have h1 := Pcenter_residual_partition_equation
    D p1 R1 X1 Y1 n1 hDX1 houter1 hpartition1 hwing1
  have h2 := Pcenter_residual_partition_equation
    D p2 R2 X2 Y2 n2 hDX2 houter2 hpartition2 hwing2
  exact three_Pcenter_residual_budgets_sum q n0 n1 n2
    (D.neighborFinset p0 ∩ R0).card
    (D.neighborFinset p1 ∩ R1).card
    (D.neighborFinset p2 ∩ R2).card
    X0.card X1.card X2.card Y0.card Y1.card Y2.card
    hnsum h0 h1 h2

/-- With at most one resolution in each wing, the three structural
partitions give the global defect-incidence lower bound in B52′. -/
theorem three_Pcenter_residual_partitions_degree_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (p0 p1 p2 : V)
    (R0 R1 R2 X0 X1 X2 Y0 Y1 Y2 : Finset V)
    (q n0 n1 n2 : ℕ)
    (hDX0 : Disjoint (D.neighborFinset p0 ∩ R0) X0)
    (hDX1 : Disjoint (D.neighborFinset p1 ∩ R1) X1)
    (hDX2 : Disjoint (D.neighborFinset p2 ∩ R2) X2)
    (houter0 : Disjoint ((D.neighborFinset p0 ∩ R0) ∪ X0) Y0)
    (houter1 : Disjoint ((D.neighborFinset p1 ∩ R1) ∪ X1) Y1)
    (houter2 : Disjoint ((D.neighborFinset p2 ∩ R2) ∪ X2) Y2)
    (hpartition0 : ((D.neighborFinset p0 ∩ R0) ∪ X0) ∪ Y0 = R0)
    (hpartition1 : ((D.neighborFinset p1 ∩ R1) ∪ X1) ∪ Y1 = R1)
    (hpartition2 : ((D.neighborFinset p2 ∩ R2) ∪ X2) ∪ Y2 = R2)
    (hwing0 : R0.card + 1 = n0)
    (hwing1 : R1.card + 1 = n1)
    (hwing2 : R2.card + 1 = n2)
    (hnsum : n0 + n1 + n2 = q + 1)
    (hmutex0 : X0.card + Y0.card ≤ 1)
    (hmutex1 : X1.card + Y1.card ≤ 1)
    (hmutex2 : X2.card + Y2.card ≤ 1) :
    q - 5 ≤ (D.neighborFinset p0 ∩ R0).card +
      (D.neighborFinset p1 ∩ R1).card +
      (D.neighborFinset p2 ∩ R2).card := by
  have h0 := Pcenter_residual_partition_equation
    D p0 R0 X0 Y0 n0 hDX0 houter0 hpartition0 hwing0
  have h1 := Pcenter_residual_partition_equation
    D p1 R1 X1 Y1 n1 hDX1 houter1 hpartition1 hwing1
  have h2 := Pcenter_residual_partition_equation
    D p2 R2 X2 Y2 n2 hDX2 houter2 hpartition2 hwing2
  exact three_Pcenter_residual_degree_lower q n0 n1 n2
    (D.neighborFinset p0 ∩ R0).card
    (D.neighborFinset p1 ∩ R1).card
    (D.neighborFinset p2 ∩ R2).card
    X0.card X1.card X2.card Y0.card Y1.card Y2.card
    hnsum h0 h1 h2 hmutex0 hmutex1 hmutex2

end

end Erdos85

#print axioms Erdos85.Pcenter_residual_candidate_partition_card
#print axioms Erdos85.Pcenter_residual_partition_equation
#print axioms Erdos85.Pcenter_residual_partition_degree_lower
#print axioms Erdos85.three_Pcenter_residual_partitions_global_budget
#print axioms Erdos85.three_Pcenter_residual_partitions_degree_lower
