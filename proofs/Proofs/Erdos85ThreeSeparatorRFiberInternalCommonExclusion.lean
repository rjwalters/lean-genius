import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85ThreeSeparatorWingRoutingDegree

/-!
# R-fibers avoid internal two-step arcs

The center of an R-fiber is already a common A-neighbor of its two X-points.
In a C4-free graph it is their unique common neighbor.  Since the center lies
outside X, the fiber endpoints have no common neighbor inside X.  This is
(B29), the first direct compatibility constraint between the R-fiber system
and the B22 path-cycle graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- B29 in exact common-neighborhood form. -/
theorem Rfiber_internal_commonNeighbor_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (X R : Finset V) (x y r : V)
    (hxy : x ≠ y)
    (hRX : Disjoint R X)
    (hrR : r ∈ R)
    (hrx : A.Adj x r)
    (hry : A.Adj y r) :
    (A.neighborFinset x ∩ A.neighborFinset y) ∩ X = ∅ := by
  apply Finset.Subset.antisymm
  · intro z hz
    exfalso
    have hzCommon := Finset.mem_inter.mp hz |>.1
    have hzX := Finset.mem_inter.mp hz |>.2
    have hxz : A.Adj x z :=
      (A.mem_neighborFinset x z).mp (Finset.mem_inter.mp hzCommon).1
    have hyz : A.Adj y z :=
      (A.mem_neighborFinset y z).mp (Finset.mem_inter.mp hzCommon).2
    have hrz : r = z :=
      commonNeighbor_unique_of_c4Free hfree hxy hrx hry hxz hyz
    subst z
    exact Finset.disjoint_left.mp hRX hrR hzX
  · exact Finset.empty_subset _

/-- Walk-facing B29: no R-fiber can join the two ends of a two-step walk
whose middle vertex lies in X. -/
theorem not_Rfiber_of_internal_twoStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (X R : Finset V) (x y z r : V)
    (hxy : x ≠ y)
    (hRX : Disjoint R X)
    (hzX : z ∈ X)
    (hxz : A.Adj x z)
    (hyz : A.Adj y z)
    (hrR : r ∈ R) :
    ¬(A.Adj x r ∧ A.Adj y r) := by
  rintro ⟨hrx, hry⟩
  have hempty := Rfiber_internal_commonNeighbor_empty
    A hfree X R x y r hxy hRX hrR hrx hry
  have hzmem : z ∈ (A.neighborFinset x ∩ A.neighborFinset y) ∩ X := by
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨(A.mem_neighborFinset x z).mpr hxz,
       (A.mem_neighborFinset y z).mpr hyz⟩, hzX⟩
  rw [hempty] at hzmem
  simpa using hzmem

end

end Erdos85

#print axioms Erdos85.Rfiber_internal_commonNeighbor_empty
#print axioms Erdos85.not_Rfiber_of_internal_twoStep
