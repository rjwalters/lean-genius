import Proofs.Erdos85SizeTwoEigenlineCyclicOrbitIncidence
import Proofs.Erdos85Problem
import Proofs.Erdos101ProblemOQ02

/-!
# C4-free second moments on cyclic difference orbits

First-moment orbit incidence is not enough to refute the reflection-circulant
grid.  This file retains the first genuinely nonlinear datum: for one source
difference orbit, count how many of its `q` cells meet each target cell.
C4-freeness bounds the sum of the choose-two multiplicities by `choose(q,2)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Number of cells in the fixed source-difference orbit `t` adjacent to the
target cell `v`. -/
def sizeTwoOrbitNeighborMultiplicity
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t : sizeTwoAllowedDifference q a)
    (v : sizeTwoCyclicExteriorCell q a) : ℕ :=
  ((Finset.univ : Finset (ZMod q)).filter fun x =>
    C.Adj (sizeTwoCyclicCellAt q a x t) v).card

/-- Distinct base points give distinct cells in a fixed difference orbit. -/
theorem sizeTwoCyclicCellAt_injective
    (q : ℕ) (a : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Injective (fun x : ZMod q => sizeTwoCyclicCellAt q a x t) := by
  intro x y h
  have h' := congrArg (fun u => (sizeTwoCyclicExteriorCellEquiv q a u).1) h
  simpa [sizeTwoCyclicCellAt] using h'

/-- **Orbit cherry bound.**  Each pair of distinct cells in one source orbit
can have at most one common target, or those four vertices form a `C4`. -/
theorem sizeTwoOrbitNeighborMultiplicity_choose_two_sum_le
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (t : sizeTwoAllowedDifference q a) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
        (sizeTwoOrbitNeighborMultiplicity q a C t v).choose 2) ≤ q.choose 2 := by
  letI : DecidableEq (sizeTwoCyclicExteriorCell q a) := Classical.decEq _
  let Inc : ZMod q → sizeTwoCyclicExteriorCell q a → Prop :=
    fun x v => C.Adj (sizeTwoCyclicCellAt q a x t) v
  have huniq : ∀ x ∈ (Finset.univ : Finset (ZMod q)),
      ∀ y ∈ (Finset.univ : Finset (ZMod q)), x ≠ y →
      ∀ v ∈ (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)),
      ∀ w ∈ (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)),
      Inc x v → Inc y v → Inc x w → Inc y w → v = w := by
    intro x _ y _ hxy v _ w _ hxv hyv hxw hyw
    by_contra hvw
    apply hfree
    exact containsC4_of_two_common
      (fun h => hxy (sizeTwoCyclicCellAt_injective q a t h)) hvw
      (C.adj_symm hxv) (C.adj_symm hyv)
      (C.adj_symm hxw) (C.adj_symm hyw)
  have h := Erdos101OQ02ST.sum_choose_two_le Inc
    (Finset.univ : Finset (ZMod q))
    (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)) huniq
  simpa [Inc, Erdos101OQ02ST.pointsOn,
    sizeTwoOrbitNeighborMultiplicity, ZMod.card] using h

/-- The total target multiplicity is the total degree of the `q` source cells
in the fixed difference orbit. -/
theorem sizeTwoOrbitNeighborMultiplicity_sum_of_regular
    (q d : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hreg : ∀ u, C.degree u = d)
    (t : sizeTwoAllowedDifference q a) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
      sizeTwoOrbitNeighborMultiplicity q a C t v) = q * d := by
  calc
    _ = ∑ v : sizeTwoCyclicExteriorCell q a,
        ∑ x : ZMod q,
          if C.Adj (sizeTwoCyclicCellAt q a x t) v then 1 else 0 := by
      unfold sizeTwoOrbitNeighborMultiplicity
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.card_filter]
    _ = ∑ x : ZMod q,
        ∑ v : sizeTwoCyclicExteriorCell q a,
          if C.Adj (sizeTwoCyclicCellAt q a x t) v then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ x : ZMod q, C.degree (sizeTwoCyclicCellAt q a x t) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← C.card_neighborFinset_eq_degree]
      rw [show C.neighborFinset (sizeTwoCyclicCellAt q a x t) =
          (Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)).filter
            fun v => C.Adj (sizeTwoCyclicCellAt q a x t) v by
        ext v
        simp]
      rw [Finset.card_filter]
    _ = ∑ _x : ZMod q, d := by simp [hreg]
    _ = q * d := by simp [ZMod.card]

/-- Under the normalized row-hit law the total source-orbit multiplicity is
`q(q-2)`. -/
theorem sizeTwoOrbitNeighborMultiplicity_sum_of_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
      sizeTwoOrbitNeighborMultiplicity q a C t v) = q * (q - 2) := by
  exact sizeTwoOrbitNeighborMultiplicity_sum_of_regular q (q - 2) a C
    (sizeTwoCyclic_degree_eq_sub_two_of_row_hit q a C hq1 hrow_hit) t

/-- Combining the exact first moment with C4-freeness bounds the square
second moment of the orbit-to-target multiplicities. -/
theorem sizeTwoOrbitNeighborMultiplicity_sq_sum_le_of_row_hit
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hq1 : (1 : ZMod q) ≠ 0)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1)
    (t : sizeTwoAllowedDifference q a) :
    (∑ v : sizeTwoCyclicExteriorCell q a,
      (sizeTwoOrbitNeighborMultiplicity q a C t v) ^ 2) ≤
      q * (q - 2) + 2 * q.choose 2 := by
  have hchoose := sizeTwoOrbitNeighborMultiplicity_choose_two_sum_le
    q a C hfree t
  have hsum := sizeTwoOrbitNeighborMultiplicity_sum_of_row_hit
    q a C hq1 hrow_hit t
  have hid : (∑ v : sizeTwoCyclicExteriorCell q a,
      (sizeTwoOrbitNeighborMultiplicity q a C t v) ^ 2) =
      (∑ v : sizeTwoCyclicExteriorCell q a,
        sizeTwoOrbitNeighborMultiplicity q a C t v) +
      2 * ∑ v : sizeTwoCyclicExteriorCell q a,
        (sizeTwoOrbitNeighborMultiplicity q a C t v).choose 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact Erdos101OQ02ST.sq_eq_self_add_two_mul_choose_two _
  rw [hsum] at hid
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicCellAt_injective
#print axioms Erdos85.sizeTwoOrbitNeighborMultiplicity_choose_two_sum_le
#print axioms Erdos85.sizeTwoOrbitNeighborMultiplicity_sum_of_row_hit
#print axioms Erdos85.sizeTwoOrbitNeighborMultiplicity_sq_sum_le_of_row_hit
