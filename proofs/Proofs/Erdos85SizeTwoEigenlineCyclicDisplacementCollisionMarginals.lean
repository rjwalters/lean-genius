import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementLineSums

/-!
# Coupling collision counts to displacement marginals

For fixed target difference and displacement, a two-source collision is the
intersection of two shifted one-edge fibers.  Finite inclusion--exclusion
therefore converts the C4 collision cap into explicit autocorrelation
constraints on the displacement tensor.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reindexing the second source base identifies its edge fiber with a
predicate on the first source base. -/
def sizeTwoDisplacementSecondEdgeFiberEquiv
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (t s : sizeTwoAllowedDifference q a) (d r : ZMod q) :
    sizeTwoDisplacementEdgeFiber q a C t s (r - d) ≃
      {x : ZMod q //
        C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
          (sizeTwoCyclicCellAt q a (x + r) s)} where
  toFun y := ⟨y.1 - d, by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using y.2⟩
  invFun x := ⟨x.1 + d, by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using x.2⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- **Collision/marginal coupling.**  Two shifted edge fibers live in a
`q`-element base universe, and their intersection is exactly the collision
fiber. -/
theorem sizeTwoDisplacementEdgeCount_add_shift_le
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (t s : sizeTwoAllowedDifference q a) (d r : ZMod q) :
    sizeTwoDisplacementEdgeCount q a C t s r +
        sizeTwoDisplacementEdgeCount q a C t s (r - d) ≤
      q + sizeTwoDisplacementCollisionCount q a C t d s r := by
  let A : Finset (ZMod q) := (Finset.univ.filter fun x =>
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a (x + r) s))
  let B : Finset (ZMod q) := (Finset.univ.filter fun x =>
    C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
      (sizeTwoCyclicCellAt q a (x + r) s))
  have hA : sizeTwoDisplacementEdgeCount q a C t s r = A.card := by
    unfold sizeTwoDisplacementEdgeCount sizeTwoDisplacementEdgeFiber A
    rw [Fintype.card_subtype]
  have hB : sizeTwoDisplacementEdgeCount q a C t s (r - d) = B.card := by
    rw [sizeTwoDisplacementEdgeCount]
    rw [Fintype.card_congr
      (sizeTwoDisplacementSecondEdgeFiberEquiv q a C t s d r)]
    unfold B
    rw [Fintype.card_subtype]
  have hI : sizeTwoDisplacementCollisionCount q a C t d s r =
      (A ∩ B).card := by
    unfold sizeTwoDisplacementCollisionCount sizeTwoDisplacementCollisionFiber
    rw [Fintype.card_subtype]
    unfold A B
    congr 1
    ext x
    simp
  have hU : (A ∪ B).card ≤ q := by
    calc
      (A ∪ B).card ≤ (Finset.univ : Finset (ZMod q)).card := by
        apply Finset.card_le_card
        exact Finset.subset_univ _
      _ = q := by simp [ZMod.card]
  have hie := Finset.card_union_add_card_inter A B
  rw [hA, hB, hI]
  omega

end

end Erdos85

#print axioms Erdos85.sizeTwoDisplacementEdgeCount_add_shift_le
