import Proofs.Erdos85MuThreeMixedGridForeignRectangleOrthogonality

/-!
# Fixed-point-free rectangle monodromy

The three-step route and the direct fourth-side matching are equivalences
from the same source column fiber to the same target row fiber.  Comparing
them gives a permutation of the six-cell source fiber.  Rectangle
orthogonality says this monodromy has no fixed points.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The three-step rectangle route as an equivalence of fibers. -/
noncomputable def MuThreeMixedGridCode.foreignRectangleThreeStepEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (_ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    {u : muThreeMixedCell K // u.1.2 = b} ≃
      {q : muThreeMixedCell K // q.1.1 = a'} :=
  (code.foreignRowTransportEquiv H K C a b b' hab hab').trans
    (code.foreignFiberMatchingEquiv H K C a' b' ha'b')

/-- Compare the three-step route to the direct matching, obtaining a
permutation of the source column fiber. -/
noncomputable def MuThreeMixedGridCode.foreignRectangleMonodromyEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    {u : muThreeMixedCell K // u.1.2 = b} ≃
      {u : muThreeMixedCell K // u.1.2 = b} :=
  (code.foreignRectangleThreeStepEquiv H K C a a' b b'
      hab hab' ha'b ha'b').trans
    (code.foreignFiberMatchingEquiv H K C a' b ha'b).symm

/-- **Rectangle monodromy derangement.**  No source cell is fixed. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a a' : X} (haa' : a ≠ a') {b b' : Y} (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
      hab hab' ha'b ha'b' u ≠ u := by
  intro hfix
  apply code.foreignRectangleThreeStep_ne_direct H K C haa' hbb'
    hab hab' ha'b ha'b' u
  have h := congrArg (code.foreignFiberMatchingEquiv H K C a' b ha'b) hfix
  simpa [MuThreeMixedGridCode.foreignRectangleMonodromyEquiv,
    MuThreeMixedGridCode.foreignRectangleThreeStepEquiv,
    MuThreeMixedGridCode.foreignRectangleThreeStep] using h

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleThreeStepEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_ne
