import Proofs.Erdos85MuThreeMixedGridForeignColumnTransport
import Proofs.Erdos85MuThreeMixedGridForeignRowTransport

/-!
# Orthogonality around H-empty rectangles

For an H-empty coordinate rectangle `(a,a') × (b,b')`, start at an occupied
cell of column `b`.  Follow the matching to row `a`, back to column `b'`, and
then to row `a'`.  This three-step endpoint cannot be the direct matching mate
in row `a'` through column `b`; equality would close the four matched edges
into a C4.  This is the first explicit coupling of row and column transport.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The endpoint of the three matching steps around three sides of an
H-empty rectangle. -/
noncomputable def MuThreeMixedGridCode.foreignRectangleThreeStep
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (_ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    {q : muThreeMixedCell K // q.1.1 = a'} :=
  code.foreignFiberMatchingEquiv H K C a' b' ha'b'
    (code.foreignRowTransportEquiv H K C a b b' hab hab' u)

/-- **Foreign rectangle orthogonality.**  The three-step endpoint differs
from the direct mate on the fourth side. -/
theorem MuThreeMixedGridCode.foreignRectangleThreeStep_ne_direct
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a a' : X} (haa' : a ≠ a') {b b' : Y} (hbb' : b ≠ b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    code.foreignRectangleThreeStep H K C a a' b b'
        hab hab' ha'b ha'b' u ≠
      code.foreignFiberMatchingEquiv H K C a' b ha'b u := by
  intro hroute
  apply code.foreignRowTransportEquiv_ne H K C haa' hbb'
    hab hab' ha'b ha'b' u
  apply (code.foreignFiberMatchingEquiv H K C a' b' ha'b').injective
  simpa [MuThreeMixedGridCode.foreignRectangleThreeStep,
    MuThreeMixedGridCode.foreignRowTransportEquiv] using hroute

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignRectangleThreeStep
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleThreeStep_ne_direct
