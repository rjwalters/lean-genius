import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalTraceSharp

/-!
# Tagged two-shore rotation patterns for the high eight-plus-eight trace

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The two shores and three cyclic rotations give six distinct membership
patterns with respect to the first internal component.  This finite kernel
lemma is the injectivity discriminator for combining both 96-contributions
into a single 192-term antipodal trace census.
-/

namespace Erdos85

/-- Membership in the first shore at each of the three tuple positions.
`false` tags a base with two first-shore vertices; `true` tags a base with
one first-shore vertex. -/
def eightEightTwoShoreRotationPattern
    (shore : Bool) (rotation position : Fin 3) : Bool :=
  if shore then
    ![![false, false, true], ![false, true, false], ![true, false, false]]
      rotation position
  else
    ![![true, true, false], ![true, false, true], ![false, true, true]]
      rotation position

/-- The shore tag and cyclic rotation are recovered uniquely from their
three-position shore-membership pattern. -/
theorem eightEightTwoShoreRotationPattern_injective :
    Function.Injective (fun p : Bool × Fin 3 =>
      fun position => eightEightTwoShoreRotationPattern p.1 p.2 position) := by
  intro p q hpq
  have hp0 := congrFun hpq 0
  have hp1 := congrFun hpq 1
  have hp2 := congrFun hpq 2
  revert p q
  decide

end Erdos85

#print axioms Erdos85.eightEightTwoShoreRotationPattern_injective
