import Proofs.Erdos85SizeTwoEigenlineSixTenAntipodalTraceSharp
import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTriangleShape

/-!
# Sharp trace in the high all-triangle C10 branch

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The six directed orderings of the C10 triangle with successive offsets
`3,3,4`, based at `i`. -/
def sixTenLongTrianglePattern (p : ZMod 10 × Fin 6) :
    ZMod 10 × ZMod 10 × ZMod 10 :=
  let i := p.1
  ![(i, i + 3, i + 6), (i, i + 6, i + 3),
    (i + 3, i, i + 6), (i + 3, i + 6, i),
    (i + 6, i, i + 3), (i + 6, i + 3, i)] p.2

theorem sixTenLongTrianglePattern_injective :
    Function.Injective sixTenLongTrianglePattern := by
  decide

end


end Erdos85

#print axioms Erdos85.sixTenLongTrianglePattern_injective
