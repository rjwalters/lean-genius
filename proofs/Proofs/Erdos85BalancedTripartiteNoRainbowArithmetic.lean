import Proofs.Erdos85OrderSixtyFourDefectComponentEquitable

/-! # Arithmetic obstruction to a balanced four-color Gallai triangle -/

namespace Erdos85

/-- Fix a vertex in one part of a balanced four-coloring of a complete
tripartite graph and split each of the other parts into its four color
classes.  In a rainbow-triangle-free coloring, an off-diagonal block `(i,j)`
can use only colors `i` and `j`.  Let `pᵢⱼ` count the color-`i` edges in that
block.  Exact balance on the opposite side gives `pᵢⱼ + pⱼᵢ = 16`, while the
color-`i` degree budget of the four vertices in class `i` gives outgoing mass
at most `16`.  The six pair equations total `96`, but the four row budgets
total at most `64`. -/
theorem false_of_fourColor_balanced_offDiagonal_blocks
    (p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 : ℕ)
    (h01 : p01 + p10 = 16)
    (h02 : p02 + p20 = 16)
    (h03 : p03 + p30 = 16)
    (h12 : p12 + p21 = 16)
    (h13 : p13 + p31 = 16)
    (h23 : p23 + p32 = 16)
    (h0 : p01 + p02 + p03 ≤ 16)
    (h1 : p10 + p12 + p13 ≤ 16)
    (h2 : p20 + p21 + p23 ≤ 16)
    (h3 : p30 + p31 + p32 ≤ 16) : False := by
  omega

end Erdos85
