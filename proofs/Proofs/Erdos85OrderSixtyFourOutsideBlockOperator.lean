import Proofs.Erdos85OrderSixtyFourComponentComplexGram

/-! # The first operator involving the outside 48-vertex block -/

namespace Erdos85

noncomputable section

/-- If the H-to-outside incidence matrix has row sum six and column sum two,
and the outside graph is six-regular, then the length-three return operator
`B C Bᴴ` has principal eigenvalue `72`.  These are exactly the block degrees
in the seven-component order-64 branch. -/
theorem outsideReturn_mulVec_one_eq_seventyTwo
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    (B : Matrix H O ℂ) (C : Matrix O O ℂ)
    (hB : B.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1))
    (hBt : (Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (2 : ℂ) • (fun _ ↦ 1))
    (hC : C.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1)) :
    ((B * C) * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (72 : ℂ) • (fun _ ↦ 1) := by
  rw [← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul, hB]
  module

/-- The same computation, stated for arbitrary row, column, and middle
degrees. -/
theorem rectangularReturn_mulVec_one
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    (B : Matrix H O ℂ) (C : Matrix O O ℂ) (r s t : ℂ)
    (hB : B.mulVec (fun _ ↦ 1) = r • (fun _ ↦ 1))
    (hBt : (Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      s • (fun _ ↦ 1))
    (hC : C.mulVec (fun _ ↦ 1) = t • (fun _ ↦ 1)) :
    ((B * C) * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (s * t * r) • (fun _ ↦ 1) := by
  rw [← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul, hB]
  module

end

end Erdos85
