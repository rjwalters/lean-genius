import Proofs.Erdos85SymmetricRestrictionSemisimple
import Proofs.Erdos85OneTwentyThreeHardSector

/-!
# Semisimplicity in the scalar-123 hard-sector package

This strengthens the existing restriction package with the fact that the
restricted defect operator is semisimple.  It is the direct graph-to-arithmetic
interface needed to peel the principal frequency `μ = 2`.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

/-- The scalar-123 hard-sector package, strengthened with semisimplicity of
the restricted defect operator when the ambient defect matrix is symmetric. -/
theorem range_restrict_oneTwentyThree_semisimple_package
    {X : Type*} [Fintype X] [DecidableEq X]
    (A P Q : Matrix X X ℚ)
    (hPsymm : P.IsSymm)
    (hQ : Q * Q = Q) (hcommA : A * Q = Q * A)
    (hcommP : P * Q = Q * P)
    (htrace : Matrix.trace (A * Q) = -(135 : ℚ))
    (hsq : (A * A) * Q =
      ((123 : ℚ) • (1 : Matrix X X ℚ) - P) * Q) :
    let AL := A.toLin'
    let PL := P.toLin'
    let QL := Q.toLin'
    let hA := mapsTo_range_of_commute AL QL (by
      simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hcommA)
    let hP := mapsTo_range_of_commute PL QL (by
      simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hcommP)
    let S := AL.restrict hA
    let T := PL.restrict hP
    LinearMap.trace ℚ (LinearMap.range QL) S = -(135 : ℚ) ∧
      S * S = (123 : ℚ) • LinearMap.id - T ∧ S * T = T * S ∧
        Module.End.IsSemisimple T := by
  dsimp only
  let AL := A.toLin'
  let PL := P.toLin'
  let QL := Q.toLin'
  have hcommAL : AL * QL = QL * AL := by
    simpa only [AL, QL, Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommA
  have hcommPL : PL * QL = QL * PL := by
    simpa only [PL, QL, Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommP
  let hA := mapsTo_range_of_commute AL QL hcommAL
  let hP := mapsTo_range_of_commute PL QL hcommPL
  let S := AL.restrict hA
  let T := PL.restrict hP
  obtain ⟨htr, hsqR, hcommST⟩ :=
    range_restrict_oneTwentyThree_package A P Q hQ hcommA hcommP htrace hsq
  have hsemi : Module.End.IsSemisimple T := by
    exact restrict_isSemisimple_of_isSymm hPsymm (LinearMap.range QL) hP
  exact ⟨htr, hsqR, hcommST, hsemi⟩

end

end Erdos85
