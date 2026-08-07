import Proofs.Erdos85OwnerFiberProjectedSquare
import Proofs.Erdos85OneTwentyThreeTraceEscape

/-!
# Restricting the scalar-123 exterior identity to the hard sector

This file turns the projected matrix identity into honest endomorphisms of
the range of the fiber-sum-zero projector.  On that space the restricted
adjacency `S` and lifted defect `T` commute, satisfy `S² = 123 I - T`, and
the trace of `S` is `-135`.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

/-- A projected square identity restricts to an actual square identity on
the range of an invariant idempotent.  Commutation of the two restricted
operators then follows formally because `T = 123 I - S²`. -/
theorem range_restrict_oneTwentyThree_package
    {X : Type*} [Fintype X] [DecidableEq X]
    (A P Q : Matrix X X ℚ)
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
      S * S = (123 : ℚ) • LinearMap.id - T ∧ S * T = T * S := by
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
  have hQL : QL * QL = QL := by
    simpa only [QL, Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hQ
  have htr : LinearMap.trace ℚ (LinearMap.range QL) S = -(135 : ℚ) := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      AL QL hQL hcommAL]
    have hAQ : AL * QL = Matrix.toLin' (A * Q) := by
      simp [AL, QL, Module.End.mul_eq_comp, Matrix.toLin'_mul]
    rw [hAQ, Matrix.trace_toLin'_eq]
    exact htrace
  have hsqLin := congrArg Matrix.toLin' hsq
  have hsqR : S * S = (123 : ℚ) • LinearMap.id - T := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    obtain ⟨w, hw⟩ := v.property
    have hQv : QL (v : X → ℚ) = (v : X → ℚ) := by
      rw [← hw]
      simpa [QL, Module.End.mul_apply] using LinearMap.congr_fun hQL w
    have hv := LinearMap.congr_fun hsqLin (v : X → ℚ)
    simp only [Matrix.toLin'_mul, map_sub, map_smul,
      LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Matrix.toLin'_one, LinearMap.id_apply] at hv
    change AL (AL (QL (v : X → ℚ))) =
      (123 : ℚ) • QL (v : X → ℚ) - PL (QL (v : X → ℚ)) at hv
    rw [hQv] at hv
    change AL (AL (v : X → ℚ)) =
      (123 : ℚ) • (v : X → ℚ) - PL (v : X → ℚ)
    exact hv
  have hT : T = (123 : ℚ) • LinearMap.id - S * S := by
    rw [hsqR]
    abel
  have hcommST : S * T = T * S := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [hT, Module.End.mul_apply]
  exact ⟨htr, hsqR, hcommST⟩

end

end Erdos85
