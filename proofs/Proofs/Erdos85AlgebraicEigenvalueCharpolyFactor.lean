import Proofs.Erdos85CyclePrimaryQuadraticTerminals
import Proofs.Erdos85CycleDefectPrimaryClassification

/-! # Algebraic eigenvalues force rational characteristic factors -/

/-!
The general eigenvalue-to-divisibility theorem below is unconditional.  In
the order-64 application, `D` should be the 7-regular defect-block operator,
not the separate two-regular cycle operator.  The helper based on the full
matrix identity `D = 7I-A²` is generic and is not the simultaneous-sector
connector used by that graph branch.  The graph block identity has an
additional positive-semidefinite exterior Gram term; this helper applies to a
graph direction only when that term vanishes.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- If an algebraic number is an eigenvalue of a rational matrix after
extension to the algebraic closure, its minimal polynomial over `ℚ` divides
the original rational characteristic polynomial. -/
theorem minpoly_dvd_matrix_charpoly_of_algebraic_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℚ) (μ : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (M.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = μ • v) :
    minpoly ℚ μ ∣ M.charpoly := by
  let ι : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hev : Module.End.HasEigenvector (M.map ι).toLin' μ v := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simpa [ι, Matrix.toLin'_apply] using heigen, hv0⟩
  have hroot : (M.map ι).charpoly.IsRoot μ := by
    rw [← Matrix.charpoly_toLin']
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
      (Module.End.hasEigenvalue_of_hasEigenvector hev)
  apply minpoly.dvd ℚ μ
  rw [Matrix.charpoly_map] at hroot
  simpa [Polynomial.aeval_def, Polynomial.eval_map, ι] using hroot.eq_zero

/-- Under the H16 square-trace budget, an actual eigenvalue of a rational
Hermitian defect matrix cannot have any of the four oversized cycle-primary
minimal polynomials. -/
theorem algebraic_eigenvector_minpoly_ne_large_cycle_primaries
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) (μ : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (D.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = μ • v)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    minpoly ℚ μ ≠ cycleDefectCubicSeven.map (Int.castRingHom ℚ) ∧
    minpoly ℚ μ ≠ cycleDefectCubicNine.map (Int.castRingHom ℚ) ∧
    minpoly ℚ μ ≠ cycleDefectQuinticEleven.map (Int.castRingHom ℚ) ∧
    minpoly ℚ μ ≠ cycleDefectSexticThirteen.map (Int.castRingHom ℚ) := by
  have hdvd := minpoly_dvd_matrix_charpoly_of_algebraic_eigenvector
    D μ v hv0 heigen
  constructor
  · intro h
    apply false_of_cycleDefectCubicSeven_dvd_rational_charpoly D
      (h ▸ hdvd) hD htrace
  constructor
  · intro h
    apply false_of_cycleDefectCubicNine_dvd_rational_charpoly D
      (h ▸ hdvd) hD htrace
  constructor
  · intro h
    apply false_of_cycleDefectQuinticEleven_dvd_rational_charpoly D
      (h ▸ hdvd) hD htrace
  · intro h
    apply false_of_cycleDefectSexticThirteen_dvd_rational_charpoly D
      (h ▸ hdvd) hD htrace

/-- The same eigenvector-to-divisibility bridge closes the C16 quadratic
once the 15-dimensional trace `-7` and square-trace budget are supplied. -/
theorem algebraic_eigenvector_minpoly_ne_cycleDefectQuadraticSixteen
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) (μ : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (D.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = μ • v)
    (hcard : Fintype.card n = 15)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : Matrix.trace (D.map (algebraMap ℚ ℂ)) = -7)
    (htraceSq :
      (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    minpoly ℚ μ ≠
      cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ) := by
  intro hmin
  have hdvd := minpoly_dvd_matrix_charpoly_of_algebraic_eigenvector
    D μ v hv0 heigen
  exact false_of_cycleDefectQuadraticSixteen_dvd_rational_charpoly
    D hcard (hmin ▸ hdvd) hD htrace htraceSq

theorem algebraic_eigenvector_minpoly_ne_cycleDefectQuadraticFive
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) (μ : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (D.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = μ • v)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : Matrix.trace (D.map (algebraMap ℚ ℂ)) = -7)
    (htraceSq :
      (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    minpoly ℚ μ ≠ cycleDefectQuadraticFive.map (Int.castRingHom ℚ) := by
  intro hmin
  have hdvd := minpoly_dvd_matrix_charpoly_of_algebraic_eigenvector
    D μ v hv0 heigen
  exact false_of_cycleDefectQuadraticFive_dvd_rational_charpoly
    D (hmin ▸ hdvd) hD htrace htraceSq

/-- Intersecting the complete cycle-primary census with all six nonlinear
moment exclusions leaves only the four rational linear primaries. -/
theorem cycle_primary_of_budget_forces_rational_linear
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) (μ : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (D.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = μ • v)
    (hprimary : OrderSixteenCycleDefectPrimaryClass μ)
    (hcard : Fintype.card n = 15)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : Matrix.trace (D.map (algebraMap ℚ ℂ)) = -7)
    (htraceSq :
      (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    minpoly ℚ μ = X - C 3 ∨
    minpoly ℚ μ = X - C 5 ∨
    minpoly ℚ μ = X - C 6 ∨
    minpoly ℚ μ = X - C 7 := by
  have hlarge := algebraic_eigenvector_minpoly_ne_large_cycle_primaries
    D μ v hv0 heigen hD htraceSq
  have hsixteen :=
    algebraic_eigenvector_minpoly_ne_cycleDefectQuadraticSixteen
      D μ v hv0 heigen hcard hD htrace htraceSq
  have hfive := algebraic_eigenvector_minpoly_ne_cycleDefectQuadraticFive
    D μ v hv0 heigen hD htrace htraceSq
  rcases hprimary with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd h hfive
  · exact absurd h hsixteen
  · exact absurd h hlarge.1
  · exact absurd h hlarge.2.1
  · exact absurd h hlarge.2.2.1
  · exact absurd h hlarge.2.2.2

/-- The generic rational matrix polynomial `7I - A²`.  It models the
order-64 defect relation only on the exterior-incidence kernel. -/
def sevenMinusSquareMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) : Matrix n n ℚ :=
  7 • (1 : Matrix n n ℚ) - A ^ 2

/-- For the generic matrix polynomial above, an eigenvalue `α` transports to
`7-α²`; under the stated H16-style budget its minimal polynomial therefore
avoids all four oversized cycle primaries.  In the graph application this is
the exterior-incidence-kernel specialization, not the general block relation. -/
theorem seven_sub_sq_eigenvalue_minpoly_ne_large_cycle_primaries
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (α : AlgebraicClosure ℚ)
    (v : n → AlgebraicClosure ℚ) (hv0 : v ≠ 0)
    (heigen :
      (A.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = α • v)
    (hD : ((sevenMinusSquareMatrix A).map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace
      (((sevenMinusSquareMatrix A).map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    minpoly ℚ (7 - α ^ 2) ≠
        cycleDefectCubicSeven.map (Int.castRingHom ℚ) ∧
    minpoly ℚ (7 - α ^ 2) ≠
        cycleDefectCubicNine.map (Int.castRingHom ℚ) ∧
    minpoly ℚ (7 - α ^ 2) ≠
        cycleDefectQuinticEleven.map (Int.castRingHom ℚ) ∧
    minpoly ℚ (7 - α ^ 2) ≠
        cycleDefectSexticThirteen.map (Int.castRingHom ℚ) := by
  have heigen2 :
      ((A.map (algebraMap ℚ (AlgebraicClosure ℚ))) ^ 2).mulVec v =
        (α ^ 2) • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul, heigen,
      smul_smul]
    simp [pow_two]
  have hseven :
      (7 : Matrix n n ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      (7 : Matrix n n (AlgebraicClosure ℚ)) := by
    rw [Matrix.map_ofNat]
    · ext i j
      by_cases hij : i = j <;>
        simp [Matrix.ofNat_apply, hij]
    · simp
  have hmap :
      (sevenMinusSquareMatrix A).map
          (algebraMap ℚ (AlgebraicClosure ℚ)) =
        7 • (1 : Matrix n n (AlgebraicClosure ℚ)) -
          (A.map (algebraMap ℚ (AlgebraicClosure ℚ))) ^ 2 := by
    ext i j
    simp [sevenMinusSquareMatrix, pow_two, Matrix.mul_apply]
    exact congrFun (congrFun hseven i) j
  have hdefect :
      ((sevenMinusSquareMatrix A).map
        (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v =
          (7 - α ^ 2) • v := by
    rw [hmap, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      heigen2]
    rw [← Nat.cast_smul_eq_nsmul (R := AlgebraicClosure ℚ)]
    exact (sub_smul (7 : AlgebraicClosure ℚ) (α ^ 2) v).symm
  exact algebraic_eigenvector_minpoly_ne_large_cycle_primaries
    (sevenMinusSquareMatrix A) (7 - α ^ 2) v hv0 hdefect hD htrace

end

end Erdos85
