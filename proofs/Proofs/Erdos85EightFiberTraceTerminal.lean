import Proofs.Erdos85EightFiberProjection
import Proofs.Erdos85OrderSixtyFourBipartiteDefectTrace

/-! # Eight-fiber projection trace terminal

This file joins the elementary entrywise description of four
`K_{8,8}`-minus-matching blocks to the rational primary-trace contradiction.
Its hypotheses are deliberately graph-facing: an eight-element equivalence
partition and the three possible entries of the square of the defect matrix.
-/

namespace Erdos85

noncomputable section

/-- Eight-element equivalence fibers together with the expected defect
codegrees force the four-factor annihilator of the defect operator. -/
theorem eightFiber_aeval_bipartite_defect_polynomial_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Matrix V V ℚ)
    (r : V → V → Prop) [DecidableRel r]
    (hrefl : ∀ x, r x x)
    (hsymm : ∀ {x y}, r x y → r y x)
    (htrans : ∀ {x y z}, r x y → r y z → r x z)
    (hcard : ∀ x,
      ((Finset.univ : Finset V).filter fun y => r x y).card = 8)
    (hdiag : ∀ x, (D * D) x x = 7)
    (hsame : ∀ {x y}, x ≠ y → r x y → (D * D) x y = 6)
    (hdiff : ∀ {x y}, ¬ r x y → (D * D) x y = 0) :
    Polynomial.aeval (Matrix.toLin' D)
      ((Polynomial.X - Polynomial.C (7 : ℚ)) *
       (Polynomial.X - Polynomial.C (1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-1 : ℚ)) *
       (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0 := by
  let P := relationClassMatrix r
  have hDmatrix : D * D = 1 + (6 : ℚ) • P :=
    matrix_sq_eq_one_add_six_relationClassMatrix
      D r hrefl hdiag hsame hdiff
  have hPmatrix : P * P = (8 : ℚ) • P :=
    relationClassMatrix_mul_self_eq_eight r hsymm htrans hcard
  have hDlin : Matrix.toLin' D * Matrix.toLin' D =
      1 + (6 : ℚ) • Matrix.toLin' P := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_add,
      map_smul, Matrix.toLin'_one, Module.End.one_eq_id] using
      congrArg Matrix.toLin' hDmatrix
  have hPlin : Matrix.toLin' P * Matrix.toLin' P =
      (8 : ℚ) • Matrix.toLin' P := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_smul] using
      congrArg Matrix.toLin' hPmatrix
  exact aeval_bipartite_defect_polynomial_eq_zero_of_fourth
    (Matrix.toLin' D)
    (bipartite_defect_fourth_eq_zero_of_square_projection
      (Matrix.toLin' D) (Matrix.toLin' P) hDlin hPlin)

/-- Fully assembled trace contradiction.  The only structural input about the
defect matrix is its eight-fiber codegree table; all spectral bookkeeping is
discharged here. -/
theorem false_of_eightFiber_defect_trace_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (S D : Matrix V V ℚ)
    (r : V → V → Prop) [DecidableRel r]
    (hrefl : ∀ x, r x x)
    (hsymm : ∀ {x y}, r x y → r y x)
    (htrans : ∀ {x y z}, r x y → r y z → r x z)
    (hcard : ∀ x,
      ((Finset.univ : Finset V).filter fun y => r x y).card = 8)
    (hdiag : ∀ x, (D * D) x x = 7)
    (hsame : ∀ {x y}, x ≠ y → r x y → (D * D) x y = 6)
    (hdiff : ∀ {x y}, ¬ r x y → (D * D) x y = 0)
    (hcomm : Matrix.toLin' S * Matrix.toLin' D =
      Matrix.toLin' D * Matrix.toLin' S)
    (htotal : LinearMap.trace ℚ (V → ℚ) (Matrix.toLin' S) = 0)
    (h7 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S) (Matrix.toLin' D) hcomm
        (Polynomial.X - Polynomial.C (7 : ℚ))) = 8)
    (h1 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S) (Matrix.toLin' D) hcomm
        (Polynomial.X - Polynomial.C (1 : ℚ))) = 0)
    (hm1 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S) (Matrix.toLin' D) hcomm
        (Polynomial.X - Polynomial.C (-1 : ℚ))) = 0)
    (hm7 : LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' S) (Matrix.toLin' D) hcomm
        (Polynomial.X - Polynomial.C (-7 : ℚ))) = 0) : False := by
  apply false_of_bipartite_defect_four_sector_traces
    (Matrix.toLin' S) (Matrix.toLin' D) hcomm
    (eightFiber_aeval_bipartite_defect_polynomial_eq_zero
      D r hrefl hsymm htrans hcard hdiag hsame hdiff)
    htotal h7 h1 hm1 hm7

end

end Erdos85
