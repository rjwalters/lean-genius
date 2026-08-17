import Proofs.Erdos85OrderSixtyFourResidualTrace

/-! # The defect minus-one sector has zero trace at order 64 -/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

private theorem trace_zero_of_square_eight
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (f : E →ₗ[ℚ] E)
    (hf : f * f = (8 : ℚ) • LinearMap.id) :
    LinearMap.trace ℚ E f = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim f (0 : E →ₗ[ℚ] E)]
    exact map_zero _
  · exact LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat
      f 8 (by norm_num) hf

/-- On the complete-block eigenvalue `-1` of the defect graph, adjacency
squares to `8I`; irrationality of `√8` forces zero rational trace. -/
theorem orderSixtyFour_minusOne_defect_sector_trace_eq_zero
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
        (by
          simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
            congrArg Matrix.toLin'
              (adjMatrix_comm_secondOrderDefect_of_regular_rat
                G hfree
                  (orderSixtyFour_regular_of_tightCover
                    G hfree hmin hcover)))
        (X - C (-1 : ℚ))) = 0 := by
  classical
  let D := secondOrderDefectGraph G
  let S := Matrix.toLin' (G.adjMatrix ℚ)
  let T := Matrix.toLin' (D.adjMatrix ℚ)
  let J := Matrix.toLin' (ratOnesMatrix (Fin 64))
  have hkernel := orderSixtyFour_regular_defect_kernel G hfree hmin hcover
  have hreg : ∀ x : Fin 64, G.degree x = 8 := hkernel.1
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hcommM := adjMatrix_comm_secondOrderDefect_of_regular_rat
    G hfree hreg
  have hcomm : S * T = T * S := by
    simpa only [S, T, Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  have hsqM := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    G hfree hreg
  have hsq : S * S = (7 : ℚ) • (1 : (Fin 64 → ℚ) →ₗ[ℚ] (Fin 64 → ℚ)) +
      J - T := by
    have hh := congrArg Matrix.toLin' hsqM
    simp only [S, T, J, Module.End.mul_eq_comp, Matrix.toLin'_mul,
      map_add, map_sub, map_smul, Matrix.toLin'_one] at hh ⊢
    norm_num at hh
    exact hh
  have hJTM := ratOnesMatrix_mul_adjMatrix_of_regular D hDreg
  have hJT : J * T = (7 : ℚ) • J := by
    have hh := congrArg Matrix.toLin' hJTM
    simp only [J, T, Module.End.mul_eq_comp, Matrix.toLin'_mul,
      map_smul] at hh ⊢
    norm_num at hh
    exact hh
  have hsector := kerAevalRestrict_X_sub_C_sq
    S T J hcomm hsq hJT (show (-1 : ℚ) ≠ 7 by norm_num)
  have hsector8 :
      kerAevalRestrict S T hcomm (X - C (-1 : ℚ)) *
          kerAevalRestrict S T hcomm (X - C (-1 : ℚ)) =
        (8 : ℚ) • LinearMap.id := by
    convert hsector using 1 <;> norm_num
  exact trace_zero_of_square_eight _ hsector8

end

end Erdos85
