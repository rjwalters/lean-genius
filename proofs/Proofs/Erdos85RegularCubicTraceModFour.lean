import Proofs.Erdos85CubicTraceModFour

/-! # Arbitrary-parameter sixth adjacency trace modulo four

Node: F.3 GENERALIZATION.  The cubic parity argument does not depend on
degree six or order 48; those parameters enter only through the total cubic
row mass.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- In a finite `d`-regular graph, the sixth adjacency trace differs modulo
four from the total cubic row mass by the signed cubic diagonal mass. -/
theorem regular_trace_pow_six_mod_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ x, G.degree x = d)
    (hcard : 3 ≤ Fintype.card V) :
    (4 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) -
      (Fintype.card V : ℤ) * (d : ℤ) ^ 3 +
        6 * (adjacencyTriangleMinorFinset G).card := by
  classical
  let A := G.adjMatrix ℤ
  let B := A ^ 3
  have hBmul : B = A * A * A := by
    simp [B, pow_succ, Matrix.mul_assoc]
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  have hB : B.IsSymm := hA.pow 3
  have hsymm : ∀ i ∈ (Finset.univ : Finset V),
      ∀ j ∈ (Finset.univ : Finset V), B i j = B j i := by
    intro i _ j _
    exact congrFun (congrFun hB.eq j) i
  have hdiag : ∀ i ∈ (Finset.univ : Finset V), Even (B i i) := by
    intro i _
    simpa [A, B, pow_succ] using even_adjMatrix_cube_apply_self G i
  have hdiv := four_dvd_sum_sq_sub_sum_add_diag_of_symmetric_even_diag
    (Finset.univ : Finset V) B hsymm hdiag
  have hsquares : (∑ i : V, ∑ j : V, (B i j) ^ 2) =
      Matrix.trace (A ^ 6) := by
    rw [trace_pow_six_eq_sum_cube_apply_sq A hA]
  have hrow (i : V) : (∑ j : V, B i j) = (d : ℤ) ^ 3 := by
    rw [hBmul]
    simpa [A] using regular_adjMatrix_cube_row_sum G d hreg i
  have htotal : (∑ i : V, ∑ j : V, B i j) =
      (Fintype.card V : ℤ) * (d : ℤ) ^ 3 := by
    calc
      _ = ∑ _i : V, ((d : ℤ) ^ 3) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hrow i
      _ = (Fintype.card V : ℤ) * (d : ℤ) ^ 3 := by simp
  have htrace : Matrix.trace B =
      6 * (adjacencyTriangleMinorFinset G).card := by
    rw [hBmul]
    simpa [A] using
      trace_adjMatrix_cube_eq_six_mul_triangleMinorCount G hcard
  have hdiagSum : (∑ i : V, B i i) =
      6 * (adjacencyTriangleMinorFinset G).card := by
    simpa [Matrix.trace, Matrix.diag] using htrace
  simpa [hsquares, htotal, hdiagSum] using hdiv

/-- The former degree-six/order-48 congruence is a specialization of the
parameter-free statement. -/
theorem sixRegular_fortyEight_trace_pow_six_mod_four_of_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (4 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) -
      2 * (adjacencyTriangleMinorFinset G).card := by
  obtain ⟨k, hk⟩ := regular_trace_pow_six_mod_four G 6 hreg (by omega)
  refine ⟨k + 2592 - 2 * (adjacencyTriangleMinorFinset G).card, ?_⟩
  norm_num [hcard] at hk ⊢
  linear_combination hk

end

end Erdos85

#print axioms Erdos85.regular_trace_pow_six_mod_four
#print axioms Erdos85.sixRegular_fortyEight_trace_pow_six_mod_four_of_general
