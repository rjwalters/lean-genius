import Proofs.Erdos85CubicTraceParity
import Proofs.Erdos85C4FreeRegularAdjacencyCube
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger
import Proofs.Erdos85CubicTraceHistogramExcess
import Proofs.Erdos85ServiceSixthTraceDivisibility

/-! # Sixth adjacency trace modulo four -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- For a symmetric integer table with even diagonal, its square mass is
congruent modulo four to its total mass minus its diagonal mass. -/
theorem four_dvd_sum_sq_sub_sum_add_diag_of_symmetric_even_diag
    {X : Type*} (s : Finset X) (f : X → X → ℤ)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i)
    (hdiag : ∀ i ∈ s, Even (f i i)) :
    (4 : ℤ) ∣
      (∑ i ∈ s, ∑ j ∈ s, (f i j) ^ 2) -
        (∑ i ∈ s, ∑ j ∈ s, f i j) + ∑ i ∈ s, f i i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hsymm_s : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i := by
        intro i hi j hj
        exact hsymm i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj)
      have hdiag_s : ∀ i ∈ s, Even (f i i) := by
        intro i hi
        exact hdiag i (Finset.mem_insert_of_mem hi)
      obtain ⟨r, hr⟩ := ih hsymm_s hdiag_s
      obtain ⟨d, hd⟩ := hdiag a (Finset.mem_insert_self a s)
      have hcross : (∑ i ∈ s, f i a) = ∑ i ∈ s, f a i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsymm i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s)
      have hcrossSq : (∑ i ∈ s, (f i a) ^ 2) =
          ∑ i ∈ s, (f a i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsymm i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s)]
      have hcrossEven : Even (∑ i ∈ s, ((f a i) ^ 2 - f a i)) := by
        apply Finset.even_sum
        intro i hi
        simpa [pow_two, mul_sub] using Int.even_mul_pred_self (f a i)
      obtain ⟨q, hq⟩ := hcrossEven
      have hq' : (∑ i ∈ s, (f a i) ^ 2) - (∑ i ∈ s, f a i) = q + q := by
        rw [← Finset.sum_sub_distrib]
        exact hq
      refine ⟨r + d ^ 2 + q, ?_⟩
      simp_rw [Finset.sum_insert ha]
      simp only [Finset.sum_add_distrib]
      rw [hcross, hcrossSq, hd]
      linear_combination hr + 2 * hq'

/-- For a 6-regular graph on 48 vertices, the sixth adjacency trace is
congruent modulo four to twice its triangle count. -/
theorem sixRegular_fortyEight_trace_pow_six_mod_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (4 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) -
      2 * (adjacencyTriangleMinorFinset G).card := by
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
  have hrow (i : V) : (∑ j : V, B i j) = 216 := by
    rw [hBmul]
    simpa [A] using regular_adjMatrix_cube_row_sum G 6 hreg i
  have htotal : (∑ i : V, ∑ j : V, B i j) = 10368 := by
    calc
      _ = ∑ _i : V, (216 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hrow i
      _ = 10368 := by simp [hcard]
  have htrace : Matrix.trace B =
      6 * (adjacencyTriangleMinorFinset G).card := by
    rw [hBmul]
    simpa [A] using
      trace_adjMatrix_cube_eq_six_mul_triangleMinorCount G (by omega)
  have hdiagSum : (∑ i : V, B i i) =
      6 * (adjacencyTriangleMinorFinset G).card := by
    simpa [Matrix.trace, Matrix.diag] using htrace
  rw [hsquares, htotal, hdiagSum] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k + 2592 - 2 * (adjacencyTriangleMinorFinset G).card, ?_⟩
  linear_combination hk

/-- Histogram-facing form: the global cubic excess is congruent modulo four
to twice the triangle count. -/
theorem sixRegular_fortyEight_histogramExcess_mod_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let E : ℤ := ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4))
    (4 : ℤ) ∣ E - 2 * (adjacencyTriangleMinorFinset G).card := by
  dsimp only
  have hmod := sixRegular_fortyEight_trace_pow_six_mod_four G hcard hreg
  rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    G hfree hcard hreg] at hmod
  obtain ⟨k, hk⟩ := hmod
  refine ⟨k - 15264, ?_⟩
  linear_combination hk

/-- If the triangle count is even, the mod-four congruence combines with
sixth-trace divisibility by six to move the strict threshold to the next
multiple of twelve. -/
theorem sixRegular_fortyEight_strict_trace_six_ge_61260_of_even_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6))
    (hTeven : Even (adjacencyTriangleMinorFinset G).card) :
    61260 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  obtain ⟨k, hk⟩ := six_dvd_sixRegular_fortyEight_trace_pow_six
    G hcard hreg
  obtain ⟨m, hm⟩ := sixRegular_fortyEight_trace_pow_six_mod_four
    G hcard hreg
  obtain ⟨t, ht⟩ := hTeven
  omega

/-- With even triangle count, the global cubic histogram excess is at least
`204`, rather than the unconditional congruence threshold `198`. -/
theorem sixRegular_fortyEight_histogramExcess_ge_204_of_even_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6))
    (hTeven : Even (adjacencyTriangleMinorFinset G).card) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    204 ≤ ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4)) := by
  dsimp only
  have htrace :=
    sixRegular_fortyEight_strict_trace_six_ge_61260_of_even_triangles
      G hcard hreg hstrict hTeven
  rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    G hfree hcard hreg] at htrace
  omega

end

end Erdos85

#print axioms
  Erdos85.four_dvd_sum_sq_sub_sum_add_diag_of_symmetric_even_diag
#print axioms Erdos85.sixRegular_fortyEight_trace_pow_six_mod_four
#print axioms Erdos85.sixRegular_fortyEight_histogramExcess_mod_four
#print axioms
  Erdos85.sixRegular_fortyEight_histogramExcess_ge_204_of_even_triangles
