import Proofs.Erdos85HermitianCharpolyPowerSums
import Proofs.Erdos85SquareOrderAdjacencyMoments
import Proofs.Erdos85SquareOrderHighQuadraticResidual

/-!
# Exact root moments of the order-49 residual characteristic polynomial

This joins the certified high-quadratic factorization to the exact adjacency
walk moments.  The residual quotient has complex-root power sums
`357 - 13h` and `4557 - 69h`, where `h` is the number of degree-eight
vertices.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem exists_orderFortyNineSeven_residualCharpoly_rootMoments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ Q : ℚ[X],
      Q.Monic ∧
      (G.adjMatrix ℚ).charpoly =
        (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1) * Q ∧
      Q.natDegree = 49 - 2 * ((squareOrderHighVertices G 7).card - 1) ∧
      Q.nextCoeff = 0 ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 =
        357 - 13 * ((squareOrderHighVertices G 7).card : ℂ) ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 =
        4557 - 69 * ((squareOrderHighVertices G 7).card : ℂ) := by
  let H := squareOrderHighVertices G 7
  obtain ⟨Q, hQmonic, hfactor, hdegree, hnext⟩ :=
    exists_monic_squareOrder_residualCharpoly_nextCoeff_zero
      G hfree (d := 7) (by norm_num) hmin hcover
        (by norm_num [hcard]) ha
  have hfactorM : (G.adjMatrix ℚ).charpoly =
      (X ^ 2 - C 7) ^ (H.card - 1) * Q := by
    simpa [H, Matrix.charpoly_toLin'] using hfactor
  have hsplit := rational_quadratic_factor_complexRootPowerSums
    (P := (G.adjMatrix ℚ).charpoly) (Q := Q) 7 (H.card - 1)
      hfactorM hQmonic.ne_zero
  have hHpos : 1 ≤ H.card := by
    exact Finset.one_le_card.mpr ⟨a, ha⟩
  have htraceTwo : Matrix.trace ((G.adjMatrix ℤ) ^ 2) =
      343 + (H.card : ℤ) := by
    simpa [H, pow_two] using
      (trace_squareOrder_adjMatrix_sq G hfree (d := 7) (by norm_num)
        hmin hcover (by norm_num [hcard]))
  have htraceFour : Matrix.trace ((G.adjMatrix ℤ) ^ 4) =
      4459 + 29 * (H.card : ℤ) := by
    rw [show (G.adjMatrix ℤ) ^ 4 =
        ((G.adjMatrix ℤ) * (G.adjMatrix ℤ)) *
          ((G.adjMatrix ℤ) * (G.adjMatrix ℤ)) by noncomm_ring]
    simpa [H] using
      (trace_squareOrder_adjMatrix_fourth G hfree (d := 7) (by norm_num)
        hmin hcover (by norm_num [hcard]))
  have hambientTwo :
      complexRootPowerSum
          ((G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)) 2 =
        343 + (H.card : ℂ) := by
    rw [complexRootPowerSum_ratAdjCharpoly_eq_trace_pow,
      trace_complex_adjMatrix_pow_eq_intCast, htraceTwo]
    push_cast
    ring
  have hambientFour :
      complexRootPowerSum
          ((G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)) 4 =
        4459 + 29 * (H.card : ℂ) := by
    rw [complexRootPowerSum_ratAdjCharpoly_eq_trace_pow,
      trace_complex_adjMatrix_pow_eq_intCast, htraceFour]
    push_cast
    ring
  have hkcast : ((H.card - 1 : ℕ) : ℂ) = (H.card : ℂ) - 1 := by
    rw [Nat.cast_sub hHpos]
    norm_num
  have hresTwo : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 =
      357 - 13 * (H.card : ℂ) := by
    rw [hambientTwo] at hsplit
    rw [hkcast] at hsplit
    linear_combination -hsplit.1
  have hresFour : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 =
      4557 - 69 * (H.card : ℂ) := by
    rw [hambientFour] at hsplit
    rw [hkcast] at hsplit
    linear_combination -hsplit.2
  refine ⟨Q, hQmonic, hfactorM, ?_, hnext, hresTwo, hresFour⟩
  simpa [H] using hdegree

end

end Erdos85
