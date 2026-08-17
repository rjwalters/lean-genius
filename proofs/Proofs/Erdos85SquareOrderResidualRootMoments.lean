import Proofs.Erdos85HermitianCharpolyPowerSums
import Proofs.Erdos85SquareOrderAdjacencyMoments
import Proofs.Erdos85SquareOrderHighQuadraticResidual

/-!
# Uniform residual root moments at square order

After removing the forced high-vertex quadratic sector
`(X^2 - d)^(h-1)`, the remaining adjacency characteristic polynomial has
second and fourth root moments depending only on `d` and the high count `h`.
This is the scale-free version of the order-49 residual calculation.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem exists_squareOrder_residualCharpoly_rootMoments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    ∃ Q : ℚ[X],
      Q.Monic ∧
      (G.adjMatrix ℚ).charpoly =
        (X ^ 2 - C (d : ℚ)) ^
          ((squareOrderHighVertices G d).card - 1) * Q ∧
      Q.natDegree =
        d * d - 2 * ((squareOrderHighVertices G d).card - 1) ∧
      Q.nextCoeff = 0 ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 =
        (d : ℂ) ^ 3 + 2 * d +
          (1 - 2 * d) * ((squareOrderHighVertices G d).card : ℂ) ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 =
        2 * (d : ℂ) ^ 4 - d ^ 3 + 2 * d ^ 2 +
          (4 * d + 1 - 2 * d ^ 2) *
            ((squareOrderHighVertices G d).card : ℂ) := by
  let H := squareOrderHighVertices G d
  obtain ⟨Q, hQmonic, hfactor, hdegree, hnext⟩ :=
    exists_monic_squareOrder_residualCharpoly_nextCoeff_zero
      G hfree hd hmin hcover hcard ha
  have hfactorM : (G.adjMatrix ℚ).charpoly =
      (X ^ 2 - C (d : ℚ)) ^ (H.card - 1) * Q := by
    simpa [H, Matrix.charpoly_toLin'] using hfactor
  have hsplit := rational_quadratic_factor_complexRootPowerSums
    (P := (G.adjMatrix ℚ).charpoly) (Q := Q) d (H.card - 1)
      hfactorM hQmonic.ne_zero
  have hdcast : ((d : ℚ) : ℂ) = (d : ℂ) := by norm_num
  rw [hdcast] at hsplit
  have hHpos : 1 ≤ H.card :=
    Finset.one_le_card.mpr ⟨a, ha⟩
  have htraceTwo : Matrix.trace ((G.adjMatrix ℤ) ^ 2) =
      (d : ℤ) ^ 3 + (H.card : ℤ) := by
    simpa [H, pow_two] using
      (trace_squareOrder_adjMatrix_sq G hfree hd hmin hcover hcard)
  have htraceFour : Matrix.trace ((G.adjMatrix ℤ) ^ 4) =
      2 * (d : ℤ) ^ 4 - d ^ 3 + (4 * d + 1) * (H.card : ℤ) := by
    rw [show (G.adjMatrix ℤ) ^ 4 =
        ((G.adjMatrix ℤ) * (G.adjMatrix ℤ)) *
          ((G.adjMatrix ℤ) * (G.adjMatrix ℤ)) by noncomm_ring]
    simpa [H] using
      (trace_squareOrder_adjMatrix_fourth G hfree hd hmin hcover hcard)
  have hambientTwo :
      complexRootPowerSum
          ((G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)) 2 =
        (d : ℂ) ^ 3 + (H.card : ℂ) := by
    rw [complexRootPowerSum_ratAdjCharpoly_eq_trace_pow,
      trace_complex_adjMatrix_pow_eq_intCast, htraceTwo]
    push_cast
    ring
  have hambientFour :
      complexRootPowerSum
          ((G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)) 4 =
        2 * (d : ℂ) ^ 4 - d ^ 3 +
          (4 * d + 1) * (H.card : ℂ) := by
    rw [complexRootPowerSum_ratAdjCharpoly_eq_trace_pow,
      trace_complex_adjMatrix_pow_eq_intCast, htraceFour]
    push_cast
    ring
  have hkcast : ((H.card - 1 : ℕ) : ℂ) = (H.card : ℂ) - 1 := by
    rw [Nat.cast_sub hHpos]
    norm_num
  have hresTwo : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 =
      (d : ℂ) ^ 3 + 2 * d + (1 - 2 * d) * (H.card : ℂ) := by
    rw [hambientTwo] at hsplit
    rw [hkcast] at hsplit
    linear_combination -hsplit.1
  have hresFour : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 =
      2 * (d : ℂ) ^ 4 - d ^ 3 + 2 * d ^ 2 +
        (4 * d + 1 - 2 * d ^ 2) * (H.card : ℂ) := by
    rw [hambientFour] at hsplit
    rw [hkcast] at hsplit
    linear_combination -hsplit.2
  refine ⟨Q, hQmonic, hfactorM, ?_, hnext, hresTwo, hresFour⟩
  simpa [H] using hdegree

end

end Erdos85
