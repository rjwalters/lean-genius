import Proofs.Erdos85AbstractTraceEscape

/-!
# Residual trace escape at binary square order

For a regular square-order candidate put `A` for ambient adjacency, `D` for
the second-order defect adjacency, and `J` for the all-ones operator.  The
shifted defect operator `T = D - J` removes the rank-one term globally:

`A² = (q - 1) I - T`.

This file is the graph-facing bridge to `abstract_residual_trace_eq_zero`.
It deliberately leaves the annihilator and its arithmetic certificate as
inputs: controlling the square-in-eigenfield factors is the remaining
`NONBIP-CONNECTED [q]` problem.
-/

open Polynomial
open SimpleGraph

namespace Erdos85

noncomputable section

/-- A regular adjacency matrix commutes with the rational all-ones matrix. -/
theorem adjMatrix_comm_ratOnesMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ x, G.degree x = q) :
    G.adjMatrix ℚ * ratOnesMatrix V =
      ratOnesMatrix V * G.adjMatrix ℚ := by
  have hJA := ratOnesMatrix_mul_adjMatrix_of_regular G hreg
  have hAJ : G.adjMatrix ℚ * ratOnesMatrix V =
      (q : ℚ) • ratOnesMatrix V := by
    have hJt : (ratOnesMatrix V).transpose = ratOnesMatrix V := by
      ext i j
      simp [ratOnesMatrix]
    have h := congrArg Matrix.transpose hJA
    rw [Matrix.transpose_mul, Matrix.transpose_smul, hJt,
      SimpleGraph.isSymm_adjMatrix] at h
    exact h
  rw [hAJ, hJA]

/-- **Binary-square graph-facing residual trace escape.**

The shifted defect `D-J` satisfies the exact no-rank-one square identity
required by `abstract_residual_trace_eq_zero`.  Consequently every residual
primary sector avoiding the designated shifted principal value has zero
ambient-adjacency trace whenever the stated irreducible-factor norm
certificate holds. -/
theorem binarySquare_regular_shiftedDefect_residual_trace_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    {gP : ℚ[X]}
    (hgP : Polynomial.aeval
      (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ -
        ratOnesMatrix V)) gP = 0)
    {r : ℚ[X]}
    (hrPrincipal : r.eval ((q : ℚ) - 1 - (q * q : ℕ)) ≠ 0)
    (hrdvd : r ∣ minpoly ℚ
      (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ -
        ratOnesMatrix V)))
    (harith : ∀ f : ℚ[X], f.Monic → Irreducible f → f ∣ gP →
      f ≠ X - C ((q : ℚ) - 1 - (q * q : ℕ)) →
        ¬ IsSquare (f.eval ((q : ℚ) - 1))) :
    LinearMap.trace ℚ _
      (kerAevalRestrict
        (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ -
          ratOnesMatrix V))
        (by
          apply toLin'_comm_of_matrix_comm
          have hAD := adjMatrix_comm_secondOrderDefect_of_regular_rat
            G hfree hreg
          have hAJ := adjMatrix_comm_ratOnesMatrix_of_regular G hreg
          rw [Matrix.mul_sub, Matrix.sub_mul, hAD, hAJ])
        r) = 0 := by
  let A := Matrix.toLin' (G.adjMatrix ℚ)
  let T := Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ -
    ratOnesMatrix V)
  have hcommM : G.adjMatrix ℚ *
        ((secondOrderDefectGraph G).adjMatrix ℚ - ratOnesMatrix V) =
      ((secondOrderDefectGraph G).adjMatrix ℚ - ratOnesMatrix V) *
        G.adjMatrix ℚ := by
    have hAD := adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
    have hAJ := adjMatrix_comm_ratOnesMatrix_of_regular G hreg
    rw [Matrix.mul_sub, Matrix.sub_mul, hAD, hAJ]
  have hcomm : A * T = T * A := by
    exact toLin'_comm_of_matrix_comm hcommM
  have hsqM : G.adjMatrix ℚ * G.adjMatrix ℚ =
      ((q : ℚ) - 1) • (1 : Matrix V V ℚ) -
        ((secondOrderDefectGraph G).adjMatrix ℚ - ratOnesMatrix V) := by
    rw [adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat G hfree hreg]
    abel
  have hsq : A * A =
      ((q : ℚ) - 1) • (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) - T := by
    have h := congrArg Matrix.toLin' hsqM
    rw [Matrix.toLin'_mul, map_sub, map_smul, Matrix.toLin'_one] at h
    simpa [A, T, Module.End.mul_eq_comp, Module.End.one_eq_id] using h
  exact abstract_residual_trace_eq_zero A T hcomm hsq hgP
    hrPrincipal hrdvd harith

end

end Erdos85

#print axioms Erdos85.adjMatrix_comm_ratOnesMatrix_of_regular
#print axioms Erdos85.binarySquare_regular_shiftedDefect_residual_trace_eq_zero
