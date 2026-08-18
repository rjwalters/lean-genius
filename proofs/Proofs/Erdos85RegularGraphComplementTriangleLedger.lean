import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-!
# Triangle ledger for a regular graph and its complement

This is the q-generic Goodman identity needed to compare the centered-owner
triangle divisibility with all complement triangles.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cubic trace form of the regular graph/complement triangle ledger. -/
theorem regularGraph_trace_adjMatrix_cube_add_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel Hᶜ.Adj]
    (n d : ℕ) (hcard : Fintype.card V = n)
    (hreg : ∀ x, H.degree x = d) :
    Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) +
      Matrix.trace (Hᶜ.adjMatrix ℤ * Hᶜ.adjMatrix ℤ * Hᶜ.adjMatrix ℤ) =
        (n : ℤ) * (n - 1) * (n - 2) -
          3 * (n : ℤ) * d * (n - 1 - d) := by
  let A := H.adjMatrix ℤ
  let C := Hᶜ.adjMatrix ℤ
  let J : Matrix V V ℤ := Matrix.of fun _ _ => 1
  let ni : ℤ := n
  let di : ℤ := d
  have hC : C = J - 1 - A := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [A, C, J, SimpleGraph.adjMatrix_apply]
    · by_cases hAdj : H.Adj x y
      · simp [A, C, J, SimpleGraph.adjMatrix_apply, hxy, hAdj]
      · simp [A, C, J, SimpleGraph.adjMatrix_apply, hxy, hAdj]
  have hAJ : A * J = di • J := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [A, J, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
    have hx := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := H) (α := ℤ) (a := (1 : ℤ)) (v := x)
    rw [hreg x] at hx
    simpa [Matrix.mulVec, dotProduct, di] using hx
  have hJA : J * A = di • J := by
    have ht := congrArg Matrix.transpose hAJ
    have hAT : A.transpose = A := H.isSymm_adjMatrix.eq
    have hJT : J.transpose = J := by rfl
    simpa only [Matrix.transpose_mul, hAT, hJT, Matrix.transpose_smul] using ht
  have hJJ : J * J = ni • J := by
    ext x y
    simp [J, Matrix.mul_apply, hcard, ni]
  have hAAJ : A * A * J = (di ^ 2) • J := by
    rw [Matrix.mul_assoc, hAJ, Matrix.mul_smul, hAJ, smul_smul]
    ring_nf
  have hcube : C * C * C =
      (ni ^ 2 - 3 * ni * (1 + di) + 3 * (1 + di) ^ 2) • J -
        (1 : Matrix V V ℤ) - (3 : ℤ) • A -
          (3 : ℤ) • (A * A) - A * A * A := by
    rw [hC]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [hAJ, hJA, hJJ]
    simp only [hJA, hJJ, hAAJ, Matrix.smul_mul, smul_smul]
    module
  have htrA : Matrix.trace A = 0 := SimpleGraph.trace_adjMatrix ℤ H
  have htrA2 : Matrix.trace (A * A) = ni * di := by
    have h := FriendshipTheoremOQ01.trace_adjMatrix_sq H d hreg
    rw [hcard] at h
    simpa [A, ni, di] using h
  have htrJ : Matrix.trace J = ni := by
    simp [J, Matrix.trace, Matrix.diag, hcard, ni]
  have htrI : Matrix.trace (1 : Matrix V V ℤ) = ni := by
    simp [Matrix.trace, Matrix.diag, hcard, ni]
  rw [hcube, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, htrJ, htrI, htrA, htrA2]
  dsimp [ni, di]
  ring

/-- Count form: a regular graph and its complement contain the standard
Goodman number of triangles. -/
theorem regularGraph_triangleMinorCount_add_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel Hᶜ.Adj]
    (n d : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card V = n)
    (hreg : ∀ x, H.degree x = d) :
    (6 : ℤ) *
      (((adjacencyTriangleMinorFinset H).card : ℤ) +
        ((adjacencyTriangleMinorFinset Hᶜ).card : ℤ)) =
      (n : ℤ) * (n - 1) * (n - 2) -
        3 * (n : ℤ) * d * (n - 1 - d) := by
  have htrace := regularGraph_trace_adjMatrix_cube_add_compl
    H n d hcard hreg
  have hH := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount H (by omega)
  have hC := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount Hᶜ (by omega)
  rw [hH, hC] at htrace
  linarith

/-- The global defect graph at a regular square-order endpoint is
`(q-1)`-regular, so the generic complement ledger specializes uniformly. -/
theorem binarySquare_regular_defect_triangleMinorCount_add_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (6 : ℤ) *
      (((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
        ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)ᶜ).card : ℤ)) =
      ((q * q : ℕ) : ℤ) * ((q * q : ℕ) - 1) * ((q * q : ℕ) - 2) -
        3 * ((q * q : ℕ) : ℤ) * (q - 1 : ℕ) *
          ((q * q : ℕ) - 1 - (q - 1 : ℕ)) := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  exact regularGraph_triangleMinorCount_add_compl D (q * q) (q - 1)
    (by nlinarith) hcard hDreg

end


end Erdos85

#print axioms Erdos85.regularGraph_trace_adjMatrix_cube_add_compl
#print axioms Erdos85.regularGraph_triangleMinorCount_add_compl
#print axioms Erdos85.binarySquare_regular_defect_triangleMinorCount_add_compl
