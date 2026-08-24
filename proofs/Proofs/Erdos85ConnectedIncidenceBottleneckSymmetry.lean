import Proofs.Erdos85ConnectedIncidenceBottleneckRowNonzero

/-!
# Symmetry and row nonvanishing of the incidence bottleneck

The matrices `A`, `D`, and `J` are symmetric and `A` commutes with `D`, so
`E = AD-(J-A)` is symmetric.  Consequently the connected column
nonvanishing theorem is also the row nonvanishing interface required by
rowwise energy and cut identities.
-/

namespace Erdos85

noncomputable section

/-- Commuting symmetric factors make the incidence bottleneck symmetric. -/
theorem incidenceBottleneck_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J : Matrix V V ℚ)
    (hA : A.IsSymm) (hD : D.IsSymm) (hJ : J.IsSymm)
    (hcomm : A * D = D * A) :
    (A * D - (J - A)).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_sub,
    Matrix.transpose_mul, hA.eq, hD.eq, hJ.eq, hcomm]

/-- For a symmetric matrix, a nonzero basis column supplies a nonzero entry
in the corresponding row. -/
theorem exists_row_entry_ne_zero_of_isSymm_mulVec_single_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Matrix V V ℚ) (hE : E.IsSymm) (x : V)
    (hcol : E.mulVec (Pi.single x 1) ≠ 0) :
    ∃ y, E x y ≠ 0 := by
  by_contra! hrow
  apply hcol
  ext y
  rw [Matrix.mulVec_single_one]
  exact (hE.apply y x).symm.trans (hrow y)

/-- **Connected row-nonvanishing capstone.**  Every row of the square-order
connected incidence bottleneck has a nonzero entry. -/
theorem binarySquare_connected_incidenceBottleneck_exists_row_entry_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected) (x : V) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let J := ratOnesMatrix V
    let E := A * D - (J - A)
    ∃ y, E x y ≠ 0 := by
  dsimp only
  let A := G.adjMatrix ℚ
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let J := ratOnesMatrix V
  let E := A * D - (J - A)
  have hcomm : A * D = D * A := by
    exact adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hJsymm : J.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    rfl
  have hEsymm : E.IsSymm := by
    exact incidenceBottleneck_isSymm A D J
      G.isSymm_adjMatrix (secondOrderDefectGraph G).isSymm_adjMatrix
      hJsymm hcomm
  apply exists_row_entry_ne_zero_of_isSymm_mulVec_single_ne_zero E hEsymm x
  exact binarySquare_connected_incidenceBottleneck_mulVec_single_ne_zero
    G hfree hq hreg hcard hconn x

end

end Erdos85

#print axioms Erdos85.incidenceBottleneck_isSymm
#print axioms Erdos85.exists_row_entry_ne_zero_of_isSymm_mulVec_single_ne_zero
#print axioms Erdos85.binarySquare_connected_incidenceBottleneck_exists_row_entry_ne_zero
