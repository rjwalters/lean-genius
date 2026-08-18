import Proofs.Erdos85BinarySquareUnitOwnerSpectralInterval

/-! # Spectral interval for arbitrary owner colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For a normalized owner color of size `m_c`, the centered Gram matrix is
bounded above by `m_c q² I`.  The complement is exactly a positive
combination of the owner-graph Laplacian and the all-ones matrix:

`m_c q² I - C_c = q Lap(Owner(c)) + m_c J`.

Unlike the earlier unit-color specialization, this applies to every surviving
binary component partition, where all normalized parts are at least two. -/
theorem binarySquare_regular_centeredOwnerGram_upper_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (m_c : ℕ)
    (hc : c.supp.ncard = q * m_c) :
    (((m_c : ℤ) * (q : ℤ) ^ 2) • (1 : Matrix V V ℤ) -
      ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V)).PosSemidef := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hOreg : ∀ x, O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hLap : (O.lapMatrix ℤ).PosSemidef := posSemidef_lapMatrix_int O
  have hJ : J.PosSemidef := by
    simpa [J, Matrix.vecMulVec, FriendshipTheoremOQ01.onesMatrix] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : V => (1 : ℤ)))
  have heq :
      ((m_c : ℤ) * (q : ℤ) ^ 2) • (1 : Matrix V V ℤ) -
          ((q : ℤ) • (O.adjMatrix ℤ +
              (m_c : ℤ) • (1 : Matrix V V ℤ)) -
            (m_c : ℤ) • J) =
        (q : ℤ) • O.lapMatrix ℤ + (m_c : ℤ) • J := by
    have hdeg : O.degMatrix ℤ =
        ((m_c * (q - 1) : ℕ) : ℤ) • (1 : Matrix V V ℤ) := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [SimpleGraph.degMatrix, hOreg]
      · simp [SimpleGraph.degMatrix, hxy]
    rw [SimpleGraph.lapMatrix, hdeg]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q)]
    module
  rw [heq]
  exact (hLap.smul (by positivity)).add (hJ.smul (by positivity))

end

end Erdos85
