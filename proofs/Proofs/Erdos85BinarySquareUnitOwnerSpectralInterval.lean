import Proofs.Erdos85BinarySquareCenteredOwnerPositivity
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Spectral interval for unit owner colors

For a normalized-size-one owner color, the complement of its centered Gram
sector inside `q² I` is a positive combination of the owner-graph Laplacian
and the all-ones matrix.  Thus the sector is trapped between `0` and `q² I`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph Laplacian is positive semidefinite over the integers. -/
theorem posSemidef_lapMatrix_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (H.lapMatrix ℤ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact H.isHermitian_lapMatrix (R := ℤ)
  · intro x
    rw [star_trivial]
    have heq :
        2 * (x ⬝ᵥ (H.lapMatrix ℤ).mulVec x) =
          ∑ i : V, ∑ j : V, if H.Adj i j then (x i - x j) ^ 2 else 0 := by
      simp_rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub,
        SimpleGraph.dotProduct_mulVec_degMatrix,
        SimpleGraph.dotProduct_mulVec_adjMatrix, ← Finset.sum_sub_distrib,
        SimpleGraph.degree_eq_sum_if_adj, Finset.sum_mul, ite_mul, one_mul,
        zero_mul, ← Finset.sum_sub_distrib]
      have hswap :
          (∑ i : V, ∑ j : V,
              ((if H.Adj i j then x i * x i else 0) -
                (if H.Adj i j then x i * x j else 0))) =
            ∑ i : V, ∑ j : V,
              ((if H.Adj i j then x j * x j else 0) -
                (if H.Adj i j then x i * x j else 0)) := by
        conv_lhs =>
          enter [2, i, 2, j]
          rw [if_congr (H.adj_comm i j) rfl rfl]
          rw [if_congr (H.adj_comm i j) rfl rfl]
        rw [Finset.sum_comm]
        congr 2 with i
        congr 2 with j
        ring
      rw [two_mul]
      nth_rewrite 2 [hswap]
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : H.Adj i j <;> simp [hij]
      ring
    have hrhs : 0 ≤
        ∑ i : V, ∑ j : V, if H.Adj i j then (x i - x j) ^ 2 else 0 := by
      positivity
    nlinarith

private theorem onesMatrix_posSemidef_int
    {V : Type*} [Fintype V] [DecidableEq V] :
    (FriendshipTheoremOQ01.onesMatrix V : Matrix V V ℤ).PosSemidef := by
  simpa [Matrix.vecMulVec, FriendshipTheoremOQ01.onesMatrix] using
    (Matrix.posSemidef_vecMulVec_self_star (fun _ : V => (1 : ℤ)))

/-- For a unit owner color, `q² I - C_c` is PSD.  Together with centered
owner positivity, this traps the real spectrum of `C_c` in `[0,q²]`. -/
theorem binarySquare_regular_unit_centeredOwnerGram_upper_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) :
    ((q : ℤ) ^ 2 • (1 : Matrix V V ℤ) -
      ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (1 : ℤ) • (1 : Matrix V V ℤ)) -
        (1 : ℤ) • FriendshipTheoremOQ01.onesMatrix V)).PosSemidef := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hOreg : ∀ x, O.degree x = q - 1 := by
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c (m_c := 1) (by simpa using hc)
    simpa using h
  have hLap : (O.lapMatrix ℤ).PosSemidef := posSemidef_lapMatrix_int O
  have hJ : J.PosSemidef := by simpa [J] using (onesMatrix_posSemidef_int (V := V))
  have heq :
      (q : ℤ) ^ 2 • (1 : Matrix V V ℤ) -
          ((q : ℤ) • (O.adjMatrix ℤ + (1 : ℤ) • (1 : Matrix V V ℤ)) -
            (1 : ℤ) • J) =
        (q : ℤ) • O.lapMatrix ℤ + J := by
    have hdeg : O.degMatrix ℤ = ((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [SimpleGraph.degMatrix, hOreg]
      · simp [SimpleGraph.degMatrix, hxy]
    rw [SimpleGraph.lapMatrix, hdeg]
    simp only [one_smul]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    module
  rw [heq]
  exact hLap.smul (by positivity) |>.add hJ

end

end Erdos85
