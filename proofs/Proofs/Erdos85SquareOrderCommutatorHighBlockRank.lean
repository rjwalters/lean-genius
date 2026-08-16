import Proofs.Erdos85SquareOrderCommutatorHighGramDeterminant
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Full row rank of the high commutator block

The high Gram matrix is `B Bᵀ`, where `B` is the high-row restriction of
the adjacency/defect commutator. Its certified nonzero determinant therefore
forces `B` to have full row rank.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_rank_high_commutator_block
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hHtwo : 2 ≤ (squareOrderHighVertices G d).card) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    let B : Matrix (↥H) V ℚ := fun a y => (C a.1 y : ℚ)
    Matrix.rank B = H.card := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let B : Matrix (↥H) V ℚ := fun a y => (C a.1 y : ℚ)
  let M : Matrix (↥H) (↥H) ℚ := fun a b =>
    ((∑ y : V, C a.1 y * C b.1 y : ℤ) : ℚ)
  dsimp only
  have hHtwo' : 2 ≤ H.card := by simpa [H] using hHtwo
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  letI : Nonempty ↥H := ⟨⟨u, hu⟩⟩
  have hgram : B * B.transpose = M := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    dsimp [B, M]
    push_cast
    rfl
  have hdet : Matrix.det M ≠ 0 := by
    simpa [H, C, M] using
      squareOrder_det_high_commutator_gram_ne_zero
        G hfree hd hmin hcover hcard hHtwo
  have hunit : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hdet
  have hrankM : Matrix.rank M = H.card := by
    have h := Matrix.rank_mul_eq_left_of_isUnit_det
      M (1 : Matrix (↥H) (↥H) ℚ) hunit
    simpa using h
  calc
    Matrix.rank B = Matrix.rank (B * B.transpose) :=
      (Matrix.rank_self_mul_transpose B).symm
    _ = Matrix.rank M := by rw [hgram]
    _ = H.card := hrankM

/-- The full commutator has rank at least the number of high vertices. -/
theorem squareOrder_card_high_le_rank_commutator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hHtwo : 2 ≤ (squareOrderHighVertices G d).card) :
    let H := squareOrderHighVertices G d
    let C : Matrix V V ℚ := fun x y =>
      ((G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
        (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y : ℚ)
    H.card ≤ Matrix.rank C := by
  classical
  let H := squareOrderHighVertices G d
  let CZ := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let C : Matrix V V ℚ := fun x y => (CZ x y : ℚ)
  let B : Matrix (↥H) V ℚ := fun a y => (CZ a.1 y : ℚ)
  dsimp only
  have hrankB : Matrix.rank B = H.card := by
    simpa [H, CZ, B] using squareOrder_rank_high_commutator_block
      G hfree hd hmin hcover hcard hHtwo
  have hsub := Matrix.rank_submatrix_le C
    (fun a : ↥H => a.1) (id : V → V)
  have hBC : B = C.submatrix (fun a : ↥H => a.1) (id : V → V) := by
    rfl
  rw [← hBC, hrankB] at hsub
  exact hsub

end

end Erdos85
