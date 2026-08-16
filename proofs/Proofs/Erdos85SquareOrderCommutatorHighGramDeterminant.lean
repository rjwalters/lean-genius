import Proofs.Erdos85SquareOrderCommutatorHighFullQuadratic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant of the high commutator Gram matrix

The constant-diagonal/off-diagonal Gram matrix is a scalar matrix plus a
rank-one all-ones perturbation.  The matrix determinant lemma therefore
gives its determinant in closed form.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem det_const_offDiagonal_rat
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d s : ℚ) (hd : d ≠ 0) :
    Matrix.det (fun i j : ι => if i = j then d + s else s) =
      d ^ (Fintype.card ι - 1) * (d + s * Fintype.card ι) := by
  let u : ι → ℚ := fun _ => s / d
  let v : ι → ℚ := fun _ => 1
  let R : Matrix ι ι ℚ :=
    Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v
  have hmatrix : ((fun i j : ι => if i = j then d + s else s) :
      Matrix ι ι ℚ) =
      d • (1 + R) := by
    ext i j
    simp [R, u, v, Matrix.mul_apply, hd]
    by_cases hij : i = j <;> simp [hij, hd]
  rw [hmatrix, Matrix.det_smul]
  have hdetR : Matrix.det (1 + R) = 1 + v ⬝ᵥ u := by
    simpa [R] using
      Matrix.det_one_add_replicateCol_mul_replicateRow
        (ι := Fin 1) u v
  rw [hdetR]
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  rw [hk]
  simp [u, v, dotProduct, Finset.sum_const, hd]
  field_simp
  ring

theorem squareOrder_det_high_commutator_gram
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
    let M : Matrix (↥H) (↥H) ℚ := fun a b =>
      ((∑ y : V, C a.1 y * C b.1 y : ℤ) : ℚ)
    let s := d * d - H.card - (2 * d + 1)
    Matrix.det M =
      (d : ℚ) ^ (H.card - 1) * ((d : ℚ) + (s : ℚ) * H.card) := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let M : Matrix (↥H) (↥H) ℚ := fun a b =>
    ((∑ y : V, C a.1 y * C b.1 y : ℤ) : ℚ)
  let s := d * d - H.card - (2 * d + 1)
  dsimp only
  have hHtwo' : 2 ≤ H.card := by simpa [H] using hHtwo
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Finset.one_lt_card.mp (show 1 < H.card by omega)
  have hcapacity : 2 * d + 1 + H.card ≤ d * d := by
    simpa [H] using
      squareOrder_two_mul_add_one_add_card_high_le_of_two_high
        G hfree hd hmin hcover hcard hu hv huv
  have hHle : H.card ≤ d * d := by omega
  have hcapOne : d + 1 ≤ d * d - H.card := by omega
  have hcapTwo : 2 * d + 1 ≤ d * d - H.card := by omega
  have hM : M = fun a b : ↥H =>
      if a = b then (d : ℚ) + s else s := by
    ext a b
    have h := squareOrder_sum_commutator_row_mul_of_high
      G hfree hd hmin hcover hcard a.2 b.2
    by_cases hab : a = b
    · rw [if_pos hab]
      have habv : a.1 = b.1 := congrArg Subtype.val hab
      rw [show M a b =
          ((d * d - H.card - (d + 1) : Nat) : ℚ) by
        simpa [M, C, H, habv] using congrArg (fun q : ℤ => (q : ℚ)) h]
      rw [Nat.cast_sub hcapOne, Nat.cast_sub hHle,
        show s = d * d - H.card - (2 * d + 1) by rfl,
        Nat.cast_sub hcapTwo, Nat.cast_sub hHle]
      push_cast
      ring
    · rw [if_neg hab]
      have habv : a.1 ≠ b.1 := fun he => hab (Subtype.ext he)
      simpa [M, C, H, s, habv] using congrArg (fun q : ℤ => (q : ℚ)) h
  change Matrix.det M =
    (d : ℚ) ^ (H.card - 1) * ((d : ℚ) + (s : ℚ) * H.card)
  rw [hM, det_const_offDiagonal_rat]
  · simp
  · exact_mod_cast (by omega : d ≠ 0)

end

end Erdos85
