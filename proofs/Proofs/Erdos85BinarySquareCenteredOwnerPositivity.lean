import Proofs.Erdos85BinarySquareCenteredOwnerTrace

/-!
# Positivity of centered owner sectors

Centering a positive semidefinite matrix along its constant eigendirection
preserves positivity.  Applied to shifted owner Gram matrices, this proves
that every centered owner sector is PSD—the structural hypothesis needed to
turn the sharp trace-moment ratio into rank/eigenvalue rigidity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A PSD matrix with constant row sum remains PSD after subtracting its
constant eigendirection, in the division-free normalization `n M - r J`. -/
theorem centered_posSemidef_of_const_eigen
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M : Matrix V V ℤ) (r : ℤ)
    (hM : M.PosSemidef)
    (hMone : M.mulVec (fun _ => (1 : ℤ)) = r • (fun _ => (1 : ℤ))) :
    ((Fintype.card V : ℤ) • M -
      r • FriendshipTheoremOQ01.onesMatrix V).PosSemidef := by
  let n : ℤ := Fintype.card V
  let one : V → ℤ := fun _ => 1
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hJherm : J.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [J, FriendshipTheoremOQ01.onesMatrix]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (hM.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).sub
      (hJherm.smul (isSelfAdjoint_iff.mpr (by simp)))
  intro v
  let s : ℤ := ∑ x, v x
  let w : V → ℤ := n • v - s • one
  have hstarv : star v = v := by funext x; simp
  have hstarw : star w = w := by funext x; simp [w, one]
  have hMone' : M.mulVec one = r • one := by simpa [one] using hMone
  have hvMone : v ⬝ᵥ M.mulVec one = r * s := by
    rw [hMone']
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, one, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  have honeMv : one ⬝ᵥ M.mulVec v = r * s := by
    calc
      one ⬝ᵥ M.mulVec v = star one ⬝ᵥ M.mulVec v := by simp [one]
      _ = star (M.mulVec one) ⬝ᵥ v := by
        rw [Matrix.star_mulVec, hM.isHermitian.eq, Matrix.dotProduct_mulVec]
      _ = r * s := by
        rw [hMone']
        simp only [dotProduct]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        simp [one]
  have honeMone : one ⬝ᵥ M.mulVec one = r * n := by
    rw [hMone']
    simp [dotProduct, one, n, mul_comm]
  have hJquad : v ⬝ᵥ J.mulVec v = s * s := by
    have hJv : J.mulVec v = s • one := by
      funext x
      simp [J, FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct,
        s, one]
    rw [hJv]
    simp [dotProduct, one, s, Finset.mul_sum, mul_comm]
  have hwquad : w ⬝ᵥ M.mulVec w =
      n * (n * (v ⬝ᵥ M.mulVec v) - r * (v ⬝ᵥ J.mulVec v)) := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [hvMone, honeMv, honeMone, hJquad]
    ring
  have hw_nonneg : 0 ≤ w ⬝ᵥ M.mulVec w := by
    simpa [hstarw] using hM.dotProduct_mulVec_nonneg w
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hcenter : 0 ≤ n * (v ⬝ᵥ M.mulVec v) - r * (v ⬝ᵥ J.mulVec v) := by
    rw [hwquad] at hw_nonneg
    nlinarith
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, hstarv]
  simpa [n, J] using hcenter

/-- Positivity descends through multiplication by a positive integer scalar. -/
theorem posSemidef_of_pos_int_smul
    {V : Type*} [Fintype V]
    (C : Matrix V V ℤ) (a : ℤ) (ha : 0 < a)
    (hC : C.IsHermitian) (hscaled : (a • C).PosSemidef) :
    C.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hC
  intro v
  have h := hscaled.dotProduct_mulVec_nonneg v
  rw [Matrix.smul_mulVec, dotProduct_smul] at h
  simp only [smul_eq_mul] at h
  nlinarith

/-- Every centered owner Gram sector is positive semidefinite. -/
theorem binarySquare_regular_centeredOwnerGram_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V).PosSemidef := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let M := O.adjMatrix ℤ + (m_c : ℤ) • (1 : Matrix V V ℤ)
  let J := FriendshipTheoremOQ01.onesMatrix V
  let C := (q : ℤ) • M - (m_c : ℤ) • J
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  letI : Nonempty V := hV
  have hM : M.PosSemidef :=
    binarySquare_regular_componentOwnerGraph_adjMatrix_add_posSemidef
      G hfree hq hreg hcard c hc
  have hOreg : ∀ x, O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hOone : (O.adjMatrix ℤ).mulVec (fun _ => (1 : ℤ)) =
      ((m_c * (q - 1) : ℕ) : ℤ) • (fun _ => (1 : ℤ)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    change (O.adjMatrix ℤ).mulVec (Function.const V 1) x =
      ((m_c * (q - 1) : ℕ) : ℤ)
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hOreg x]
  have hMone : M.mulVec (fun _ => (1 : ℤ)) =
      ((q * m_c : ℕ) : ℤ) • (fun _ => (1 : ℤ)) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hOone]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hscaled := centered_posSemidef_of_const_eigen
    M (((q * m_c : ℕ) : ℤ)) hM hMone
  have heq :
      ((Fintype.card V : ℤ) • M -
          ((q * m_c : ℕ) : ℤ) • J) = (q : ℤ) • C := by
    dsimp [C]
    rw [hcard]
    push_cast
    module
  rw [heq] at hscaled
  have hJherm : J.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [J, FriendshipTheoremOQ01.onesMatrix]
  have hCherm : C.IsHermitian :=
    (hM.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).sub
      (hJherm.smul (isSelfAdjoint_iff.mpr (by simp)))
  exact posSemidef_of_pos_int_smul C (q : ℤ) (by exact_mod_cast (by omega : 0 < q))
    hCherm hscaled

end

end Erdos85
