import Proofs.Erdos85BinarySquareEndpointRigidity

/-!
# Unit centered-owner sectors are scaled projections

This transports the integer combinatorial sector to the real matrix order and
applies the sharp endpoint equality case.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open scoped MatrixOrder

/-- Eigenvalues of a scaled projection lie at its two endpoints. -/
theorem eigenvalue_eq_zero_or_scale_of_mul_self_eq_smul
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (r eig : ℝ)
    (hpoly : A * A = r • A)
    (v : V → ℝ) (hv : A.mulVec v = eig • v) (hv0 : v ≠ 0) :
    eig = 0 ∨ eig = r := by
  have hvec := congrArg (fun M : Matrix V V ℝ ↦ M.mulVec v) hpoly
  have hleft : (A * A).mulVec v = (eig * eig) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv]
    simp [smul_smul]
  rw [hleft, Matrix.smul_mulVec, hv] at hvec
  simp only [smul_smul] at hvec
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  have hiEq := congrFun hvec i
  simp only [Pi.smul_apply, smul_eq_mul] at hiEq
  have hz : (eig * (eig - r)) * v i = 0 := by
    calc
      (eig * (eig - r)) * v i = eig * eig * v i - r * eig * v i := by ring
      _ = 0 := sub_eq_zero.mpr hiEq
  rcases mul_eq_zero.mp hz with hfactor | hiv
  · rcases mul_eq_zero.mp hfactor with hzero | hend
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hend)
  · exact (hi hiv).elim

/-- Real division-free centering: removing a constant eigendirection from a
PSD matrix preserves positivity. -/
theorem centered_posSemidef_of_const_eigen_real
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M : Matrix V V ℝ) (r : ℝ)
    (hM : M.PosSemidef)
    (hMone : M.mulVec (fun _ => (1 : ℝ)) = r • (fun _ => (1 : ℝ))) :
    ((Fintype.card V : ℝ) • M -
      r • (show Matrix V V ℝ from fun _ _ ↦ 1)).PosSemidef := by
  let n : ℝ := Fintype.card V
  let one : V → ℝ := fun _ => 1
  let J : Matrix V V ℝ := fun _ _ ↦ 1
  have hJherm : J.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [J]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (hM.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).sub
      (hJherm.smul (isSelfAdjoint_iff.mpr (by simp)))
  intro v
  let s : ℝ := ∑ x, v x
  let w : V → ℝ := n • v - s • one
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
      simp [J, Matrix.mulVec, dotProduct,
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

/-- The real cast of a unit centered-owner sector is a scaled projection. -/
theorem binarySquare_regular_unit_centeredOwnerGram_real_mul_self
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
    let C : Matrix V V ℝ :=
      (q : ℝ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
            (1 : Matrix V V ℝ)) -
        (show Matrix V V ℝ from fun _ _ ↦ 1)
    C * C = ((q : ℝ) ^ 2) • C := by
  dsimp
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D c
  let P : Matrix V V ℝ := defectComponentDiagonalMatrix (K := ℝ) D c
  let M : Matrix V V ℝ := O.adjMatrix ℝ + (1 : Matrix V V ℝ)
  let J : Matrix V V ℝ := fun _ _ ↦ 1
  let C : Matrix V V ℝ := (q : ℝ) • M - J
  have hEqZ := binarySquare_regular_componentOwnerGraph_adjMatrix_eq
    G hfree hq hreg hcard c (m_c := 1) (by simpa using hc)
  have hEqR : M = G.adjMatrix ℝ * P * G.adjMatrix ℝ := by
    have hmap := congrArg
      (fun A ↦ A.map (Int.castRingHom ℝ)) hEqZ
    ext x y
    have hxy := congrFun (congrFun hmap x) y
    have hone :
        (((1 : Matrix V V ℤ) x y : ℤ) : ℝ) =
          (1 : Matrix V V ℝ) x y := by
      by_cases h : x = y <;> simp [Matrix.one_apply, h]
    simp [M, P, D, O, SimpleGraph.adjMatrix_apply,
      defectComponentDiagonalMatrix] at hxy ⊢
    rw [hone] at hxy
    exact eq_sub_iff_add_eq.mp hxy
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro x
    by_cases hx : D.connectedComponentMk x = c <;> simp [hx]
  have hM : M.PosSemidef := by
    rw [hEqR]
    have hGram := hP.conjTranspose_mul_mul_same (G.adjMatrix ℝ)
    have hA : Matrix.conjTranspose (G.adjMatrix ℝ) = G.adjMatrix ℝ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, G.isSymm_adjMatrix]
    rwa [hA] at hGram
  have hOreg : ∀ x, O.degree x = q - 1 := by
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c (m_c := 1) (by simpa using hc)
    simpa [O, D] using h
  have hMone : M.mulVec (fun _ ↦ (1 : ℝ)) =
      (q : ℝ) • (fun _ ↦ (1 : ℝ)) := by
    rw [show M = O.adjMatrix ℝ + (1 : Matrix V V ℝ) by rfl,
      Matrix.add_mulVec, Matrix.one_mulVec]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    change (O.adjMatrix ℝ).mulVec (Function.const V 1) x + 1 = (q : ℝ)
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hOreg x]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  letI : Nonempty V := hV
  have hcenter := centered_posSemidef_of_const_eigen_real
    M (q : ℝ) hM hMone
  have hcenterEq :
      ((Fintype.card V : ℝ) • M -
          (q : ℝ) • J) = (q : ℝ) • C := by
    rw [hcard]
    dsimp [C]
    push_cast
    module
  have hscaled : ((q : ℝ) • C).PosSemidef := by
    rw [← hcenterEq]
    simpa [J] using hcenter
  have hC : C.PosSemidef := by
    have hinv : 0 ≤ ((q : ℝ)⁻¹) := by positivity
    have := hscaled.smul hinv
    simpa [smul_smul, ne_of_gt (show (0 : ℝ) < q by positivity)] using this
  have hJ : J.PosSemidef := by
    change (Matrix.of (fun _ _ ↦ (1 : ℝ))).PosSemidef
    simpa [Matrix.vecMulVec] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : V ↦ (1 : ℝ)))
  have hLap : (O.lapMatrix ℝ).PosSemidef :=
    O.posSemidef_lapMatrix (R := ℝ)
  have hUpperEq :
      ((q : ℝ) ^ 2) • (1 : Matrix V V ℝ) - C =
        (q : ℝ) • O.lapMatrix ℝ + J := by
    have hdeg : O.degMatrix ℝ =
        (((q - 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ)) := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [SimpleGraph.degMatrix, hOreg]
      · simp [SimpleGraph.degMatrix, hxy]
    rw [SimpleGraph.lapMatrix, hdeg]
    dsimp [C, M]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast
    module
  have hUpper :
      (((q : ℝ) ^ 2) • (1 : Matrix V V ℝ) - C).PosSemidef := by
    rw [hUpperEq]
    exact (hLap.smul (by positivity)).add hJ
  let Cz : Matrix V V ℤ :=
    (q : ℤ) •
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
          (1 : Matrix V V ℤ)) -
      FriendshipTheoremOQ01.onesMatrix V
  have hCmap : Cz.map (Int.castRingHom ℝ) = C := by
    ext x y
    change
      (((q : ℤ) *
          ((O.adjMatrix ℤ) x y + (1 : Matrix V V ℤ) x y) - 1 : ℤ) : ℝ) =
        (q : ℝ) *
          ((O.adjMatrix ℝ) x y + (1 : Matrix V V ℝ) x y) - 1
    by_cases hxy : x = y <;>
      by_cases hadj : O.Adj x y <;>
      simp [SimpleGraph.adjMatrix_apply, Matrix.one_apply, hxy, hadj]
  have htraceZ : Matrix.trace (Cz * Cz) =
      ((q : ℤ) ^ 2) * Matrix.trace Cz := by
    simpa [Cz] using
      (binarySquare_regular_trace_centeredOwnerGram_sq_eq
        G hfree hq hreg hcard c (m_c := 1) (by simpa using hc))
  have htraceCast := congrArg (fun z : ℤ ↦ (z : ℝ)) htraceZ
  have htrace : Matrix.trace (C * C) =
      ((q : ℝ) ^ 2) * Matrix.trace C := by
    rw [← hCmap]
    simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply] using htraceCast
  have hproj := posSemidef_mul_self_eq_smul_of_upper_of_trace_sq_eq
    C ((q : ℝ) ^ 2) hC hUpper htrace
  simpa [C, M, J, O, D] using hproj

/-- Every eigenvalue of the real unit centered-owner sector is `0` or `q²`. -/
theorem binarySquare_regular_unit_centeredOwnerGram_real_eigenvalue_eq_zero_or_sq
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
    (hc : c.supp.ncard = q)
    (eig : ℝ) (v : V → ℝ)
    (hv :
      let C : Matrix V V ℝ :=
        (q : ℝ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
              (1 : Matrix V V ℝ)) -
          (show Matrix V V ℝ from fun _ _ ↦ 1)
      C.mulVec v = eig • v)
    (hv0 : v ≠ 0) :
    eig = 0 ∨ eig = (q : ℝ) ^ 2 := by
  let C : Matrix V V ℝ :=
    (q : ℝ) •
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
          (1 : Matrix V V ℝ)) -
      (show Matrix V V ℝ from fun _ _ ↦ 1)
  have hpoly : C * C = ((q : ℝ) ^ 2) • C := by
    simpa [C] using
      binarySquare_regular_unit_centeredOwnerGram_real_mul_self
        G hfree hq hreg hcard c hc
  exact eigenvalue_eq_zero_or_scale_of_mul_self_eq_smul
    C ((q : ℝ) ^ 2) eig hpoly v (by simpa [C] using hv) hv0

end


end Erdos85
