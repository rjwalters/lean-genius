import Proofs.Erdos85BinarySquareCenteredOwnerRank

/-! # Spectrum transfer between defect components and centered owner sectors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The real centered Gram matrix belonging to one owner sector. -/
def realCenteredOwnerGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (q m_c : ℕ) (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix V V ℝ :=
  (((q : ℤ) •
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
          (m_c : ℤ) • (1 : Matrix V V ℤ)) -
      (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V).map
        (Int.castRingHom ℝ))

/-- Real form of the row-Gram factorization `B Bᵀ = q C`. -/
theorem realCenteredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    realCenteredDefectComponentNeighborIncidenceMatrix G q c *
        (realCenteredDefectComponentNeighborIncidenceMatrix G q c).transpose =
      (q : ℝ) • realCenteredOwnerGram G q m_c c := by
  let CZ : Matrix V V ℤ :=
    (q : ℤ) •
        ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
          (m_c : ℤ) • (1 : Matrix V V ℤ)) -
      (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  have hz :=
    centeredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_centeredOwnerGram
      G hfree hq hreg hcard c hc
  have hr := congrArg (fun M : Matrix V V ℤ =>
    M.map (Int.castRingHom ℝ)) hz
  have hleft :
      (centeredDefectComponentNeighborIncidenceMatrix G q c *
        (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose).map
          (Int.castRingHom ℝ) =
        realCenteredDefectComponentNeighborIncidenceMatrix G q c *
          (realCenteredDefectComponentNeighborIncidenceMatrix G q c).transpose := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hright : ((q : ℤ) • CZ).map (Int.castRingHom ℝ) =
      (q : ℝ) • realCenteredOwnerGram G q m_c c := by
    ext x y
    change (((q : ℤ) * CZ x y : ℤ) : ℝ) =
      (q : ℝ) * ((CZ x y : ℤ) : ℝ)
    norm_num
  exact hleft.symm.trans (hr.trans hright)

/-- The centered incidence block intertwines the component Laplacian and its
owner Gram.  Thus their nonzero spectra agree after the scale factor `q`. -/
theorem realCenteredOwnerGram_mul_incidence_eq_incidence_mul_lapMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    realCenteredOwnerGram G q m_c c *
        realCenteredDefectComponentNeighborIncidenceMatrix G q c =
      (q : ℝ) •
        (realCenteredDefectComponentNeighborIncidenceMatrix G q c *
          ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ) := by
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  let C := realCenteredOwnerGram G q m_c c
  let L := ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ
  have hrow : B * B.transpose = (q : ℝ) • C := by
    simpa [B, C] using
      realCenteredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerGram
        G hfree hq hreg hcard c hc
  have hcol : B.transpose * B = ((q * q : ℕ) : ℝ) • L := by
    simpa [B, L] using
      transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
        G hfree hq hreg hcard c
  have hscaled : (q : ℝ) • (C * B) =
      (q : ℝ) • ((q : ℝ) • (B * L)) := by
    calc
      (q : ℝ) • (C * B) = ((q : ℝ) • C) * B := by rw [Matrix.smul_mul]
      _ = (B * B.transpose) * B := by rw [hrow]
      _ = B * (B.transpose * B) := by rw [Matrix.mul_assoc]
      _ = B * (((q * q : ℕ) : ℝ) • L) := by rw [hcol]
      _ = (q : ℝ) • ((q : ℝ) • (B * L)) := by
        rw [Matrix.mul_smul]
        ext x y
        simp only [Matrix.smul_apply, smul_eq_mul]
        push_cast
        ring
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  ext x y
  have hxy := congrArg (fun M => M x y) hscaled
  simp only [Matrix.smul_apply, smul_eq_mul] at hxy
  exact mul_left_cancel₀ hq0 hxy

/-- A nonzero component-Laplacian eigenvector maps through `B` to a nonzero
owner-Gram eigenvector, with eigenvalue multiplied by `q`. -/
theorem realCenteredOwnerGram_eigenvector_of_lapMatrix_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c)
    (v : c.supp → ℝ) (a : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ).mulVec v =
      a • v) (hv0 : v ≠ 0) (ha0 : a ≠ 0) :
    let w := (realCenteredDefectComponentNeighborIncidenceMatrix G q c).mulVec v
    w ≠ 0 ∧ (realCenteredOwnerGram G q m_c c).mulVec w =
      ((q : ℝ) * a) • w := by
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  let C := realCenteredOwnerGram G q m_c c
  let L := ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ
  have hcol : B.transpose * B = ((q * q : ℕ) : ℝ) • L := by
    simpa [B, L] using
      transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
        G hfree hq hreg hcard c
  have hw0 : B.mulVec v ≠ 0 := by
    intro hw
    have hz : (((q * q : ℕ) : ℝ) • L).mulVec v = 0 := by
      rw [← hcol, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    rw [Matrix.smul_mulVec, hv, smul_smul] at hz
    have hscalar : (((q * q : ℕ) : ℝ) * a) ≠ 0 := by positivity
    exact hv0 (smul_eq_zero.mp hz |>.resolve_left hscalar)
  refine ⟨hw0, ?_⟩
  have hinter := realCenteredOwnerGram_mul_incidence_eq_incidence_mul_lapMatrix
    G hfree hq hreg hcard c hc
  change C.mulVec (B.mulVec v) = ((q : ℝ) * a) • B.mulVec v
  calc
    C.mulVec (B.mulVec v) = (C * B).mulVec v :=
      Matrix.mulVec_mulVec v C B
    _ = ((q : ℝ) • (B * L)).mulVec v := by rw [hinter]
    _ = (q : ℝ) • B.mulVec (L.mulVec v) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
    _ = (q : ℝ) • B.mulVec (a • v) := by rw [hv]
    _ = ((q : ℝ) * a) • B.mulVec v := by
      rw [Matrix.mulVec_smul, smul_smul]

/-- Conversely, a nonzero owner-Gram eigenvector maps through `Bᵀ` to a
nonzero eigenvector of `q L`, with the same eigenvalue. -/
theorem smul_lapMatrix_eigenvector_of_realCenteredOwnerGram_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c)
    (w : V → ℝ) (a : ℝ)
    (hw : (realCenteredOwnerGram G q m_c c).mulVec w = a • w)
    (hw0 : w ≠ 0) (ha0 : a ≠ 0) :
    let v := (realCenteredDefectComponentNeighborIncidenceMatrix G q c).transpose.mulVec w
    v ≠ 0 ∧
      (((q : ℝ) •
        ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ).mulVec v =
          a • v) := by
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  let C := realCenteredOwnerGram G q m_c c
  let L := ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ
  have hrow : B * B.transpose = (q : ℝ) • C := by
    simpa [B, C] using
      realCenteredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerGram
        G hfree hq hreg hcard c hc
  have hcol : B.transpose * B = ((q * q : ℕ) : ℝ) • L := by
    simpa [B, L] using
      transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
        G hfree hq hreg hcard c
  have hv0 : B.transpose.mulVec w ≠ 0 := by
    intro hv
    have hz : ((q : ℝ) • C).mulVec w = 0 := by
      rw [← hrow, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.smul_mulVec, hw, smul_smul] at hz
    have hscalar : (q : ℝ) * a ≠ 0 := by positivity
    exact hw0 (smul_eq_zero.mp hz |>.resolve_left hscalar)
  refine ⟨hv0, ?_⟩
  change ((q : ℝ) • L).mulVec (B.transpose.mulVec w) =
    a • B.transpose.mulVec w
  have hraw : (((q * q : ℕ) : ℝ) • L).mulVec
      (B.transpose.mulVec w) =
      ((q : ℝ) * a) • B.transpose.mulVec w := by
    calc
      (((q * q : ℕ) : ℝ) • L).mulVec (B.transpose.mulVec w) =
          (B.transpose * B).mulVec (B.transpose.mulVec w) := by rw [hcol]
      _ = B.transpose.mulVec (B.mulVec (B.transpose.mulVec w)) := by
        rw [← Matrix.mulVec_mulVec]
      _ = B.transpose.mulVec ((B * B.transpose).mulVec w) :=
        congrArg B.transpose.mulVec (Matrix.mulVec_mulVec w B B.transpose)
      _ = B.transpose.mulVec (((q : ℝ) • C).mulVec w) := by rw [hrow]
      _ = ((q : ℝ) * a) • B.transpose.mulVec w := by
        rw [Matrix.smul_mulVec, hw]
        rw [smul_smul, Matrix.mulVec_smul]
  ext x
  have hx := congrFun hraw x
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] at hx ⊢
  push_cast at hx
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hq0
  simpa [mul_assoc] using hx

end

end Erdos85
