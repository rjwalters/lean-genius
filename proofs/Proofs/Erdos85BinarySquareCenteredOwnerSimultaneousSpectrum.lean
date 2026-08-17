import Proofs.Erdos85BinarySquareCenteredOwnerSpectrumTransfer
import Proofs.Erdos85BinarySquareCenteredOwnerCross
import Proofs.Erdos85PrincipalIndicatorTrace

/-!
# Simultaneous spectrum of distinct owner colors

Pairwise annihilation of centered owner sectors upgrades the one-color
Laplacian transfer to a simultaneous statement: a nonzero vector carried by
color `c` lies at the bottom eigenvalue of every other owner color.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Expanded real form of a centered owner Gram. -/
theorem realCenteredOwnerGram_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (q m_c : ℕ) (c : (secondOrderDefectGraph G).ConnectedComponent) :
    realCenteredOwnerGram G q m_c c =
      (q : ℝ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
            (m_c : ℝ) • (1 : Matrix V V ℝ)) -
        (m_c : ℝ) • (Matrix.of (fun _ : V => fun _ : V => (1 : ℝ))) := by
  ext x y
  change (((q : ℤ) *
      (((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℤ) x y +
          (m_c : ℤ) * (1 : Matrix V V ℤ) x y) - (m_c : ℤ) * 1 : ℤ) : ℝ) = _
  push_cast
  have hO := congrFun (congrFun
    (adjMatrix_map_intCast (K := ℝ)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)) x) y
  simp only [Matrix.map_apply] at hO
  have hO' :
      (((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℤ x y : ℤ) : ℝ) =
        (componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℝ x y := by
    exact hO
  rw [hO']
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Distinct real centered owner Grams annihilate one another. -/
theorem binarySquare_regular_realCenteredOwnerGrams_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    {m_c m_d : ℕ} (hc : c.supp.ncard = q * m_c)
    (hd : d.supp.ncard = q * m_d) :
    realCenteredOwnerGram G q m_d d *
        realCenteredOwnerGram G q m_c c = 0 := by
  have hz := binarySquare_regular_centeredOwnerGrams_mul_eq_zero
    G hfree hq hreg hcard d c hcd.symm hd hc
  have hr := congrArg (fun M : Matrix V V ℤ =>
    M.map (Int.castRingHom ℝ)) hz
  have hzero : (0 : Matrix V V ℤ).map (Int.castRingHom ℝ) = 0 := by
    ext x y
    simp
  rw [hzero] at hr
  simpa only [Matrix.map_mul, realCenteredOwnerGram] using hr

/-- On a zero-sum centered-sector eigenvector, the corresponding owner graph
has eigenvalue `a/q-m_c`. -/
theorem componentOwnerGraph_eigenvector_of_realCenteredOwnerGram_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {q : ℕ} (hq0 : q ≠ 0)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (w : V → ℝ) (a : ℝ)
    (hw : (realCenteredOwnerGram G q m_c c).mulVec w = a • w)
    (hsum : ∑ x, w x = 0) :
    ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec w =
        (a / (q : ℝ) - m_c) • w := by
  have hJ : (Matrix.of (fun _ : V => fun _ : V => (1 : ℝ))).mulVec w = 0 := by
    funext x
    simp [Matrix.mulVec, dotProduct, hsum]
  rw [realCenteredOwnerGram_eq, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
  rw [Matrix.smul_mulVec, hJ, smul_zero, sub_zero] at hw
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  ext x
  have hx := congrFun hw x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  field_simp [hqR]
  nlinarith

/-- A nonzero eigenvector carried by one centered owner sector is a bottom
eigenvector of every distinct owner color. -/
theorem componentOwnerGraph_bottom_eigenvector_of_distinct_realCenteredOwnerGram_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    {m_c m_d : ℕ} (hc : c.supp.ncard = q * m_c)
    (hd : d.supp.ncard = q * m_d)
    (w : V → ℝ) (a : ℝ)
    (hw : (realCenteredOwnerGram G q m_c c).mulVec w = a • w)
    (ha0 : a ≠ 0) (hsum : ∑ x, w x = 0) :
    ((componentOwnerGraph G
      (secondOrderDefectGraph G) d).adjMatrix ℝ).mulVec w =
        (-(m_d : ℝ)) • w := by
  have hprod := binarySquare_regular_realCenteredOwnerGrams_mul_eq_zero
    G hfree hq hreg hcard c d hcd hc hd
  have hCdw : (realCenteredOwnerGram G q m_d d).mulVec w = 0 := by
    have hz := congrArg (fun M => M.mulVec w) hprod
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul,
      Matrix.zero_mulVec] at hz
    exact (smul_eq_zero.mp hz).resolve_left ha0
  have hJ : (Matrix.of (fun _ : V => fun _ : V => (1 : ℝ))).mulVec w = 0 := by
    funext x
    simp [Matrix.mulVec, dotProduct, hsum]
  rw [realCenteredOwnerGram_eq, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hCdw
  rw [Matrix.smul_mulVec, hJ, smul_zero, sub_zero] at hCdw
  have hqR : (q : ℝ) ≠ 0 := by positivity
  apply_fun fun z => (q : ℝ)⁻¹ • z at hCdw
  simp only [smul_smul, inv_mul_cancel₀ hqR, one_smul, smul_zero] at hCdw
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hCdw

end

end Erdos85
