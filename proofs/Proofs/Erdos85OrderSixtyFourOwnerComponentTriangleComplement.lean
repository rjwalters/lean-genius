import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger
import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity

/-!
# Owner/component triangle complement at order 64

For a size-16 defect component, rectangular incidence cyclicity makes the
owner and component cubic traces complementary.  Consequently their triangle
counts always sum to `1008`; the four-component `4032` ledger is therefore an
automatic sum of four local identities, not a third-moment obstruction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A size-16 component and its owner have complementary cubic traces. -/
theorem orderSixtyFour_sizeSixteen_owner_component_cube_trace_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    let O := componentOwnerGraph G (secondOrderDefectGraph G) c
    let H := (secondOrderDefectGraph G).induce c.supp
    Matrix.trace (O.adjMatrix ℤ * O.adjMatrix ℤ * O.adjMatrix ℤ) +
      Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) =
        6048 := by
  let I := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let H := (secondOrderDefectGraph G).induce c.supp
  let A := O.adjMatrix ℤ
  let B := H.adjMatrix ℤ
  let J : Matrix c.supp c.supp ℤ := Matrix.of fun _ _ => 1
  let M := I * I.transpose
  let Q := I.transpose * I
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hc
  have hrowR :=
    realDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerShift
      G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
        (m_c := 2) (by simpa using hc)
  have hrow : M = A + (2 : ℤ) • (1 : Matrix V V ℤ) := by
    apply (Matrix.map_injective (Int.cast_injective : Function.Injective
      (Int.castRingHom ℝ))).eq_iff.mp
    calc
      M.map (Int.castRingHom ℝ) =
          realDefectComponentNeighborIncidenceMatrix G c *
            (realDefectComponentNeighborIncidenceMatrix G c).transpose := by
        rw [Matrix.map_mul, Matrix.transpose_map]
        rfl
      _ = (O.adjMatrix ℝ) + (2 : ℝ) • (1 : Matrix V V ℝ) := hrowR
      _ = (A + (2 : ℤ) • (1 : Matrix V V ℤ)).map
          (Int.castRingHom ℝ) := by
        ext x y
        change O.adjMatrix ℝ x y + 2 * (if x = y then 1 else 0) =
          ((A x y + 2 * (if x = y then 1 else 0) : ℤ) : ℝ)
        by_cases hxy : x = y <;>
          simp [A, SimpleGraph.adjMatrix_apply, hxy]
  have hcol0 := transpose_defectComponentNeighborIncidenceMatrix_mul_self
    G hfree (q := 8) (by omega) hreg c
  have hcol : Q = (7 : ℤ) • (1 : Matrix c.supp c.supp ℤ) + J - B := by
    simpa [Q, J, B, H] using hcol0
  have hcycle : Matrix.trace (M * M * M) = Matrix.trace (Q * Q * Q) := by
    calc
      Matrix.trace (M * M * M) =
          Matrix.trace ((I * (Q * Q)) * I.transpose) := by
        congr 1
        simp [M, Q, Matrix.mul_assoc]
      _ = Matrix.trace (I.transpose * (I * (Q * Q))) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Q * Q * Q) := by
        congr 1
        simp [Q, Matrix.mul_assoc]
  have hOreg : ∀ x, O.degree x = 14 := by
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
        (m_c := 2) (by simpa using hc)
    simpa using h
  have htrA : Matrix.trace A = 0 := SimpleGraph.trace_adjMatrix ℤ O
  have htrA2 : Matrix.trace (A * A) = 896 := by
    have h := FriendshipTheoremOQ01.trace_adjMatrix_sq O 14 hOreg
    rw [hcard] at h
    norm_num at h
    simpa [A] using h
  have hM3 :
      (A + (2 : ℤ) • (1 : Matrix V V ℤ)) *
          (A + (2 : ℤ) • (1 : Matrix V V ℤ)) *
          (A + (2 : ℤ) • (1 : Matrix V V ℤ)) =
        A * A * A + (6 : ℤ) • (A * A) + (12 : ℤ) • A +
          (8 : ℤ) • (1 : Matrix V V ℤ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  have hleft : Matrix.trace (M * M * M) =
      Matrix.trace (A * A * A) + 5888 := by
    rw [hrow, hM3, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, htrA2, htrA, hcard]
    norm_num
    ring
  have hHreg : ∀ x, H.degree x = 7 := by
    intro x
    simpa [H] using binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by omega) hreg (by simpa using hcard) c x
  have htrB : Matrix.trace B = 0 := SimpleGraph.trace_adjMatrix ℤ H
  have htrB2 : Matrix.trace (B * B) = 112 := by
    have h := FriendshipTheoremOQ01.trace_adjMatrix_sq H 7 hHreg
    rw [hcs] at h
    norm_num at h
    simpa [B] using h
  have hBJ : B * J = (7 : ℤ) • J := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [B, J, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
    have hx := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := H) (α := ℤ) (a := (1 : ℤ)) (v := x)
    rw [hHreg x] at hx
    simpa [Matrix.mulVec, dotProduct] using hx
  have hJB : J * B = (7 : ℤ) • J := by
    have ht := congrArg Matrix.transpose hBJ
    have hBT : B.transpose = B := by
      exact H.isSymm_adjMatrix.eq
    have hJT : J.transpose = J := by rfl
    simpa only [Matrix.transpose_mul, hBT, hJT, Matrix.transpose_smul] using ht
  have hJJ : J * J = (16 : ℤ) • J := by
    ext x y
    simp [J, Matrix.mul_apply, hcs]
  let L := (7 : ℤ) • (1 : Matrix c.supp c.supp ℤ) - B
  have hLJ : L * J = 0 := by
    dsimp [L]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hBJ]
    rfl
  have hJL : J * L = 0 := by
    dsimp [L]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hJB]
    rfl
  have hQeq : Q = L + J := by
    rw [hcol]
    dsimp [L]
    module
  have hQ3 : (L + J) * (L + J) * (L + J) =
      L * L * L + J * J * J := by
    simp only [Matrix.add_mul, Matrix.mul_add]
    simp [Matrix.mul_assoc, hLJ, hJL]
  have hL3 : L * L * L =
      (343 : ℤ) • (1 : Matrix c.supp c.supp ℤ) -
        (147 : ℤ) • B + (21 : ℤ) • (B * B) - B * B * B := by
    dsimp [L]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul]
    module
  have hJ3 : J * J * J = (256 : ℤ) • J := by
    rw [hJJ, Matrix.smul_mul, hJJ, smul_smul]
    norm_num
  have htrJ : Matrix.trace J = 16 := by
    simp [J, Matrix.trace, Matrix.diag, hcs]
  have hright : Matrix.trace (Q * Q * Q) =
      11936 - Matrix.trace (B * B * B) := by
    rw [hQeq, hQ3, Matrix.trace_add, hL3, hJ3,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_one, htrB, htrB2, htrJ, hcs]
    norm_num
    ring
  dsimp only [O, H]
  dsimp only [A, B] at hleft hright
  linarith

/-- **Local triangle complement.**  The owner and its size-16 defect
component always contain a total of `1008` triangles. -/
theorem orderSixtyFour_sizeSixteen_owner_component_triangleMinorCount_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    (adjacencyTriangleMinorFinset
      (componentOwnerGraph G (secondOrderDefectGraph G) c)).card +
      (adjacencyTriangleMinorFinset
        ((secondOrderDefectGraph G).induce c.supp)).card = 1008 := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let H := (secondOrderDefectGraph G).induce c.supp
  have htrace := orderSixtyFour_sizeSixteen_owner_component_cube_trace_sum
    G hfree hreg hcard c hc
  have hO := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount O
    (by omega : 3 ≤ Fintype.card V)
  have hH := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount H
    (by rw [show Fintype.card c.supp = 16 by
      rw [Set.fintypeCard_eq_ncard]; exact hc]; omega)
  dsimp only [O, H] at htrace hO hH ⊢
  rw [hO, hH] at htrace
  norm_cast at htrace
  omega

end

end Erdos85
