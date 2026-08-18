import Proofs.Erdos85BinarySquareCenteredAdjacencyRank
import Proofs.Erdos85BinarySquareRegularParity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Exact adjacency nullity at regular square order

The centered operator `C=qA-J` has range equal to the adjacency range with
the principal constant line removed.  Combining this codimension-one split
with the exact centered rank gives adjacency nullity exactly one less than the
number of defect components.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every output of the square-order centered adjacency operator has coordinate
sum zero. -/
theorem binarySquareCenteredAdjacencyMatrix_coordinateSum_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (v : V → ℝ) :
    ∑ x, (binarySquareCenteredAdjacencyMatrix G q).mulVec v x = 0 := by
  let C := binarySquareCenteredAdjacencyMatrix G q
  let one : V → ℝ := Function.const V 1
  have hCone : C.mulVec one = 0 := by
    dsimp [C, one]
    rw [binarySquareCenteredAdjacencyMatrix, Matrix.sub_mulVec,
      Matrix.smul_mulVec]
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change (q : ℝ) *
        (G.adjMatrix ℝ).mulVec (Function.const V 1) x -
          (realOnesMatrix V).mulVec (Function.const V 1) x = 0
    have hrow : (G.adjMatrix ℝ).mulVec (Function.const V 1) x = (q : ℝ) := by
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x]
    rw [hrow]
    simp [realOnesMatrix, Matrix.mulVec, dotProduct, hcard]
  have hCT : C.transpose = C := by
    dsimp [C]
    rw [binarySquareCenteredAdjacencyMatrix, Matrix.transpose_sub,
      Matrix.transpose_smul, G.isSymm_adjMatrix.eq]
    congr 1
  calc
    (∑ x, C.mulVec v x) = one ⬝ᵥ C.mulVec v := by simp [dotProduct, one]
    _ = Matrix.vecMul one C ⬝ᵥ v := by rw [Matrix.dotProduct_mulVec]
    _ = C.transpose.mulVec one ⬝ᵥ v := by rw [Matrix.mulVec_transpose]
    _ = 0 := by rw [hCT, hCone, zero_dotProduct]

/-- The adjacency range splits as the centered-adjacency range plus the
constant line. -/
theorem binarySquare_adjMatrix_range_eq_centered_sup_const
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 1 ≤ q) (hreg : ∀ x, G.degree x = q) :
    LinearMap.range (G.adjMatrix ℝ).mulVecLin =
      LinearMap.range (binarySquareCenteredAdjacencyMatrix G q).mulVecLin ⊔
        Submodule.span ℝ ({Function.const V 1} : Set (V → ℝ)) := by
  let A : (V → ℝ) →ₗ[ℝ] (V → ℝ) := (G.adjMatrix ℝ).mulVecLin
  let C : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    (binarySquareCenteredAdjacencyMatrix G q).mulVecLin
  let one : V → ℝ := Function.const V 1
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hAone : A one = (q : ℝ) • one := by
    funext x
    change (G.adjMatrix ℝ).mulVec (Function.const V 1) x = _
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x]
    simp [one]
  have hC (v : V → ℝ) :
      C v = (q : ℝ) • A v - (∑ x, v x) • one := by
    funext x
    simp [C, A, one, binarySquareCenteredAdjacencyMatrix,
      realOnesMatrix, Matrix.mulVec, dotProduct]
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    have hdecomp :
        A v = (q : ℝ)⁻¹ • C v +
          (((∑ x, v x) / (q : ℝ)) • one) := by
      rw [hC]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [hdecomp]
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      exact Submodule.smul_mem _ _ ⟨v, rfl⟩
    · apply Submodule.mem_sup_right
      rw [Submodule.mem_span_singleton]
      exact ⟨(∑ x, v x) / (q : ℝ), rfl⟩
  · apply sup_le
    · rintro y ⟨v, rfl⟩
      let s : ℝ := ∑ x, v x
      refine ⟨(q : ℝ) • v - (s / (q : ℝ)) • one, ?_⟩
      calc
        A ((q : ℝ) • v - (s / (q : ℝ)) • one) =
            (q : ℝ) • A v - (s / (q : ℝ)) • A one := by
              rw [map_sub, map_smul, map_smul]
        _ = C v := by
          rw [hAone, hC]
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          dsimp [s]
          field_simp
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst v
      refine ⟨(q : ℝ)⁻¹ • one, ?_⟩
      rw [map_smul, hAone]
      funext x
      simp [one, hqR]

/-- The constant vector is not in the centered-adjacency range. -/
theorem const_not_mem_binarySquareCenteredAdjacencyMatrix_range
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Function.const V (1 : ℝ) ∉
      LinearMap.range (binarySquareCenteredAdjacencyMatrix G q).mulVecLin := by
  intro hone
  obtain ⟨v, hv⟩ := hone
  have hCsum :
      ∑ x, (binarySquareCenteredAdjacencyMatrix G q).mulVec v x = 0 := by
    exact binarySquareCenteredAdjacencyMatrix_coordinateSum_eq_zero
      G hreg hcard v
  have hv' := congrArg (fun w : V → ℝ => ∑ x, w x) hv
  change (∑ x, (binarySquareCenteredAdjacencyMatrix G q).mulVecLin v x) = 0 at hCsum
  rw [hCsum] at hv'
  have hcardPos : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  have hvcard : (0 : ℝ) = Fintype.card V := by simpa using hv'
  exact (ne_of_gt hcardPos) hvcard.symm

/-- The adjacency matrix has one more rank than its centered part: the
principal constant eigendirection. -/
theorem binarySquare_regular_adjMatrix_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    (G.adjMatrix ℝ).rank =
      (q * q - Fintype.card (secondOrderDefectGraph G).ConnectedComponent) + 1 := by
  have hcardPos : 0 < Fintype.card V := by rw [hcard]; positivity
  letI : Nonempty V := Fintype.card_pos_iff.mp hcardPos
  have hrange := binarySquare_adjMatrix_range_eq_centered_sup_const
    G (by omega) hreg
  have hnot := const_not_mem_binarySquareCenteredAdjacencyMatrix_range
    G hreg hcard
  have hcenter := binarySquareCenteredAdjacencyMatrix_rank
    G hfree hq hreg hcard
  change Module.finrank ℝ (LinearMap.range (G.adjMatrix ℝ).mulVecLin) = _
  rw [hrange, Submodule.finrank_sup_span_singleton hnot]
  change (binarySquareCenteredAdjacencyMatrix G q).rank + 1 = _
  rw [hcenter]

/-- **Exact adjacency nullity.**  The zero eigenspace has dimension exactly
`#components - 1`, upgrading the component-constant construction from a lower
bound to a complete description by dimension. -/
theorem binarySquare_regular_adjMatrix_nullity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Module.finrank ℝ (LinearMap.ker (G.adjMatrix ℝ).mulVecLin) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
  classical
  let A := (G.adjMatrix ℝ).mulVecLin
  let r := Fintype.card (secondOrderDefectGraph G).ConnectedComponent
  have hVcard : 0 < Fintype.card V := by rw [hcard]; positivity
  letI : Nonempty V := Fintype.card_pos_iff.mp hVcard
  have hrpos : 1 ≤ r := by
    dsimp [r]
    exact Fintype.card_pos
  have hrank := binarySquare_regular_adjMatrix_rank
    G hfree hq hreg hcard
  have hcount := binarySquare_regular_card_defectComponents_le
    G hfree hq hreg hcard
  have hrankNull := LinearMap.finrank_range_add_finrank_ker A
  have hcardfun : Module.finrank ℝ (V → ℝ) = Fintype.card V :=
    Module.finrank_fintype_fun_eq_card ℝ
  have hrankNull' :
      Module.finrank ℝ (LinearMap.range A) +
          Module.finrank ℝ (LinearMap.ker A) = q * q := by
    calc
      _ = Module.finrank ℝ (V → ℝ) := hrankNull
      _ = Fintype.card V := hcardfun
      _ = q * q := hcard
  change Module.finrank ℝ (LinearMap.ker A) = r - 1
  change r ≤ q at hcount
  have hrle : r ≤ q * q := by nlinarith
  change Module.finrank ℝ (LinearMap.range A) = (q * q - r) + 1 at hrank
  rw [hrank] at hrankNull'
  omega

end

end Erdos85
