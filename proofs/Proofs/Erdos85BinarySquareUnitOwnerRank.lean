import Proofs.Erdos85BinarySquareUnitOwnerProjection
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection

/-!
# Exact rank of a unit centered-owner sector

After normalization by `q⁻²`, a unit sector is an idempotent.  Its trace is
therefore its rank, giving the exact value `q - 1`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The trace of an idempotent real matrix is the dimension of its range. -/
theorem rank_eq_of_mul_self_eq_self_of_trace_eq_nat
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (k : ℕ)
    (hidem : A * A = A) (htrace : Matrix.trace A = k) :
    A.rank = k := by
  let f : (V → ℝ) →ₗ[ℝ] (V → ℝ) := A.toLin'
  have hf : IsIdempotentElem f := by
    rw [IsIdempotentElem]
    change A.toLin'.comp A.toLin' = A.toLin'
    rw [← Matrix.toLin'_mul, hidem]
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    LinearMap.IsIdempotentElem.isProj_range f hf
  have ht := hproj.trace
  rw [Matrix.trace_toLin'_eq] at ht
  change A.rank = k
  rw [Matrix.rank]
  change Module.finrank ℝ (LinearMap.range f) = k
  exact_mod_cast ht.symm.trans htrace

/-- Multiplication by a nonzero real scalar preserves matrix rank. -/
theorem rank_smul_real_of_ne_zero
    {M N : Type*} [Fintype M] [Fintype N]
    (A : Matrix M N ℝ) (a : ℝ) (ha : a ≠ 0) :
    (a • A).rank = A.rank := by
  rw [Matrix.rank, Matrix.rank]
  have hrange : LinearMap.range (a • A).mulVecLin =
      LinearMap.range A.mulVecLin := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨a • x, ?_⟩
      simp
    · rintro ⟨x, rfl⟩
      refine ⟨a⁻¹ • x, ?_⟩
      simp [ha]
  rw [hrange]

/-- A unit centered-owner sector has exact real matrix rank `q - 1`. -/
theorem binarySquare_regular_unit_centeredOwnerGram_real_rank
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
    C.rank = q - 1 := by
  dsimp
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let J : Matrix V V ℝ := fun _ _ ↦ 1
  let C : Matrix V V ℝ :=
    (q : ℝ) • (O.adjMatrix ℝ + (1 : Matrix V V ℝ)) - J
  let r : ℝ := (q : ℝ) ^ 2
  let E : Matrix V V ℝ := r⁻¹ • C
  have hr : r ≠ 0 := by
    dsimp [r]
    positivity
  have hpoly : C * C = r • C := by
    dsimp [r]
    simpa [C, O, J] using
      binarySquare_regular_unit_centeredOwnerGram_real_mul_self
        G hfree hq hreg hcard c hc
  have hidem : E * E = E := by
    dsimp [E]
    rw [Matrix.smul_mul, Matrix.mul_smul, hpoly]
    simp [smul_smul, hr]
  have htrO : Matrix.trace (O.adjMatrix ℝ) = 0 :=
    SimpleGraph.trace_adjMatrix (G := O) (α := ℝ)
  have htrJ : Matrix.trace J = (Fintype.card V : ℝ) := by
    simp [J, Matrix.trace, Matrix.diag]
  have htrC : Matrix.trace C = r * (q - 1 : ℕ) := by
    dsimp [C]
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
      htrO, Matrix.trace_one, htrJ, hcard]
    dsimp [r]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    push_cast
    ring
  have htrE : Matrix.trace E = (q - 1 : ℕ) := by
    dsimp [E]
    rw [Matrix.trace_smul, htrC]
    simp [smul_eq_mul, hr]
  have hrankE : E.rank = q - 1 :=
    rank_eq_of_mul_self_eq_self_of_trace_eq_nat E (q - 1) hidem htrE
  have hrankScale : E.rank = C.rank :=
    rank_smul_real_of_ne_zero C r⁻¹ (inv_ne_zero hr)
  simpa [C, O, J] using hrankScale.symm.trans hrankE

/-- The image space of a unit centered-owner sector has dimension `q - 1`. -/
theorem binarySquare_regular_unit_centeredOwnerGram_real_range_finrank
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
    Module.finrank ℝ (LinearMap.range C.mulVecLin) = q - 1 := by
  dsimp
  rw [← Matrix.rank]
  exact binarySquare_regular_unit_centeredOwnerGram_real_rank
    G hfree hq hreg hcard c hc

end


end Erdos85
