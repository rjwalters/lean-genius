import Proofs.Erdos85BinarySquareAdjacencyKernelCharacterization

/-!
# Rational square-order adjacency kernel

The real pointwise kernel classification descends faithfully to `ℚ`.  This is
the scalar field used by the component-constant kernel and owner-bottom-space
interfaces.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rational form of the complete zero-eigenspace description. -/
theorem binarySquare_regular_adjMatrix_mulVec_eq_zero_iff_rat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (v : V → ℚ) :
    (G.adjMatrix ℚ).mulVec v = 0 ↔
      (∀ x y, (secondOrderDefectGraph G).Reachable x y → v x = v y) ∧
        ∑ x, v x = 0 := by
  let vR : V → ℝ := fun x => (v x : ℝ)
  have hcast (x : V) :
      (G.adjMatrix ℝ).mulVec vR x =
        (((G.adjMatrix ℚ).mulVec v x : ℚ) : ℝ) := by
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    simp only [vR, SimpleGraph.adjMatrix_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro y _hy
    by_cases hxy : G.Adj x y <;> simp [hxy]
  have hsumcast : (∑ x, vR x) = (((∑ x, v x : ℚ) : ℚ) : ℝ) := by
    simp [vR]
  constructor
  · intro hQ
    have hR : (G.adjMatrix ℝ).mulVec vR = 0 := by
      funext x
      rw [hcast x, congrFun hQ x]
      norm_num
    obtain ⟨hconstR, hsumR⟩ :=
      (binarySquare_regular_adjMatrix_mulVec_eq_zero_iff
        G hfree hq hreg hcard vR).mp hR
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have h := hconstR x y hxy
      change (v x : ℝ) = (v y : ℝ) at h
      exact Rat.cast_injective h
    · rw [hsumcast] at hsumR
      exact_mod_cast hsumR
  · rintro ⟨hconstQ, hsumQ⟩
    have hconstR : ∀ x y, (secondOrderDefectGraph G).Reachable x y →
        vR x = vR y := by
      intro x y hxy
      change (v x : ℝ) = (v y : ℝ)
      exact congrArg (fun z : ℚ => (z : ℝ)) (hconstQ x y hxy)
    have hsumR : ∑ x, vR x = 0 := by
      rw [hsumcast, hsumQ]
      norm_num
    have hR : (G.adjMatrix ℝ).mulVec vR = 0 :=
      (binarySquare_regular_adjMatrix_mulVec_eq_zero_iff
        G hfree hq hreg hcard vR).mpr ⟨hconstR, hsumR⟩
    funext x
    have hx := congrFun hR x
    rw [hcast x] at hx
    change (G.adjMatrix ℚ).mulVec v x = 0
    apply Rat.cast_injective (α := ℝ)
    simpa using hx

end

end Erdos85
