import Proofs.Erdos85FinalDyadicEndpointResidualDefectSeparation

/-!
# Exact defect profile of the endpoint residual cell

Residual vertices are low negative-shore vertices, so they send exactly `r`
defect edges into the shore.  The defect cut to the negative-high cell is
empty, forcing all remaining `q-1-r` defect neighbors back into the residual
cell itself.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every endpoint residual-cell vertex has shore defect-degree `r` and
residual defect-degree `q-1-r`. -/
theorem finalDyadic_endpoint_residual_defect_degree_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {w : V}
    (hw : w ∈ (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)) :
    ((secondOrderDefectGraph G).neighborFinset w ∩ S).card = r ∧
    ((secondOrderDefectGraph G).neighborFinset w ∩
      ((Finset.univ : Finset V) \ (S ∪
        finalDyadicNegativeHighCutCenters G S j r))).card = q - 1 - r := by
  let D := secondOrderDefectGraph G
  let M := finalDyadicNegativeHighCutCenters G S j r
  let W := (Finset.univ : Finset V) \ (S ∪ M)
  have hwData := Finset.mem_sdiff.mp hw
  have hwNotS : w ∉ S := fun hwS => hwData.2 (Finset.mem_union_left M hwS)
  have hwNotM : w ∉ M := fun hwM => hwData.2 (Finset.mem_union_right S hwM)
  have htwo := finalDyadic_negativeShore_defectCutDegree_twoLevel
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf w hwNotS
  have hS : (D.neighborFinset w ∩ S).card = r := by
    apply htwo.resolve_right
    intro hhigh
    exact hwNotM (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hwNotS, hhigh⟩)
  have hnoM :=
    finalDyadic_endpoint_residual_defectNeighbor_inter_negativeHigh_eq_empty
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hw
  change D.neighborFinset w ∩ M = ∅ at hnoM
  have hresSet : D.neighborFinset w ∩ W = D.neighborFinset w \ S := by
    ext x
    constructor
    · intro hx
      have hxData := Finset.mem_inter.mp hx
      exact Finset.mem_sdiff.mpr
        ⟨hxData.1, fun hxS =>
          (Finset.mem_sdiff.mp hxData.2).2 (Finset.mem_union_left M hxS)⟩
    · intro hx
      have hxData := Finset.mem_sdiff.mp hx
      have hxNotM : x ∉ M := by
        intro hxM
        have : x ∈ D.neighborFinset w ∩ M :=
          Finset.mem_inter.mpr ⟨hxData.1, hxM⟩
        rw [hnoM] at this
        simpa using this
      exact Finset.mem_inter.mpr
        ⟨hxData.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, fun hxUnion =>
            (Finset.mem_union.mp hxUnion).elim hxData.2 hxNotM⟩⟩
  have hDcard : (D.neighborFinset w).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard]
  have hpart := Finset.card_inter_add_card_sdiff (D.neighborFinset w) S
  rw [hS, hDcard] at hpart
  have hW : (D.neighborFinset w ∩ W).card = q - 1 - r := by
    rw [hresSet]
    omega
  exact ⟨hS, hW⟩

end

end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_residual_defect_degree_profile
