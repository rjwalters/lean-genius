import Proofs.Erdos85MuThreeAllTfGraphTransport

/-! # Graph interpretation of the native all-TF hit rows -/

namespace Erdos85

theorem mu3NativeRowVars_count_eq
    (shape : Mu3AllTfShape) (val : DimacsValuation) (u x : Nat) :
    seqPrefixTrue (mu3NativeVarsRow val (mu3NativeRowVars shape u x))
        (mu3NativeRowVars shape u x).size =
      (((mu3AllTfCells shape).filter fun cell =>
          cell / 8 = x && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
        val (mu3NativeEdgeId u (mu3NativeCellIndex shape cell))).count true := by
  rw [mu3Native_seqPrefixTrue_eq_count,
    mu3NativeVarsRow_ofFn_eq_arrayLitValues]
  simp [mu3NativeRowVars, mu3NativeArrayLitValues]
  apply congrArg (List.count true)
  apply List.map_congr_left
  intro cell hcell
  exact dimacsLitValue_natCast val (by simp [mu3NativeEdgeId])

theorem mu3NativeColumnVars_count_eq
    (shape : Mu3AllTfShape) (val : DimacsValuation) (u y : Nat) :
    seqPrefixTrue (mu3NativeVarsRow val (mu3NativeColumnVars shape u y))
        (mu3NativeColumnVars shape u y).size =
      (((mu3AllTfCells shape).filter fun cell =>
          cell % 8 = y && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
        val (mu3NativeEdgeId u (mu3NativeCellIndex shape cell))).count true := by
  rw [mu3Native_seqPrefixTrue_eq_count,
    mu3NativeVarsRow_ofFn_eq_arrayLitValues]
  simp [mu3NativeColumnVars, mu3NativeArrayLitValues]
  apply congrArg (List.count true)
  apply List.map_congr_left
  intro cell hcell
  exact dimacsLitValue_natCast val (by simp [mu3NativeEdgeId])

set_option maxRecDepth 100000 in
theorem mu3AllTfCells_length (shape : Mu3AllTfShape) :
    (mu3AllTfCells shape).length = 48 := by
  cases shape <;> native_decide

theorem mu3AllTfCellIndex_lt_48 (shape : Mu3AllTfShape) (cell : Nat)
    (hcell : cell ∈ mu3AllTfCells shape) :
    mu3NativeCellIndex shape cell < 48 := by
  rw [← mu3AllTfCells_length shape]
  exact List.idxOf_lt_length_of_mem hcell

/-- Exact graph-neighbor counts in every normalized grid row and column. -/
structure Mu3GraphGridHitCounts {W : Type*} [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) : Prop where
  row : ∀ u, u < 48 → ∀ x, x < 8 →
    (((mu3AllTfCells shape).filter fun cell =>
        cell / 8 = x && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
      mu3NormalizedGraphAdj G e
        (min u (mu3NativeCellIndex shape cell),
          max u (mu3NativeCellIndex shape cell))).count true =
      if mu3AllTfInternal shape x
          ((mu3AllTfCells shape).getD u 0 % 8) then 0 else 1
  column : ∀ u, u < 48 → ∀ y, y < 8 →
    (((mu3AllTfCells shape).filter fun cell =>
        cell % 8 = y && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
      mu3NormalizedGraphAdj G e
        (min u (mu3NativeCellIndex shape cell),
          max u (mu3NativeCellIndex shape cell))).count true =
      if mu3AllTfInternal shape
          ((mu3AllTfCells shape).getD u 0 / 8) y then 0 else 1

theorem mu3GraphGridHitCounts_to_normalized
    {W : Type*} [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3GraphGridHitCounts shape G e) :
    Mu3NormalizedHitCounts shape (mu3NormalizedGraphAdj G e) := by
  intro spec hspec
  simp only [mu3NativeHitSpecs, List.mem_flatMap, List.mem_range,
    List.mem_append, List.mem_map] at hspec
  obtain ⟨u, hu, hrow | hcol⟩ := hspec
  · obtain ⟨x, hx, rfl⟩ := hrow
    rw [mu3NativeRowVars_count_eq]
    change _ = if mu3AllTfInternal shape x
      ((mu3AllTfCells shape).getD u 0 % 8) then 0 else 1
    calc
      _ = (((mu3AllTfCells shape).filter fun cell =>
          cell / 8 = x && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
        mu3NormalizedGraphAdj G e
          (min u (mu3NativeCellIndex shape cell),
            max u (mu3NativeCellIndex shape cell))).count true := by
        apply congrArg (List.count true)
        apply List.map_congr_left
        intro cell hcell
        have hmem : cell ∈ mu3AllTfCells shape := List.mem_of_mem_filter hcell
        have hne : mu3NativeCellIndex shape cell ≠ u := by
          have hp : cell / 8 = x ∧ mu3NativeCellIndex shape cell ≠ u := by
            simpa using (List.mem_filter.mp hcell).2
          exact hp.2
        let fu : Fin 48 := ⟨u, hu⟩
        let fv : Fin 48 :=
          ⟨mu3NativeCellIndex shape cell,
            mu3AllTfCellIndex_lt_48 shape cell hmem⟩
        exact mu3NativeEdgeValOfPairRelation_edge
          (mu3NormalizedGraphAdj G e) fu fv
            (by exact fun huv => hne (Fin.ext_iff.mp huv).symm)
      _ = _ := h.row u hu x hx
  · obtain ⟨y, hy, rfl⟩ := hcol
    rw [mu3NativeColumnVars_count_eq]
    change _ = if mu3AllTfInternal shape
      ((mu3AllTfCells shape).getD u 0 / 8) y then 0 else 1
    calc
      _ = (((mu3AllTfCells shape).filter fun cell =>
          cell % 8 = y && mu3NativeCellIndex shape cell ≠ u).map fun cell =>
        mu3NormalizedGraphAdj G e
          (min u (mu3NativeCellIndex shape cell),
            max u (mu3NativeCellIndex shape cell))).count true := by
        apply congrArg (List.count true)
        apply List.map_congr_left
        intro cell hcell
        have hmem : cell ∈ mu3AllTfCells shape := List.mem_of_mem_filter hcell
        have hne : mu3NativeCellIndex shape cell ≠ u := by
          have hp : cell % 8 = y ∧ mu3NativeCellIndex shape cell ≠ u := by
            simpa using (List.mem_filter.mp hcell).2
          exact hp.2
        let fu : Fin 48 := ⟨u, hu⟩
        let fv : Fin 48 :=
          ⟨mu3NativeCellIndex shape cell,
            mu3AllTfCellIndex_lt_48 shape cell hmem⟩
        exact mu3NativeEdgeValOfPairRelation_edge
          (mu3NormalizedGraphAdj G e) fu fv
            (by exact fun huv => hne (Fin.ext_iff.mp huv).symm)
      _ = _ := h.column u hu y hy

/-- Fully graph-level certificate endpoint for a normalized all-TF grid. -/
theorem false_of_c4Free_mu3AllTfGraphGridHitCounts
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 W G) (e : Fin 48 ≃ W)
    (hhit : Mu3GraphGridHitCounts shape G e) : False :=
  false_of_c4Free_mu3AllTfGraphHitCounts G hfree e shape
    (mu3GraphGridHitCounts_to_normalized shape G e hhit)

end Erdos85
