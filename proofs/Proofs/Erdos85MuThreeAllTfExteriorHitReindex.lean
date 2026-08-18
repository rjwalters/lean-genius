import Proofs.Erdos85MuThreeAllTfExteriorHitTransport

/-! # Reindexing exterior hit fibers through the canonical occupied-cell list -/

open SimpleGraph

namespace Erdos85

noncomputable section

def mu3CellVertex {W : Type*} (shape : Mu3AllTfShape)
    (e : Fin 48 ≃ W) (cell : Nat) : W :=
  if h : mu3NativeCellIndex shape cell < 48 then
    e ⟨mu3NativeCellIndex shape cell, h⟩
  else e 0

theorem mu3CellVertex_of_mem {W : Type*} (shape : Mu3AllTfShape)
    (e : Fin 48 ≃ W) (cell : Nat) (hcell : cell ∈ mu3AllTfCells shape) :
    mu3CellVertex shape e cell =
      e ⟨mu3NativeCellIndex shape cell,
        mu3AllTfCellIndex_lt_48 shape cell hcell⟩ := by
  simp [mu3CellVertex, mu3AllTfCellIndex_lt_48 shape cell hcell]

theorem mu3CellVertex_injective_on_cells {W : Type*}
    (shape : Mu3AllTfShape) (e : Fin 48 ≃ W) :
    Set.InjOn (mu3CellVertex shape e) {cell | cell ∈ mu3AllTfCells shape} := by
  intro a ha b hb hab
  rw [mu3CellVertex_of_mem shape e a ha,
    mu3CellVertex_of_mem shape e b hb] at hab
  apply (List.idxOf_inj ha).mp
  exact congrArg Fin.val (e.injective hab)

theorem mu3NativeCellIndex_shapeCellEquiv (shape : Mu3AllTfShape)
    (i : Fin 48) :
    mu3NativeCellIndex shape (mu3AllTfShapeCellEquiv shape i).1 = i.val := by
  revert i
  cases shape <;> native_decide

theorem mu3ExteriorHitImages_row_list_count_eq_fiber
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3ExteriorHitImages shape G e)
    (u : Fin 48) (x : Fin 8) :
    (((mu3AllTfCells shape).filter fun cell =>
        cell / 8 = x.val && mu3NativeCellIndex shape cell ≠ u.val).map fun cell =>
      mu3NormalizedGraphAdj G e
        (min u.val (mu3NativeCellIndex shape cell),
          max u.val (mu3NativeCellIndex shape cell))).count true =
      (Finset.univ.filter fun v : W =>
        G.Adj (e u) v ∧ h.rowCoord v = x).card := by
  classical
  let L := (mu3AllTfCells shape).filter fun cell =>
    cell / 8 = x.val && mu3NativeCellIndex shape cell ≠ u.val
  let p : Nat → Bool := fun cell =>
    mu3NormalizedGraphAdj G e
      (min u.val (mu3NativeCellIndex shape cell),
        max u.val (mu3NativeCellIndex shape cell))
  let T := (L.filter fun cell => p cell = true).toFinset
  let S := Finset.univ.filter fun v : W =>
    G.Adj (e u) v ∧ h.rowCoord v = x
  change (L.map p).count true = S.card
  rw [List.count_eq_length_filter]
  simp only [List.filter_map, List.length_map]
  change (L.filter fun cell => p cell == true).length = S.card
  have hnodup : (L.filter fun cell => p cell == true).Nodup :=
    ((mu3AllTfCells_nodup shape).filter _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  change T.card = S.card
  have hinj : Set.InjOn (mu3CellVertex shape e) T := by
    intro a ha b hb hab
    apply mu3CellVertex_injective_on_cells shape e
    · exact List.mem_of_mem_filter (List.mem_of_mem_filter
        (List.mem_toFinset.mp ha))
    · exact List.mem_of_mem_filter (List.mem_of_mem_filter
        (List.mem_toFinset.mp hb))
    · exact hab
  rw [← Finset.card_image_iff.mpr hinj]
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, S]
  constructor
  · rintro ⟨cell, hcellT, rfl⟩
    have hfilter := List.mem_toFinset.mp hcellT
    have hp := (List.mem_filter.mp hfilter).2
    have hL := List.mem_of_mem_filter hfilter
    obtain ⟨hcell, hpair⟩ := List.mem_filter.mp hL
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair
    obtain ⟨hx, hne⟩ := hpair
    have hi := mu3AllTfCellIndex_lt_48 shape cell hcell
    let i : Fin 48 := ⟨mu3NativeCellIndex shape cell, hi⟩
    have hadj : G.Adj (e u) (e i) := by
      have hn := mu3NormalizedGraphAdj_pair G e u i
      have hp' : p cell = true := by simpa using hp
      change mu3NormalizedGraphAdj G e (min u.val i.val, max u.val i.val) = true at hp'
      rw [hn] at hp'
      by_cases hui : u ≤ i
      · simpa [min_eq_left hui, max_eq_right hui] using hp'
      · have hiu : i ≤ u := le_of_not_ge hui
        simpa [min_eq_right hiu, max_eq_left hiu, G.adj_comm] using hp'
    have hcellval : (mu3AllTfCells shape).getD i.val 0 = cell := by
      simp [i, mu3NativeCellIndex, hcell]
    have hc := h.coord i
    have hrow : h.rowCoord (e i) = x := by
      apply Fin.ext
      rw [hcellval] at hc
      omega
    rw [mu3CellVertex_of_mem shape e cell hcell]
    exact ⟨hadj, hrow⟩
  · rintro ⟨hadj, hrow⟩
    let i : Fin 48 := e.symm v
    let cell := (mu3AllTfShapeCellEquiv shape i).1
    have hcell : cell ∈ mu3AllTfCells shape :=
      (mu3AllTfShapeCellEquiv shape i).2
    have hidx : mu3NativeCellIndex shape cell = i.val :=
      mu3NativeCellIndex_shapeCellEquiv shape i
    have hne : i ≠ u := by
      intro hiu
      have hev : v = e u := by
        calc
          v = e (e.symm v) := (e.apply_symm_apply v).symm
          _ = e u := congrArg e (by exact hiu)
      rw [hev] at hadj
      exact G.loopless.irrefl _ hadj
    have hx : cell / 8 = x.val := by
      have hc := h.coord i
      rw [e.apply_symm_apply v, hrow] at hc
      rw [← mu3AllTfShapeCellEquiv_val shape i] at hc
      change x.val * 8 + (h.columnCoord v).val = cell at hc
      omega
    refine ⟨cell, ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact hcell
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hx, by
            rw [hidx]
            exact fun heq => hne (Fin.ext heq)⟩
      · simp only [decide_eq_true_eq]
        simp only [p]
        rw [hidx]
        rw [mu3NormalizedGraphAdj_pair G e u i]
        have hadj' : G.Adj (e u) (e i) := by simpa [i] using hadj
        by_cases hui : u ≤ i
        · simpa [min_eq_left hui, max_eq_right hui] using hadj'
        · have hiu : i ≤ u := le_of_not_ge hui
          simpa [min_eq_right hiu, max_eq_left hiu, G.adj_comm] using hadj'
    · rw [mu3CellVertex_of_mem shape e cell hcell]
      simp [i, hidx]

theorem mu3ExteriorHitImages_column_list_count_eq_fiber
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3ExteriorHitImages shape G e)
    (u : Fin 48) (y : Fin 8) :
    (((mu3AllTfCells shape).filter fun cell =>
        cell % 8 = y.val && mu3NativeCellIndex shape cell ≠ u.val).map fun cell =>
      mu3NormalizedGraphAdj G e
        (min u.val (mu3NativeCellIndex shape cell),
          max u.val (mu3NativeCellIndex shape cell))).count true =
      (Finset.univ.filter fun v : W =>
        G.Adj (e u) v ∧ h.columnCoord v = y).card := by
  classical
  let L := (mu3AllTfCells shape).filter fun cell =>
    cell % 8 = y.val && mu3NativeCellIndex shape cell ≠ u.val
  let p : Nat → Bool := fun cell =>
    mu3NormalizedGraphAdj G e
      (min u.val (mu3NativeCellIndex shape cell),
        max u.val (mu3NativeCellIndex shape cell))
  let T := (L.filter fun cell => p cell = true).toFinset
  let S := Finset.univ.filter fun v : W =>
    G.Adj (e u) v ∧ h.columnCoord v = y
  change (L.map p).count true = S.card
  rw [List.count_eq_length_filter]
  simp only [List.filter_map, List.length_map]
  change (L.filter fun cell => p cell == true).length = S.card
  have hnodup : (L.filter fun cell => p cell == true).Nodup :=
    ((mu3AllTfCells_nodup shape).filter _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  change T.card = S.card
  have hinj : Set.InjOn (mu3CellVertex shape e) T := by
    intro a ha b hb hab
    apply mu3CellVertex_injective_on_cells shape e
    · exact List.mem_of_mem_filter (List.mem_of_mem_filter
        (List.mem_toFinset.mp ha))
    · exact List.mem_of_mem_filter (List.mem_of_mem_filter
        (List.mem_toFinset.mp hb))
    · exact hab
  rw [← Finset.card_image_iff.mpr hinj]
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, S]
  constructor
  · rintro ⟨cell, hcellT, rfl⟩
    have hfilter := List.mem_toFinset.mp hcellT
    have hp := (List.mem_filter.mp hfilter).2
    have hL := List.mem_of_mem_filter hfilter
    obtain ⟨hcell, hpair⟩ := List.mem_filter.mp hL
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpair
    obtain ⟨hy, hne⟩ := hpair
    have hi := mu3AllTfCellIndex_lt_48 shape cell hcell
    let i : Fin 48 := ⟨mu3NativeCellIndex shape cell, hi⟩
    have hadj : G.Adj (e u) (e i) := by
      have hn := mu3NormalizedGraphAdj_pair G e u i
      have hp' : p cell = true := by simpa using hp
      change mu3NormalizedGraphAdj G e (min u.val i.val, max u.val i.val) = true at hp'
      rw [hn] at hp'
      by_cases hui : u ≤ i
      · simpa [min_eq_left hui, max_eq_right hui] using hp'
      · have hiu : i ≤ u := le_of_not_ge hui
        simpa [min_eq_right hiu, max_eq_left hiu, G.adj_comm] using hp'
    have hcellval : (mu3AllTfCells shape).getD i.val 0 = cell := by
      simp [i, mu3NativeCellIndex, hcell]
    have hc := h.coord i
    have hcolumn : h.columnCoord (e i) = y := by
      apply Fin.ext
      rw [hcellval] at hc
      omega
    rw [mu3CellVertex_of_mem shape e cell hcell]
    exact ⟨hadj, hcolumn⟩
  · rintro ⟨hadj, hcolumn⟩
    let i : Fin 48 := e.symm v
    let cell := (mu3AllTfShapeCellEquiv shape i).1
    have hcell : cell ∈ mu3AllTfCells shape :=
      (mu3AllTfShapeCellEquiv shape i).2
    have hidx : mu3NativeCellIndex shape cell = i.val :=
      mu3NativeCellIndex_shapeCellEquiv shape i
    have hne : i ≠ u := by
      intro hiu
      have hev : v = e u := by
        calc
          v = e (e.symm v) := (e.apply_symm_apply v).symm
          _ = e u := congrArg e (by exact hiu)
      rw [hev] at hadj
      exact G.loopless.irrefl _ hadj
    have hy : cell % 8 = y.val := by
      have hc := h.coord i
      rw [e.apply_symm_apply v, hcolumn] at hc
      rw [← mu3AllTfShapeCellEquiv_val shape i] at hc
      change (h.rowCoord v).val * 8 + y.val = cell at hc
      omega
    refine ⟨cell, ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact hcell
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hy, by
            rw [hidx]
            exact fun heq => hne (Fin.ext heq)⟩
      · simp only [decide_eq_true_eq]
        simp only [p]
        rw [hidx]
        rw [mu3NormalizedGraphAdj_pair G e u i]
        have hadj' : G.Adj (e u) (e i) := by simpa [i] using hadj
        by_cases hui : u ≤ i
        · simpa [min_eq_left hui, max_eq_right hui] using hadj'
        · have hiu : i ≤ u := le_of_not_ge hui
          simpa [min_eq_right hiu, max_eq_left hiu, G.adj_comm] using hadj'
    · rw [mu3CellVertex_of_mem shape e cell hcell]
      simp [i, hidx]

theorem mu3ExteriorHitImages_rowCoord_eq (shape : Mu3AllTfShape)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (h : Mu3ExteriorHitImages shape G e) (i : Fin 48) :
    (h.rowCoord (e i)).val = (mu3AllTfCells shape).getD i.val 0 / 8 := by
  have hc := h.coord i
  omega

theorem mu3ExteriorHitImages_columnCoord_eq (shape : Mu3AllTfShape)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (h : Mu3ExteriorHitImages shape G e) (i : Fin 48) :
    (h.columnCoord (e i)).val = (mu3AllTfCells shape).getD i.val 0 % 8 := by
  have hc := h.coord i
  omega

/-- Exact exterior coordinate images, expressed in the canonical occupied-cell
enumeration, supply every native row and column hit count. -/
theorem mu3GraphGridHitCounts_of_exteriorHitImages
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3ExteriorHitImages shape G e) :
    Mu3GraphGridHitCounts shape G e where
  row u hu x hx := by
    let fu : Fin 48 := ⟨u, hu⟩
    let fx : Fin 8 := ⟨x, hx⟩
    rw [mu3ExteriorHitImages_row_list_count_eq_fiber shape G e h fu fx]
    rw [mu3ExteriorHitImages_row_fiber_card shape G e h (e fu) fx]
    rw [mu3ExteriorHitImages_columnCoord_eq shape G e h fu]
  column u hu y hy := by
    let fu : Fin 48 := ⟨u, hu⟩
    let fy : Fin 8 := ⟨y, hy⟩
    rw [mu3ExteriorHitImages_column_list_count_eq_fiber shape G e h fu fy]
    rw [mu3ExteriorHitImages_column_fiber_card shape G e h (e fu) fy]
    rw [mu3ExteriorHitImages_rowCoord_eq shape G e h fu]

#print axioms mu3GraphGridHitCounts_of_exteriorHitImages

end

end Erdos85
