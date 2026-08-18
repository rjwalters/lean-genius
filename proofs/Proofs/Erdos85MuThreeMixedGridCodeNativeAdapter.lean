import Proofs.Erdos85MuThreeFixedKNativeContradiction
import Proofs.Erdos85MuThreeAllTfGraphTransport
import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Transport a mixed-grid code into a fixed-K native certificate

The finite K-enumerator works on `Fin 8 × Fin 8`, while the native CNF uses
the increasing list of the 48 occupied cell numbers.  This module constructs
that enumeration and turns the abstract graph-code hit/C4 fields into the two
Boolean hypotheses of `false_of_mu3FixedKNativeStaticConstraints`.
-/

open SimpleGraph

namespace Erdos85

def mu3Fin8CellCode (p : Fin 8 × Fin 8) : Nat := p.1.val * 8 + p.2.val

theorem mu3Fin8CellCode_lt (p : Fin 8 × Fin 8) : mu3Fin8CellCode p < 64 := by
  unfold mu3Fin8CellCode
  omega

theorem mu3Fin8CellCode_div (p : Fin 8 × Fin 8) :
    mu3Fin8CellCode p / 8 = p.1.val := by
  unfold mu3Fin8CellCode
  omega

theorem mu3Fin8CellCode_mod (p : Fin 8 × Fin 8) :
    mu3Fin8CellCode p % 8 = p.2.val := by
  unfold mu3Fin8CellCode
  omega

theorem mu3Fin8CellCode_injective : Function.Injective mu3Fin8CellCode := by
  intro p q h
  apply Prod.ext
  · apply Fin.ext
    have := congrArg (fun n => n / 8) h
    simpa [mu3Fin8CellCode_div] using this
  · apply Fin.ext
    have := congrArg (fun n => n % 8) h
    simpa [mu3Fin8CellCode_mod] using this

set_option maxRecDepth 100000 in
theorem mu3FixedKGrid_cells_nodup (i : Fin 19) :
    (mu3FixedKGrid i).cells.Nodup := by
  fin_cases i <;> native_decide

set_option maxRecDepth 100000 in
theorem mu3FixedKGrid_cells_lt_64 (i : Fin 19) :
    ∀ cell ∈ (mu3FixedKGrid i).cells, cell < 64 := by
  have hcheck : (mu3FixedKGrid i).cells.all fun cell => decide (cell < 64) := by
    fin_cases i <;> native_decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using hcheck

def mu3FixedKCellPair (i : Fin 19) (u : Fin 48) : Fin 8 × Fin 8 :=
  let cell := (mu3FixedKGrid i).cells[u.val]'(by
    simpa [mu3FixedKGrid_cells_length i] using u.isLt)
  (⟨cell / 8, by
      have hcell : cell < 64 := mu3FixedKGrid_cells_lt_64 i cell
        (List.getElem_mem _)
      omega⟩,
    ⟨cell % 8, Nat.mod_lt _ (by omega)⟩)

theorem mu3FixedKCellPair_code (i : Fin 19) (u : Fin 48) :
    mu3Fin8CellCode (mu3FixedKCellPair i u) =
      (mu3FixedKGrid i).cells[u.val]'(by
        simpa [mu3FixedKGrid_cells_length i] using u.isLt) := by
  simp only [mu3FixedKCellPair, mu3Fin8CellCode]
  have hcell : (mu3FixedKGrid i).cells[u.val]'(by
      simpa [mu3FixedKGrid_cells_length i] using u.isLt) < 64 :=
    mu3FixedKGrid_cells_lt_64 i _ (List.getElem_mem _)
  omega

/-- The increasing native cell list canonically enumerates the abstract
occupied-cell subtype whenever `K` has that exact complement. -/
def mu3FixedKCellEquiv
    (i : Fin 19) (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells) :
    Fin 48 ≃ muThreeMixedCell K where
  toFun u := ⟨mu3FixedKCellPair i u,
    (hoccupied _ _).2 (by
      rw [mu3FixedKCellPair_code]
      exact List.getElem_mem _)⟩
  invFun p := ⟨(mu3FixedKGrid i).cells.idxOf (mu3Fin8CellCode p.1),
    by
      have hlt := List.idxOf_lt_length_iff.mpr ((hoccupied _ _).1 p.2)
      simpa [mu3FixedKGrid_cells_length i] using hlt⟩
  left_inv u := by
    apply Fin.ext
    simp only
    rw [mu3FixedKCellPair_code]
    exact (mu3FixedKGrid_cells_nodup i).idxOf_getElem u.val (by
      simpa [mu3FixedKGrid_cells_length i] using u.isLt)
  right_inv p := by
    apply Subtype.ext
    apply mu3Fin8CellCode_injective
    rw [mu3FixedKCellPair_code]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr
      ((hoccupied _ _).1 p.2))

@[simp] theorem mu3FixedKCellEquiv_code
    (i : Fin 19) (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells)
    (u : Fin 48) :
    mu3Fin8CellCode ((mu3FixedKCellEquiv i K hoccupied u).1) =
      (mu3FixedKGrid i).cells[u.val]'(by
        simpa [mu3FixedKGrid_cells_length i] using u.isLt) := by
  exact mu3FixedKCellPair_code i u

theorem mu3GridNativeRowVars_count_eq
    (grid : Mu3NativeGridSpec) (val : DimacsValuation) (u x : Nat) :
    seqPrefixTrue (mu3NativeVarsRow val (mu3GridRowVars grid u x))
        (mu3GridRowVars grid u x).size =
      ((grid.cells.filter fun cell =>
          cell / 8 = x && mu3GridCellIndex grid cell ≠ u).map fun cell =>
        val (mu3NativeEdgeId u (mu3GridCellIndex grid cell))).count true := by
  rw [mu3Native_seqPrefixTrue_eq_count,
    mu3NativeVarsRow_ofFn_eq_arrayLitValues]
  simp [mu3GridRowVars, mu3NativeArrayLitValues]
  apply congrArg (List.count true)
  apply List.map_congr_left
  intro cell hcell
  exact dimacsLitValue_natCast val (by simp [mu3NativeEdgeId])

theorem mu3GridNativeColumnVars_count_eq
    (grid : Mu3NativeGridSpec) (val : DimacsValuation) (u y : Nat) :
    seqPrefixTrue (mu3NativeVarsRow val (mu3GridColumnVars grid u y))
        (mu3GridColumnVars grid u y).size =
      ((grid.cells.filter fun cell =>
          cell % 8 = y && mu3GridCellIndex grid cell ≠ u).map fun cell =>
        val (mu3NativeEdgeId u (mu3GridCellIndex grid cell))).count true := by
  rw [mu3Native_seqPrefixTrue_eq_count,
    mu3NativeVarsRow_ofFn_eq_arrayLitValues]
  simp [mu3GridColumnVars, mu3NativeArrayLitValues]
  apply congrArg (List.count true)
  apply List.map_congr_left
  intro cell hcell
  exact dimacsLitValue_natCast val (by simp [mu3NativeEdgeId])

theorem mu3FixedKGridCellIndex_lt_48 (i : Fin 19) (cell : Nat)
    (hcell : cell ∈ (mu3FixedKGrid i).cells) :
    mu3GridCellIndex (mu3FixedKGrid i) cell < 48 := by
  rw [← mu3FixedKGrid_cells_length i]
  exact List.idxOf_lt_length_of_mem hcell

/-- Exact graph-neighbour counts in every row and column of a concrete fixed
grid, with vertices enumerated in native cell-list order. -/
structure Mu3FixedKGraphGridHitCounts
    {W : Type*} [DecidableEq W]
    (i : Fin 19) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) : Prop where
  row : ∀ u, u < 48 → ∀ x, x < 8 →
    (((mu3FixedKGrid i).cells.filter fun cell =>
        cell / 8 = x && mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u).map
      fun cell => mu3NormalizedGraphAdj G e
        (min u (mu3GridCellIndex (mu3FixedKGrid i) cell),
          max u (mu3GridCellIndex (mu3FixedKGrid i) cell))).count true =
      if (mu3FixedKGrid i).internal x
          ((mu3FixedKGrid i).cells.getD u 0 % 8) then 0 else 1
  column : ∀ u, u < 48 → ∀ y, y < 8 →
    (((mu3FixedKGrid i).cells.filter fun cell =>
        cell % 8 = y && mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u).map
      fun cell => mu3NormalizedGraphAdj G e
        (min u (mu3GridCellIndex (mu3FixedKGrid i) cell),
          max u (mu3GridCellIndex (mu3FixedKGrid i) cell))).count true =
      if (mu3FixedKGrid i).internal
          ((mu3FixedKGrid i).cells.getD u 0 / 8) y then 0 else 1

theorem mu3FixedKGraphGridHitCounts_to_native
    {W : Type*} [DecidableEq W]
    (i : Fin 19) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3FixedKGraphGridHitCounts i G e) :
    ∀ spec ∈ mu3GridHitSpecs (mu3FixedKGrid i),
      seqPrefixTrue
        (mu3NativeVarsRow
          (mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)) spec.1)
        spec.1.size = spec.2 := by
  intro spec hspec
  simp only [mu3GridHitSpecs, List.mem_flatMap, List.mem_range,
    List.mem_append, List.mem_map] at hspec
  obtain ⟨u, hu, hrow | hcol⟩ := hspec
  · obtain ⟨x, hx, rfl⟩ := hrow
    rw [mu3GridNativeRowVars_count_eq]
    change _ = if (mu3FixedKGrid i).internal x
      ((mu3FixedKGrid i).cells.getD u 0 % 8) then 0 else 1
    calc
      _ = (((mu3FixedKGrid i).cells.filter fun cell =>
          cell / 8 = x && mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u).map
        fun cell => mu3NormalizedGraphAdj G e
          (min u (mu3GridCellIndex (mu3FixedKGrid i) cell),
            max u (mu3GridCellIndex (mu3FixedKGrid i) cell))).count true := by
        apply congrArg (List.count true)
        apply List.map_congr_left
        intro cell hcell
        have hmem : cell ∈ (mu3FixedKGrid i).cells :=
          List.mem_of_mem_filter hcell
        have hne : mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u := by
          have hp : cell / 8 = x ∧
              mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u := by
            simpa using (List.mem_filter.mp hcell).2
          exact hp.2
        let fu : Fin 48 := ⟨u, hu⟩
        let fv : Fin 48 := ⟨mu3GridCellIndex (mu3FixedKGrid i) cell,
          mu3FixedKGridCellIndex_lt_48 i cell hmem⟩
        exact mu3NativeEdgeValOfPairRelation_edge
          (mu3NormalizedGraphAdj G e) fu fv
            (fun huv => hne (Fin.ext_iff.mp huv).symm)
      _ = _ := h.row u hu x hx
  · obtain ⟨y, hy, rfl⟩ := hcol
    rw [mu3GridNativeColumnVars_count_eq]
    change _ = if (mu3FixedKGrid i).internal
      ((mu3FixedKGrid i).cells.getD u 0 / 8) y then 0 else 1
    calc
      _ = (((mu3FixedKGrid i).cells.filter fun cell =>
          cell % 8 = y && mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u).map
        fun cell => mu3NormalizedGraphAdj G e
          (min u (mu3GridCellIndex (mu3FixedKGrid i) cell),
            max u (mu3GridCellIndex (mu3FixedKGrid i) cell))).count true := by
        apply congrArg (List.count true)
        apply List.map_congr_left
        intro cell hcell
        have hmem : cell ∈ (mu3FixedKGrid i).cells :=
          List.mem_of_mem_filter hcell
        have hne : mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u := by
          have hp : cell % 8 = y ∧
              mu3GridCellIndex (mu3FixedKGrid i) cell ≠ u := by
            simpa using (List.mem_filter.mp hcell).2
          exact hp.2
        let fu : Fin 48 := ⟨u, hu⟩
        let fv : Fin 48 := ⟨mu3GridCellIndex (mu3FixedKGrid i) cell,
          mu3FixedKGridCellIndex_lt_48 i cell hmem⟩
        exact mu3NativeEdgeValOfPairRelation_edge
          (mu3NormalizedGraphAdj G e) fu fv
            (fun huv => hne (Fin.ext_iff.mp huv).symm)
      _ = _ := h.column u hu y hy

theorem mu3FixedKGrid_cells_eq_finRange_map
    (i : Fin 19) (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells) :
    (mu3FixedKGrid i).cells =
      (List.finRange 48).map fun u =>
        mu3Fin8CellCode ((mu3FixedKCellEquiv i K hoccupied u).1) := by
  apply List.ext_getElem
  · simp [mu3FixedKGrid_cells_length i]
  · intro n hleft hright
    simp only [List.getElem_map, List.getElem_finRange]
    symm
    exact mu3FixedKCellEquiv_code i K hoccupied ⟨n, by simpa using hright⟩

theorem mu3FixedKGrid_cellIndex_equiv_code
    (i : Fin 19) (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells)
    (u : Fin 48) :
    mu3GridCellIndex (mu3FixedKGrid i)
      (mu3Fin8CellCode ((mu3FixedKCellEquiv i K hoccupied u).1)) = u.val := by
  rw [mu3FixedKCellEquiv_code]
  exact (mu3FixedKGrid_cells_nodup i).idxOf_getElem u.val (by
    simpa [mu3FixedKGrid_cells_length i] using u.isLt)

theorem List.count_true_filter_map_bool {α : Type*}
    (xs : List α) (p q : α → Bool) :
    ((xs.filter p).map q).count true =
      (xs.map fun a => p a && q a).count true := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      simp only [List.filter_cons, List.map_cons]
      cases hp : p a <;> cases hq : q a <;> simp [hp, hq, ih]

theorem finRange_map_count_true_eq_card {n : Nat} (f : Fin n → Bool) :
    ((List.finRange n).map f).count true =
      ((Finset.univ : Finset (Fin n)).filter fun i => f i = true).card := by
  let v : List.Vector Bool n := ⟨List.ofFn f, by simp⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  rw [← List.ofFn_eq_map]
  calc
    (List.ofFn f).count true =
        ((Finset.univ : Finset (Fin n)).filter fun i => v.get i = true).card :=
      h.symm
    _ = ((Finset.univ : Finset (Fin n)).filter fun i => f i = true).card := by
      congr 1
      ext i
      simp [v, List.Vector.get]

theorem mu3NormalizedGraphAdj_pair_eq_decide_adj
    {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (u v : Fin 48) :
    mu3NormalizedGraphAdj G e (min u.val v.val, max u.val v.val) =
      decide (G.Adj (e u) (e v)) := by
  rw [mu3NormalizedGraphAdj_pair G e u v]
  by_cases h : u ≤ v
  · simp [min_eq_left h, max_eq_right h]
  · have h' : v ≤ u := le_of_not_ge h
    simp [min_eq_right h', max_eq_left h', G.adj_comm]

theorem MuThreeMixedGridCode.fixedKGraphGridHitCounts
    (i : Fin 19) (H K : Fin 8 → Fin 8 → Prop)
    [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells)
    (hinternal : ∀ x y,
      H x y ↔ (mu3FixedKGrid i).internal x.val y.val = true) :
    Mu3FixedKGraphGridHitCounts i C
      (mu3FixedKCellEquiv i K hoccupied) := by
  let e := mu3FixedKCellEquiv i K hoccupied
  constructor
  · intro u hu x hx
    let fu : Fin 48 := ⟨u, hu⟩
    let fx : Fin 8 := ⟨x, hx⟩
    let source := (Finset.univ : Finset (Fin 48)).filter fun v =>
      v ≠ fu ∧ (e v).1.1 = fx ∧ C.Adj (e fu) (e v)
    have hsource : source.card =
        ((C.neighborFinset (e fu)).filter fun v => v.1.1 = fx).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        have hp := (Finset.mem_filter.mp hv).2
        exact Finset.mem_filter.mpr
          ⟨(C.mem_neighborFinset _ _).mpr hp.2.2, hp.2.1⟩
      · intro v _ w _ heq
        exact e.injective heq
      · intro w hw
        let v := e.symm w
        have hadj : C.Adj (e fu) w :=
          (C.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hw).1
        have hne : v ≠ fu := by
          intro hv
          change e.symm w = fu at hv
          have hw : w = e fu := by
            calc
              w = e (e.symm w) := (e.apply_symm_apply w).symm
              _ = e fu := by rw [hv]
          exact C.loopless.irrefl (e fu) (by simpa [hw] using hadj)
        refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, ?_, ?_⟩, ?_⟩
        · simpa [v] using (Finset.mem_filter.mp hw).2
        · simpa [v] using hadj
        · simp [v]
    let f : Fin 48 → Bool := fun v =>
      (decide (mu3Fin8CellCode ((e v).1) / 8 = x) &&
        decide (mu3GridCellIndex (mu3FixedKGrid i)
          (mu3Fin8CellCode ((e v).1)) ≠ u)) &&
        mu3NormalizedGraphAdj C e
          (min u (mu3GridCellIndex (mu3FixedKGrid i)
            (mu3Fin8CellCode ((e v).1))),
           max u (mu3GridCellIndex (mu3FixedKGrid i)
            (mu3Fin8CellCode ((e v).1))))
    have hfcard : ((Finset.univ : Finset (Fin 48)).filter fun v =>
        f v = true).card = source.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f,
        Bool.and_eq_true, decide_eq_true_eq]
      rw [mu3FixedKGrid_cellIndex_equiv_code i K hoccupied v]
      rw [mu3Fin8CellCode_div]
      rw [mu3NormalizedGraphAdj_pair_eq_decide_adj C e fu v]
      simp [source, fu, fx, Fin.ext_iff, and_assoc, and_comm]
    have hrow := code.row_hit (e fu) fx
    change _ = if (mu3FixedKGrid i).internal x
      ((mu3FixedKGrid i).cells.getD u 0 % 8) then 0 else 1
    conv_lhs =>
      rw [mu3FixedKGrid_cells_eq_finRange_map i K hoccupied]
    rw [List.count_true_filter_map_bool]
    simp only [List.map_map]
    change ((List.finRange 48).map f).count true = _
    rw [finRange_map_count_true_eq_card]
    rw [hfcard]
    rw [hsource, hrow]
    have hcellCode := mu3FixedKCellEquiv_code i K hoccupied fu
    have hy : ((e fu).1).2.val =
        (mu3FixedKGrid i).cells.getD u 0 % 8 := by
      rw [← mu3Fin8CellCode_mod ((e fu).1), hcellCode]
      have hlen : u < (mu3FixedKGrid i).cells.length := by
        simpa [mu3FixedKGrid_cells_length i] using hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      simp [fu]
    have hiff : H fx ((e fu).1).2 ↔
        (mu3FixedKGrid i).internal x
          ((mu3FixedKGrid i).cells.getD u 0 % 8) = true := by
      simpa [fx, hy] using hinternal fx ((e fu).1).2
    by_cases hH : H fx ((e fu).1).2
    · rw [if_pos hH, if_pos (hiff.mp hH)]
    · have hnot : ¬(mu3FixedKGrid i).internal x
          ((mu3FixedKGrid i).cells.getD u 0 % 8) = true :=
        fun ht => hH (hiff.mpr ht)
      rw [if_neg hH, if_neg hnot]

  · intro u hu y hy
    let fu : Fin 48 := ⟨u, hu⟩
    let fy : Fin 8 := ⟨y, hy⟩
    let source := (Finset.univ : Finset (Fin 48)).filter fun v =>
      v ≠ fu ∧ (e v).1.2 = fy ∧ C.Adj (e fu) (e v)
    have hsource : source.card =
        ((C.neighborFinset (e fu)).filter fun v => v.1.2 = fy).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        have hp := (Finset.mem_filter.mp hv).2
        exact Finset.mem_filter.mpr
          ⟨(C.mem_neighborFinset _ _).mpr hp.2.2, hp.2.1⟩
      · intro v _ w _ heq
        exact e.injective heq
      · intro w hw
        let v := e.symm w
        have hadj : C.Adj (e fu) w :=
          (C.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hw).1
        have hne : v ≠ fu := by
          intro hv
          change e.symm w = fu at hv
          have hwEq : w = e fu := by
            calc
              w = e (e.symm w) := (e.apply_symm_apply w).symm
              _ = e fu := by rw [hv]
          exact C.loopless.irrefl (e fu) (by simpa [hwEq] using hadj)
        refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, ?_, ?_⟩, ?_⟩
        · simpa [v] using (Finset.mem_filter.mp hw).2
        · simpa [v] using hadj
        · simp [v]
    let f : Fin 48 → Bool := fun v =>
      (decide (mu3Fin8CellCode ((e v).1) % 8 = y) &&
        decide (mu3GridCellIndex (mu3FixedKGrid i)
          (mu3Fin8CellCode ((e v).1)) ≠ u)) &&
        mu3NormalizedGraphAdj C e
          (min u (mu3GridCellIndex (mu3FixedKGrid i)
            (mu3Fin8CellCode ((e v).1))),
           max u (mu3GridCellIndex (mu3FixedKGrid i)
            (mu3Fin8CellCode ((e v).1))))
    have hfcard : ((Finset.univ : Finset (Fin 48)).filter fun v =>
        f v = true).card = source.card := by
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f,
        Bool.and_eq_true, decide_eq_true_eq]
      rw [mu3FixedKGrid_cellIndex_equiv_code i K hoccupied v]
      rw [mu3Fin8CellCode_mod]
      rw [mu3NormalizedGraphAdj_pair_eq_decide_adj C e fu v]
      simp [source, fu, fy, Fin.ext_iff, and_assoc, and_comm]
    have hcolumn := code.column_hit (e fu) fy
    change _ = if (mu3FixedKGrid i).internal
      ((mu3FixedKGrid i).cells.getD u 0 / 8) y then 0 else 1
    conv_lhs =>
      rw [mu3FixedKGrid_cells_eq_finRange_map i K hoccupied]
    rw [List.count_true_filter_map_bool]
    simp only [List.map_map]
    change ((List.finRange 48).map f).count true = _
    rw [finRange_map_count_true_eq_card]
    rw [hfcard]
    rw [hsource, hcolumn]
    have hcellCode := mu3FixedKCellEquiv_code i K hoccupied fu
    have hx : ((e fu).1).1.val =
        (mu3FixedKGrid i).cells.getD u 0 / 8 := by
      rw [← mu3Fin8CellCode_div ((e fu).1), hcellCode]
      have hlen : u < (mu3FixedKGrid i).cells.length := by
        simpa [mu3FixedKGrid_cells_length i] using hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      simp [fu]
    have hiff : H ((e fu).1).1 fy ↔
        (mu3FixedKGrid i).internal
          ((mu3FixedKGrid i).cells.getD u 0 / 8) y = true := by
      simpa [fy, hx] using hinternal ((e fu).1).1 fy
    by_cases hH : H ((e fu).1).1 fy
    · rw [if_pos hH, if_pos (hiff.mp hH)]
    · have hnot : ¬(mu3FixedKGrid i).internal
          ((mu3FixedKGrid i).cells.getD u 0 / 8) y = true :=
        fun ht => hH (hiff.mpr ht)
      rw [if_neg hH, if_neg hnot]

/-- Abstract-code form of the fixed-K certificate contradiction.  The only
coordinate hypotheses say that the candidate's occupied cells and internal
relation are the concrete native record; all graph-to-CNF transport follows
from the fields of `MuThreeMixedGridCode` itself. -/
theorem false_of_muThreeMixedGridCode_fixedK
    (i : Fin 19) (H K : Fin 8 → Fin 8 → Prop)
    [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hoccupied : ∀ x y, ¬ K x y ↔
      mu3Fin8CellCode (x, y) ∈ (mu3FixedKGrid i).cells)
    (hinternal : ∀ x y,
      H x y ↔ (mu3FixedKGrid i).internal x.val y.val = true) : False := by
  let e := mu3FixedKCellEquiv i K hoccupied
  let edgeVal := mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj C e)
  apply false_of_mu3FixedKNativeStaticConstraints i edgeVal
  · exact mu3FixedKGraphGridHitCounts_to_native i C e
      (code.fixedKGraphGridHitCounts i H K C hoccupied hinternal)
  · exact mu3NormalizedBaseC4_of_c4Free C code.c4Free e

end Erdos85

#print axioms Erdos85.mu3FixedKGrid_cells_nodup
#print axioms Erdos85.mu3FixedKGrid_cells_lt_64
#print axioms Erdos85.MuThreeMixedGridCode.fixedKGraphGridHitCounts
#print axioms Erdos85.false_of_muThreeMixedGridCode_fixedK
