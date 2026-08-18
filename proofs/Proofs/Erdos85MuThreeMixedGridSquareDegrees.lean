import Proofs.Erdos85MuThreeMixedGridSquarePartition
import Proofs.Erdos85ConflictRegular

/-!
# Degrees in the mixed-grid square partition

The common-neighbour graph is the standard conflict graph of the exterior.
Its degree is therefore `6 * 5 = 30`.  The rook and residual degree counts
complete the intrinsic `30 + 10 + 7 = 47` partition.
-/

open SimpleGraph

namespace Erdos85

/-- Under C4-freeness, "has a common neighbour" is equivalent to "has
exactly one common neighbour". -/
theorem MuThreeMixedGridCode.commonNeighborGraph_eq_conflict
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridCommonNeighborGraph K C = commonNeighborConflict C := by
  ext u v
  simp only [mixedGridCommonNeighborGraph, commonNeighborConflict_adj_iff]
  constructor
  · rintro ⟨hne, hone⟩
    exact ⟨hne, Finset.card_pos.mp (by omega)⟩
  · rintro ⟨hne, hnonempty⟩
    refine ⟨hne, ?_⟩
    have hpos : 0 < (C.neighborFinset u ∩ C.neighborFinset v).card :=
      Finset.card_pos.mpr hnonempty
    have hle := MuThreeMixedGridCode.common_neighbor_card_le_one
      H K C code u v hne
    omega

/-- The common-neighbour relation in every mixed grid code is 30-regular. -/
theorem MuThreeMixedGridCode.commonNeighborGraph_degree_eq_thirty
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridCommonNeighborGraph K C).degree u = 30 := by
  rw [← (mixedGridCommonNeighborGraph K C).card_neighborFinset_eq_degree]
  have hgraph := MuThreeMixedGridCode.commonNeighborGraph_eq_conflict H K C code
  have hfinset : (mixedGridCommonNeighborGraph K C).neighborFinset u =
      (commonNeighborConflict C).neighborFinset u := by
    ext v
    simp only [mem_neighborFinset]
    exact iff_of_eq (congrArg (fun G : SimpleGraph (muThreeMixedCell K) =>
      G.Adj u v) hgraph)
  rw [hfinset, (commonNeighborConflict C).card_neighborFinset_eq_degree]
  have hdegree := degree_commonNeighborConflict_of_regular_c4Free
    C code.c4Free (fun v => MuThreeMixedGridCode.degree_eq_six H K C code v) u
  norm_num at hdegree ⊢
  exact hdegree

/-- Every row contains six occupied cells: the forbidden factor uses exactly
two of its eight positions. -/
theorem MuThreeMixedGridCode.occupied_row_card_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x : X) :
    ((Finset.univ : Finset (muThreeMixedCell K)).filter
      fun u => u.1.1 = x).card = 6 := by
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun u => u.1.1 = x
  let T := (Finset.univ : Finset Y).filter fun y => ¬ K x y
  have hST : S.card = T.card := by
    apply Finset.card_bij (fun u _hu => u.1.2)
    · intro u hu
      have huS := Finset.mem_filter.mp hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [huS.2] using u.2
    · intro u hu v hv heq
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hu).2.trans
          (Finset.mem_filter.mp hv).2.symm
      · exact heq
    · intro y hy
      have hyK : ¬ K x y := (Finset.mem_filter.mp hy).2
      let u : muThreeMixedCell K := ⟨(x, y), hyK⟩
      refine ⟨u, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hK := code.K_twoRegular.1 x
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Y)) (p := fun y => K x y)
  simp only [Finset.card_univ, code.card_right] at hpartition
  rw [hK] at hpartition
  have hT : T.card = 6 := by
    change ((Finset.univ : Finset Y).filter fun y => ¬ K x y).card = 6
    omega
  change S.card = 6
  rw [hST, hT]

/-- Column dual of the occupied-row count. -/
theorem MuThreeMixedGridCode.occupied_column_card_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y : Y) :
    ((Finset.univ : Finset (muThreeMixedCell K)).filter
      fun u => u.1.2 = y).card = 6 := by
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun u => u.1.2 = y
  let T := (Finset.univ : Finset X).filter fun x => ¬ K x y
  have hST : S.card = T.card := by
    apply Finset.card_bij (fun u _hu => u.1.1)
    · intro u hu
      have huS := Finset.mem_filter.mp hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [huS.2] using u.2
    · intro u hu v hv heq
      apply Subtype.ext
      apply Prod.ext
      · exact heq
      · exact (Finset.mem_filter.mp hu).2.trans
          (Finset.mem_filter.mp hv).2.symm
    · intro x hx
      have hxK : ¬ K x y := (Finset.mem_filter.mp hx).2
      let u : muThreeMixedCell K := ⟨(x, y), hxK⟩
      refine ⟨u, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hK := code.K_twoRegular.2 y
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => K x y)
  simp only [Finset.card_univ, code.card_left] at hpartition
  rw [hK] at hpartition
  have hT : T.card = 6 := by
    change ((Finset.univ : Finset X).filter fun x => ¬ K x y).card = 6
    omega
  change S.card = 6
  rw [hST, hT]

/-- The rook relation is 10-regular: five other occupied cells in the row and
five in the column. -/
theorem MuThreeMixedGridCode.rowColumnGraph_degree_eq_ten
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridRowColumnGraph K).degree u = 10 := by
  let R := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun v => v.1.1 = u.1.1
  let L := R.erase u
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun v => v.1.2 = u.1.2
  let M := S.erase u
  have huR : u ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hRcard : R.card = 6 :=
    MuThreeMixedGridCode.occupied_row_card_eq_six H K C code u.1.1
  have hScard : S.card = 6 :=
    MuThreeMixedGridCode.occupied_column_card_eq_six H K C code u.1.2
  have hLcard : L.card = 5 := by
    change (R.erase u).card = 5
    rw [Finset.card_erase_of_mem huR, hRcard]
  have hMcard : M.card = 5 := by
    change (S.erase u).card = 5
    rw [Finset.card_erase_of_mem huS, hScard]
  have hdisjoint : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro v hvL hvM
    have hvR := Finset.mem_erase.mp hvL
    have hvS := Finset.mem_erase.mp hvM
    apply hvR.1
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp hvR.2).2
    · exact (Finset.mem_filter.mp hvS.2).2
  have hneighbors : (mixedGridRowColumnGraph K).neighborFinset u = L ∪ M := by
    ext v
    simp only [mem_neighborFinset, mixedGridRowColumnGraph,
      Finset.mem_union, L, M, Finset.mem_erase, R, S,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hrow | hcol⟩
      · exact Or.inl ⟨hne.symm, hrow.symm⟩
      · exact Or.inr ⟨hne.symm, hcol.symm⟩
    · rintro (⟨hne, hrow⟩ | ⟨hne, hcol⟩)
      · exact ⟨hne.symm, Or.inl hrow.symm⟩
      · exact ⟨hne.symm, Or.inr hcol.symm⟩
  rw [← (mixedGridRowColumnGraph K).card_neighborFinset_eq_degree,
    hneighbors, Finset.card_union_of_disjoint hdisjoint, hLcard, hMcard]

/-- The occupied-cell set has size `8 · 6 = 48`. -/
theorem MuThreeMixedGridCode.card_mixedCell_eq_fortyEight
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    Fintype.card (muThreeMixedCell K) = 48 := by
  rw [← Finset.card_univ]
  have hmaps : ∀ u ∈ (Finset.univ : Finset (muThreeMixedCell K)),
      u.1.1 ∈ (Finset.univ : Finset X) := by
    intro u _hu
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ x : X, (((Finset.univ : Finset (muThreeMixedCell K)).filter
        fun u => u.1.1 = x).card) = ∑ _x : X, 6 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact MuThreeMixedGridCode.occupied_row_card_eq_six H K C code x
    _ = 48 := by simp [code.card_left]

/-- The residual square relation is 7-regular.  Its neighbours are the 47
other cells left after the disjoint 30 common-neighbour and 10 rook cells. -/
theorem MuThreeMixedGridCode.squareResidualGraph_degree_eq_seven
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridSquareResidualGraph K C).degree u = 7 := by
  let Q := (mixedGridCommonNeighborGraph K C).neighborFinset u
  let D := (mixedGridSquareResidualGraph K C).neighborFinset u
  let R := (mixedGridRowColumnGraph K).neighborFinset u
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    intro v hvQ hvR
    have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp hvQ
    have hr := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp hvR
    have hzero := MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
      H K C code hr
    have hone := hq.2
    omega
  have hDQR : Disjoint D (Q ∪ R) := by
    rw [Finset.disjoint_left]
    intro v hvD hvQR
    have hd := ((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp hvD
    rcases Finset.mem_union.mp hvQR with hvQ | hvR
    · have hq := ((mixedGridCommonNeighborGraph K C).mem_neighborFinset u v).mp hvQ
      have hzero := hd.2.2
      have hone := hq.2
      omega
    · have hr := ((mixedGridRowColumnGraph K).mem_neighborFinset u v).mp hvR
      exact hd.2.1 hr
  have hcover : D ∪ (Q ∪ R) =
      (Finset.univ : Finset (muThreeMixedCell K)).erase u := by
    ext v
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true,
      Q, D, R, mem_neighborFinset]
    have hpartition := MuThreeMixedGridCode.square_partition_sup_eq_top
      H K C code
    have hadj := iff_of_eq (congrArg
      (fun G : SimpleGraph (muThreeMixedCell K) => G.Adj u v) hpartition)
    simp only [sup_adj, top_adj] at hadj
    constructor
    · intro h
      apply Ne.symm
      apply hadj.mp
      rcases h with hd | hq | hr
      · exact Or.inl (Or.inr hd)
      · exact Or.inl (Or.inl hq)
      · exact Or.inr hr
    · intro h
      have hall := hadj.mpr h.symm
      rcases hall with (hq | hd) | hr
      · exact Or.inr (Or.inl hq)
      · exact Or.inl hd
      · exact Or.inr (Or.inr hr)
  have hQcard : Q.card = 30 := by
    change ((mixedGridCommonNeighborGraph K C).neighborFinset u).card = 30
    rw [(mixedGridCommonNeighborGraph K C).card_neighborFinset_eq_degree,
      MuThreeMixedGridCode.commonNeighborGraph_degree_eq_thirty H K C code u]
  have hRcard : R.card = 10 := by
    change ((mixedGridRowColumnGraph K).neighborFinset u).card = 10
    rw [(mixedGridRowColumnGraph K).card_neighborFinset_eq_degree,
      MuThreeMixedGridCode.rowColumnGraph_degree_eq_ten H K C code u]
  have htotal : (D ∪ (Q ∪ R)).card = 47 := by
    rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ,
      MuThreeMixedGridCode.card_mixedCell_eq_fortyEight H K C code]
  rw [Finset.card_union_of_disjoint hDQR,
    Finset.card_union_of_disjoint hQR, hQcard, hRcard] at htotal
  rw [← (mixedGridSquareResidualGraph K C).card_neighborFinset_eq_degree]
  change D.card = 7
  omega

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborGraph_eq_conflict
#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborGraph_degree_eq_thirty
#print axioms Erdos85.MuThreeMixedGridCode.occupied_row_card_eq_six
#print axioms Erdos85.MuThreeMixedGridCode.occupied_column_card_eq_six
#print axioms Erdos85.MuThreeMixedGridCode.rowColumnGraph_degree_eq_ten
#print axioms Erdos85.MuThreeMixedGridCode.card_mixedCell_eq_fortyEight
#print axioms Erdos85.MuThreeMixedGridCode.squareResidualGraph_degree_eq_seven
