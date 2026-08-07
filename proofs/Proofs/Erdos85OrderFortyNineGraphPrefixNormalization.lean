import Proofs.Erdos85OrderFortyNinePBDClassification
import Proofs.Erdos85OrderFortyNinePrefixNormalization

/-!
# Graph-facing prefix normalization at order 49

This file transports the abstract nine-point relabeling theorem to the actual
high-vertex supports of an order-49 graph.  It deliberately stops at the
labeling interface: subsequent files may enumerate and order the remaining
one or two triple blocks without reopening the WLOG argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Regard a finset contained in `H` as a finset of the subtype `H`. -/
def finsetInSubtype {α : Type*} [DecidableEq α]
    (H S : Finset α) : Finset {x // x ∈ H} :=
  H.attach.filter fun x => x.1 ∈ S

@[simp] theorem mem_finsetInSubtype_iff
    {α : Type*} [DecidableEq α] {H S : Finset α} {x : {x // x ∈ H}} :
    x ∈ finsetInSubtype H S ↔ x.1 ∈ S := by
  simp [finsetInSubtype]

theorem card_finsetInSubtype_of_subset
    {α : Type*} [DecidableEq α] {H S : Finset α} (hS : S ⊆ H) :
    (finsetInSubtype H S).card = S.card := by
  have hmap :
      (finsetInSubtype H S).map (Function.Embedding.subtype _) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
      simpa [← hyx] using hy
    · intro hx
      exact Finset.mem_map.mpr
        ⟨⟨x, hS hx⟩, by simp [finsetInSubtype, hx], rfl⟩
  calc
    (finsetInSubtype H S).card =
        ((finsetInSubtype H S).map (Function.Embedding.subtype _)).card := by
          simp
    _ = S.card := congrArg Finset.card hmap

theorem inter_finsetInSubtype
    {α : Type*} [DecidableEq α] (H S T : Finset α) :
    finsetInSubtype H S ∩ finsetInSubtype H T =
      finsetInSubtype H (S ∩ T) := by
  ext x
  simp

/-- A finite family of blocks either contains an intersecting distinct pair,
or every distinct pair is disjoint. -/
theorem exists_intersecting_pair_or_pairwise_disjoint
    {α : Type*} [DecidableEq α] (T : Finset (Finset α)) :
    (∃ A ∈ T, ∃ B ∈ T, A ≠ B ∧ (A ∩ B).Nonempty) ∨
      ∀ A ∈ T, ∀ B ∈ T, A ≠ B → (A ∩ B).card = 0 := by
  by_cases h : ∃ A ∈ T, ∃ B ∈ T, A ≠ B ∧ (A ∩ B).Nonempty
  · exact Or.inl h
  · apply Or.inr
    intro A hA B hB hAB
    apply Finset.card_eq_zero.mpr
    exact Finset.not_nonempty_iff_eq_empty.mp fun hne =>
      h ⟨A, hA, B, hB, hAB, hne⟩

/-- Graph-specialized selection dichotomy for the triple-support vertices. -/
theorem orderFortyNine_tripleSupports_intersecting_or_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    let T := (orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3
    (∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧
      ((orderFortyNineHighSupport G x) ∩
        orderFortyNineHighSupport G y).Nonempty) ∨
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ((orderFortyNineHighSupport G x) ∩
        orderFortyNineHighSupport G y).card = 0 := by
  dsimp only
  by_cases h : ∃ x ∈ (orderFortyNineLowVertices G).filter (fun x =>
      (orderFortyNineHighSupport G x).card = 3),
      ∃ y ∈ (orderFortyNineLowVertices G).filter (fun x =>
        (orderFortyNineHighSupport G x).card = 3),
        x ≠ y ∧ ((orderFortyNineHighSupport G x) ∩
          orderFortyNineHighSupport G y).Nonempty
  · exact Or.inl h
  · apply Or.inr
    intro x hx y hy hxy
    apply Finset.card_eq_zero.mpr
    exact Finset.not_nonempty_iff_eq_empty.mp fun hne =>
      h ⟨x, hx, y, hy, hxy, hne⟩

/-- A high support after choosing coordinates on the nine high vertices. -/
def orderFortyNineLabeledHighSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9) (x : V) :
    Finset (Fin 9) :=
  (finsetInSubtype (orderFortyNineHighVertices G)
    (orderFortyNineHighSupport G x)).map e.toEmbedding

theorem card_orderFortyNineLabeledHighSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9) (x : V) :
    (orderFortyNineLabeledHighSupport G e x).card =
      (orderFortyNineHighSupport G x).card := by
  simp only [orderFortyNineLabeledHighSupport, Finset.card_map]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp hv).2

theorem card_inter_orderFortyNineLabeledHighSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9) (x y : V) :
    (orderFortyNineLabeledHighSupport G e x ∩
      orderFortyNineLabeledHighSupport G e y).card =
    ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card := by
  simp only [orderFortyNineLabeledHighSupport, ← Finset.map_inter,
    Finset.card_map, inter_finsetInSubtype]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2

/-- Two size-three high supports in the nine-high stratum can be labeled as
the prefix `012,345` or `012,034`. -/
theorem orderFortyNine_exists_highLabeling_normalizing_two_tripleSupports
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hlin : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card ≤ 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      (finsetInSubtype (orderFortyNineHighVertices G)
          (orderFortyNineHighSupport G x)).map e.toEmbedding = {0, 1, 2} ∧
      ((finsetInSubtype (orderFortyNineHighVertices G)
          (orderFortyNineHighSupport G y)).map e.toEmbedding = {3, 4, 5} ∨
       (finsetInSubtype (orderFortyNineHighVertices G)
          (orderFortyNineHighSupport G y)).map e.toEmbedding = {0, 3, 4}) := by
  let H := orderFortyNineHighVertices G
  let A := finsetInSubtype H (orderFortyNineHighSupport G x)
  let B := finsetInSubtype H (orderFortyNineHighSupport G y)
  have hxsub : orderFortyNineHighSupport G x ⊆ H := by
    intro v hv
    exact (Finset.mem_inter.mp hv).2
  have hysub : orderFortyNineHighSupport G y ⊆ H := by
    intro v hv
    exact (Finset.mem_inter.mp hv).2
  have hA : A.card = 3 := by
    rw [card_finsetInSubtype_of_subset hxsub, hx3]
  have hB : B.card = 3 := by
    rw [card_finsetInSubtype_of_subset hysub, hy3]
  have hAB : (A ∩ B).card ≤ 1 := by
    rw [inter_finsetInSubtype]
    rw [card_finsetInSubtype_of_subset]
    · exact hlin
    · intro v hv
      exact hxsub (Finset.mem_inter.mp hv).1
  have hcardSubtype : Fintype.card {v // v ∈ H} = 9 := by
    simpa using hHigh
  exact Erdos85.OrderFortyNineWitnessTable.exists_labeling_normalizing_two_threeFinsets
    hcardSubtype A B hA hB hAB

/-- Exact graph-facing normalization for two triple supports meeting once. -/
theorem orderFortyNine_exists_highLabeling_normalizing_intersecting_tripleSupports
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hinter : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card = 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      orderFortyNineLabeledHighSupport G e x = {0, 1, 2} ∧
      orderFortyNineLabeledHighSupport G e y = {0, 3, 4} := by
  let H := orderFortyNineHighVertices G
  let A := finsetInSubtype H (orderFortyNineHighSupport G x)
  let B := finsetInSubtype H (orderFortyNineHighSupport G y)
  have hxsub : orderFortyNineHighSupport G x ⊆ H := fun _ hv =>
    (Finset.mem_inter.mp hv).2
  have hysub : orderFortyNineHighSupport G y ⊆ H := fun _ hv =>
    (Finset.mem_inter.mp hv).2
  have hA : A.card = 3 := by rw [card_finsetInSubtype_of_subset hxsub, hx3]
  have hB : B.card = 3 := by rw [card_finsetInSubtype_of_subset hysub, hy3]
  have hAB : (A ∩ B).card = 1 := by
    rw [inter_finsetInSubtype, card_finsetInSubtype_of_subset]
    · exact hinter
    · intro v hv
      exact hxsub (Finset.mem_inter.mp hv).1
  have hcardSubtype : Fintype.card {v // v ∈ H} = 9 := by simpa using hHigh
  simpa [orderFortyNineLabeledHighSupport, H, A, B] using
    (OrderFortyNineWitnessTable.exists_labeling_normalizing_intersecting_threeFinsets
      hcardSubtype A B hA hB hAB)

/-- Exact graph-facing normalization for two disjoint triple supports. -/
theorem orderFortyNine_exists_highLabeling_normalizing_disjoint_tripleSupports
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hinter : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card = 0) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      orderFortyNineLabeledHighSupport G e x = {0, 1, 2} ∧
      orderFortyNineLabeledHighSupport G e y = {3, 4, 5} := by
  let H := orderFortyNineHighVertices G
  let A := finsetInSubtype H (orderFortyNineHighSupport G x)
  let B := finsetInSubtype H (orderFortyNineHighSupport G y)
  have hxsub : orderFortyNineHighSupport G x ⊆ H := fun _ hv =>
    (Finset.mem_inter.mp hv).2
  have hysub : orderFortyNineHighSupport G y ⊆ H := fun _ hv =>
    (Finset.mem_inter.mp hv).2
  have hA : A.card = 3 := by rw [card_finsetInSubtype_of_subset hxsub, hx3]
  have hB : B.card = 3 := by rw [card_finsetInSubtype_of_subset hysub, hy3]
  have hAB : (A ∩ B).card = 0 := by
    rw [inter_finsetInSubtype, card_finsetInSubtype_of_subset]
    · exact hinter
    · intro v hv
      exact hxsub (Finset.mem_inter.mp hv).1
  have hcardSubtype : Fintype.card {v // v ∈ H} = 9 := by simpa using hHigh
  simpa [orderFortyNineLabeledHighSupport, H, A, B] using
    (OrderFortyNineWitnessTable.exists_labeling_normalizing_disjoint_threeFinsets
      hcardSubtype A B hA hB hAB)

/-- Whenever the nine-high profile contains at least two triple blocks, choose
two distinct witnessing low vertices and normalize their supports. -/
theorem orderFortyNine_exists_normalized_two_tripleSupports_of_count_ge_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : 2 ≤ orderFortyNineHighIncidenceCount G 3) :
    ∃ x y : V,
      x ≠ y ∧
      (orderFortyNineHighSupport G x).card = 3 ∧
      (orderFortyNineHighSupport G y).card = 3 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        (finsetInSubtype (orderFortyNineHighVertices G)
            (orderFortyNineHighSupport G x)).map e.toEmbedding = {0, 1, 2} ∧
        ((finsetInSubtype (orderFortyNineHighVertices G)
            (orderFortyNineHighSupport G y)).map e.toEmbedding = {3, 4, 5} ∨
         (finsetInSubtype (orderFortyNineHighVertices G)
            (orderFortyNineHighSupport G y)).map e.toEmbedding = {0, 3, 4}) := by
  let T := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3
  have hTcard : T.card = orderFortyNineHighIncidenceCount G 3 := by
    rfl
  have hTone : 1 < T.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hTone
  have hx3 : (orderFortyNineHighSupport G x).card = 3 :=
    (Finset.mem_filter.mp hx).2
  have hy3 : (orderFortyNineHighSupport G y).card = 3 :=
    (Finset.mem_filter.mp hy).2
  have hlin := orderFortyNine_card_inter_highSupport_le_one G hfree hxy
  obtain ⟨e, he1, he2⟩ :=
    orderFortyNine_exists_highLabeling_normalizing_two_tripleSupports
      G hHigh hx3 hy3 hlin
  exact ⟨x, y, hxy, hx3, hy3, e, he1, he2⟩

/-- L1 for the two-triple profile: the complete graph-derived triple system
is represented by a row of the verified `tableT2`. -/
theorem orderFortyNine_exists_tableT2_row_of_tripleSupportCount_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ x y : V,
      let T := (orderFortyNineLowVertices G).filter fun z =>
        (orderFortyNineHighSupport G z).card = 3
      T = {x, y} ∧ x ≠ y ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        ∃ row ∈ OrderFortyNineWitnessTable.tableT2,
          row.1 =
            [OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e x),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e y)] := by
  let T := (orderFortyNineLowVertices G).filter fun z =>
    (orderFortyNineHighSupport G z).card = 3
  have hTcard : T.card = 2 := by
    change orderFortyNineHighIncidenceCount G 3 = 2
    exact hcount
  obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp hTcard
  have hx : x ∈ T := by rw [hT]; simp
  have hy : y ∈ T := by rw [hT]; simp
  have hx3 : (orderFortyNineHighSupport G x).card = 3 :=
    (Finset.mem_filter.mp hx).2
  have hy3 : (orderFortyNineHighSupport G y).card = 3 :=
    (Finset.mem_filter.mp hy).2
  have hlin := orderFortyNine_card_inter_highSupport_le_one G hfree hxy
  obtain ⟨e, he1, he2⟩ :=
    orderFortyNine_exists_highLabeling_normalizing_two_tripleSupports
      G hHigh hx3 hy3 hlin
  let A := orderFortyNineLabeledHighSupport G e x
  let B := orderFortyNineLabeledHighSupport G e y
  have hA : A = {0, 1, 2} := he1
  have hBmem : OrderFortyNineWitnessTable.tripleDigits B ∈
      OrderFortyNineWitnessTable.secondTriples := by
    rcases he2 with he2 | he2
    · have hB : B = {3, 4, 5} := he2
      rw [hB]
      simp [OrderFortyNineWitnessTable.secondTriples]
    · have hB : B = {0, 3, 4} := he2
      rw [hB]
      simp [OrderFortyNineWitnessTable.secondTriples]
  have hraw :
      [OrderFortyNineWitnessTable.firstTriple,
        OrderFortyNineWitnessTable.tripleDigits B] ∈
        OrderFortyNineWitnessTable.rawT2 :=
    OrderFortyNineWitnessTable.mem_rawT2_iff.mpr hBmem
  have hraw' :
      [OrderFortyNineWitnessTable.tripleDigits A,
        OrderFortyNineWitnessTable.tripleDigits B] ∈
        OrderFortyNineWitnessTable.rawT2 := by
    simpa [hA, OrderFortyNineWitnessTable.firstTriple] using hraw
  obtain ⟨row, hrow, hroweq⟩ :=
    OrderFortyNineWitnessTable.exists_tableT2_row_of_mem_rawT2 hraw'
  exact ⟨x, y, hT, hxy, e, row, hrow, hroweq⟩

/-- Three specified graph blocks, with an intersecting first pair, produce a
verified `tableT3` row in that order. -/
theorem orderFortyNine_exists_tableT3_row_of_intersecting_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y z : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hz3 : (orderFortyNineHighSupport G z).card = 3)
    (hxy : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card = 1)
    (hxz : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G z).card ≤ 1)
    (hyz : ((orderFortyNineHighSupport G y) ∩
      orderFortyNineHighSupport G z).card ≤ 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ row ∈ OrderFortyNineWitnessTable.tableT3,
        row.1 =
          [OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e x),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e y),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e z)] := by
  obtain ⟨e, hA, hB⟩ :=
    orderFortyNine_exists_highLabeling_normalizing_intersecting_tripleSupports
      G hHigh hx3 hy3 hxy
  let R := orderFortyNineLabeledHighSupport G e z
  have hR : R.card = 3 := by
    rw [card_orderFortyNineLabeledHighSupport, hz3]
  have hR1 : (({0, 1, 2} : Finset (Fin 9)) ∩ R).card ≤ 1 := by
    rw [← hA]
    rw [card_inter_orderFortyNineLabeledHighSupport]
    exact hxz
  have hR2 : (({0, 3, 4} : Finset (Fin 9)) ∩ R).card ≤ 1 := by
    rw [← hB]
    rw [card_inter_orderFortyNineLabeledHighSupport]
    exact hyz
  have hRne1 : R ≠ {0, 1, 2} := by
    intro h
    rw [h] at hR1
    have hc : (({0, 1, 2} : Finset (Fin 9)) ∩ {0, 1, 2}).card = 3 := by
      native_decide
    omega
  have hRne2 : R ≠ {0, 3, 4} := by
    intro h
    rw [h] at hR2
    have hc : (({0, 3, 4} : Finset (Fin 9)) ∩ {0, 3, 4}).card = 3 := by
      native_decide
    omega
  have hraw := OrderFortyNineWitnessTable.mem_rawT3_of_intersectingPrefix
    hR hR1 hR2 hRne1 hRne2
  have hraw' :
      [OrderFortyNineWitnessTable.tripleDigits
          (orderFortyNineLabeledHighSupport G e x),
       OrderFortyNineWitnessTable.tripleDigits
          (orderFortyNineLabeledHighSupport G e y),
       OrderFortyNineWitnessTable.tripleDigits R] ∈
        OrderFortyNineWitnessTable.rawT3 := by
    simpa [hA, hB, OrderFortyNineWitnessTable.firstTriple] using hraw
  obtain ⟨row, hrow, hroweq⟩ :=
    OrderFortyNineWitnessTable.exists_tableT3_row_of_mem_rawT3 hraw'
  exact ⟨e, row, hrow, hroweq⟩

/-- Three pairwise-disjoint graph blocks produce a verified `tableT3` row. -/
theorem orderFortyNine_exists_tableT3_row_of_disjoint_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y z : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hz3 : (orderFortyNineHighSupport G z).card = 3)
    (hxy : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card = 0)
    (hxz : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G z).card = 0)
    (hyz : ((orderFortyNineHighSupport G y) ∩
      orderFortyNineHighSupport G z).card = 0) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ row ∈ OrderFortyNineWitnessTable.tableT3,
        row.1 =
          [OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e x),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e y),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e z)] := by
  obtain ⟨e, hA, hB⟩ :=
    orderFortyNine_exists_highLabeling_normalizing_disjoint_tripleSupports
      G hHigh hx3 hy3 hxy
  let R := orderFortyNineLabeledHighSupport G e z
  have hR : R.card = 3 := by
    rw [card_orderFortyNineLabeledHighSupport, hz3]
  have hR1 : (({0, 1, 2} : Finset (Fin 9)) ∩ R).card = 0 := by
    rw [← hA, card_inter_orderFortyNineLabeledHighSupport]
    exact hxz
  have hR2 : (({3, 4, 5} : Finset (Fin 9)) ∩ R).card = 0 := by
    rw [← hB, card_inter_orderFortyNineLabeledHighSupport]
    exact hyz
  have hraw := OrderFortyNineWitnessTable.mem_rawT3_of_disjointPrefix
    hR hR1 hR2
  have hraw' :
      [OrderFortyNineWitnessTable.tripleDigits
          (orderFortyNineLabeledHighSupport G e x),
       OrderFortyNineWitnessTable.tripleDigits
          (orderFortyNineLabeledHighSupport G e y),
       OrderFortyNineWitnessTable.tripleDigits R] ∈
        OrderFortyNineWitnessTable.rawT3 := by
    simpa [hA, hB, OrderFortyNineWitnessTable.firstTriple] using hraw
  obtain ⟨row, hrow, hroweq⟩ :=
    OrderFortyNineWitnessTable.exists_tableT3_row_of_mem_rawT3 hraw'
  exact ⟨e, row, hrow, hroweq⟩

/-- L1 for the three-triple profile: after choosing an intersecting pair when
one exists (and otherwise using the disjoint prefix), the complete graph
triple system is represented by a verified `tableT3` row. -/
theorem orderFortyNine_exists_tableT3_row_of_tripleSupportCount_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ x y z : V,
      let T := (orderFortyNineLowVertices G).filter fun w =>
        (orderFortyNineHighSupport G w).card = 3
      T = {x, y, z} ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        ∃ row ∈ OrderFortyNineWitnessTable.tableT3,
          row.1 =
            [OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e x),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e y),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e z)] := by
  let T := (orderFortyNineLowVertices G).filter fun w =>
    (orderFortyNineHighSupport G w).card = 3
  have hTcard : T.card = 3 := by
    change orderFortyNineHighIncidenceCount G 3 = 3
    exact hcount
  obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := Finset.card_eq_three.mp hTcard
  have ha : a ∈ T := by rw [hT]; simp
  have hb : b ∈ T := by rw [hT]; simp
  have hc : c ∈ T := by rw [hT]; simp
  have ha3 : (orderFortyNineHighSupport G a).card = 3 :=
    (Finset.mem_filter.mp ha).2
  have hb3 : (orderFortyNineHighSupport G b).card = 3 :=
    (Finset.mem_filter.mp hb).2
  have hc3 : (orderFortyNineHighSupport G c).card = 3 :=
    (Finset.mem_filter.mp hc).2
  have habLe := orderFortyNine_card_inter_highSupport_le_one G hfree hab
  have hacLe := orderFortyNine_card_inter_highSupport_le_one G hfree hac
  have hbcLe := orderFortyNine_card_inter_highSupport_le_one G hfree hbc
  have habCases :
      ((orderFortyNineHighSupport G a) ∩
        orderFortyNineHighSupport G b).card = 0 ∨
      ((orderFortyNineHighSupport G a) ∩
        orderFortyNineHighSupport G b).card = 1 := by omega
  rcases habCases with hab0 | hab1
  · have hacCases :
        ((orderFortyNineHighSupport G a) ∩
          orderFortyNineHighSupport G c).card = 0 ∨
        ((orderFortyNineHighSupport G a) ∩
          orderFortyNineHighSupport G c).card = 1 := by omega
    rcases hacCases with hac0 | hac1
    · have hbcCases :
          ((orderFortyNineHighSupport G b) ∩
            orderFortyNineHighSupport G c).card = 0 ∨
          ((orderFortyNineHighSupport G b) ∩
            orderFortyNineHighSupport G c).card = 1 := by omega
      rcases hbcCases with hbc0 | hbc1
      · obtain ⟨e, row, hrow, hroweq⟩ :=
          orderFortyNine_exists_tableT3_row_of_disjoint_prefix
            G hHigh ha3 hb3 hc3 hab0 hac0 hbc0
        exact ⟨a, b, c, hT, e, row, hrow, hroweq⟩
      · obtain ⟨e, row, hrow, hroweq⟩ :=
          orderFortyNine_exists_tableT3_row_of_intersecting_prefix
            G hHigh hb3 hc3 ha3 hbc1 (by
              simpa [Finset.inter_comm] using habLe) (by
              simpa [Finset.inter_comm] using hacLe)
        refine ⟨b, c, a, ?_, e, row, hrow, hroweq⟩
        change T = {b, c, a}
        rw [hT]
        ext v
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
    · obtain ⟨e, row, hrow, hroweq⟩ :=
        orderFortyNine_exists_tableT3_row_of_intersecting_prefix
          G hHigh ha3 hc3 hb3 hac1 habLe (by
            simpa [Finset.inter_comm] using hbcLe)
      refine ⟨a, c, b, ?_, e, row, hrow, hroweq⟩
      change T = {a, c, b}
      rw [hT]
      ext v
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  · obtain ⟨e, row, hrow, hroweq⟩ :=
      orderFortyNine_exists_tableT3_row_of_intersecting_prefix
        G hHigh ha3 hb3 hc3 hab1 hacLe hbcLe
    exact ⟨a, b, c, hT, e, row, hrow, hroweq⟩

/-- Four specified graph blocks, with an intersecting first pair, produce a
verified `tableT4` row; the two residual blocks are ordered automatically. -/
theorem orderFortyNine_exists_tableT4_row_of_intersecting_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {x y z w : V}
    (hx3 : (orderFortyNineHighSupport G x).card = 3)
    (hy3 : (orderFortyNineHighSupport G y).card = 3)
    (hz3 : (orderFortyNineHighSupport G z).card = 3)
    (hw3 : (orderFortyNineHighSupport G w).card = 3)
    (hxy : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card = 1)
    (hxz : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G z).card ≤ 1)
    (hyz : ((orderFortyNineHighSupport G y) ∩
      orderFortyNineHighSupport G z).card ≤ 1)
    (hxw : ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G w).card ≤ 1)
    (hyw : ((orderFortyNineHighSupport G y) ∩
      orderFortyNineHighSupport G w).card ≤ 1)
    (hzw : ((orderFortyNineHighSupport G z) ∩
      orderFortyNineHighSupport G w).card ≤ 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ row ∈ OrderFortyNineWitnessTable.tableT4,
        (row.1 =
          [OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e x),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e y),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e z),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e w)] ∨
         row.1 =
          [OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e x),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e y),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e w),
           OrderFortyNineWitnessTable.tripleDigits
              (orderFortyNineLabeledHighSupport G e z)]) := by
  obtain ⟨e, hA, hB⟩ :=
    orderFortyNine_exists_highLabeling_normalizing_intersecting_tripleSupports
      G hHigh hx3 hy3 hxy
  let R := orderFortyNineLabeledHighSupport G e z
  let S := orderFortyNineLabeledHighSupport G e w
  have hR : R.card = 3 := by rw [card_orderFortyNineLabeledHighSupport, hz3]
  have hS : S.card = 3 := by rw [card_orderFortyNineLabeledHighSupport, hw3]
  have hR1 : (({0, 1, 2} : Finset (Fin 9)) ∩ R).card ≤ 1 := by
    rw [← hA, card_inter_orderFortyNineLabeledHighSupport]
    exact hxz
  have hR2 : (({0, 3, 4} : Finset (Fin 9)) ∩ R).card ≤ 1 := by
    rw [← hB, card_inter_orderFortyNineLabeledHighSupport]
    exact hyz
  have hS1 : (({0, 1, 2} : Finset (Fin 9)) ∩ S).card ≤ 1 := by
    rw [← hA, card_inter_orderFortyNineLabeledHighSupport]
    exact hxw
  have hS2 : (({0, 3, 4} : Finset (Fin 9)) ∩ S).card ≤ 1 := by
    rw [← hB, card_inter_orderFortyNineLabeledHighSupport]
    exact hyw
  have hRS : (R ∩ S).card ≤ 1 := by
    rw [card_inter_orderFortyNineLabeledHighSupport]
    exact hzw
  have hRne1 : R ≠ {0, 1, 2} := by
    intro h
    rw [h] at hR1
    have hc : (({0, 1, 2} : Finset (Fin 9)) ∩ {0, 1, 2}).card = 3 := by
      native_decide
    omega
  have hRne2 : R ≠ {0, 3, 4} := by
    intro h
    rw [h] at hR2
    have hc : (({0, 3, 4} : Finset (Fin 9)) ∩ {0, 3, 4}).card = 3 := by
      native_decide
    omega
  have hSne1 : S ≠ {0, 1, 2} := by
    intro h
    rw [h] at hS1
    have hc : (({0, 1, 2} : Finset (Fin 9)) ∩ {0, 1, 2}).card = 3 := by
      native_decide
    omega
  have hSne2 : S ≠ {0, 3, 4} := by
    intro h
    rw [h] at hS2
    have hc : (({0, 3, 4} : Finset (Fin 9)) ∩ {0, 3, 4}).card = 3 := by
      native_decide
    omega
  have hRneS : R ≠ S := by
    intro h
    rw [h, Finset.inter_self, hS] at hRS
    omega
  rcases OrderFortyNineWitnessTable.mem_rawT4_of_intersectingPrefix
      hR hS hR1 hR2 hS1 hS2 hRS hRne1 hRne2 hSne1 hSne2 hRneS with
    hraw | hraw
  · have hraw' :
        [OrderFortyNineWitnessTable.tripleDigits
            (orderFortyNineLabeledHighSupport G e x),
         OrderFortyNineWitnessTable.tripleDigits
            (orderFortyNineLabeledHighSupport G e y),
         OrderFortyNineWitnessTable.tripleDigits R,
         OrderFortyNineWitnessTable.tripleDigits S] ∈
          OrderFortyNineWitnessTable.rawT4 := by
      simpa [hA, hB, OrderFortyNineWitnessTable.firstTriple] using hraw
    obtain ⟨row, hrow, hroweq⟩ :=
      OrderFortyNineWitnessTable.exists_tableT4_row_of_mem_rawT4 hraw'
    exact ⟨e, row, hrow, Or.inl hroweq⟩
  · have hraw' :
        [OrderFortyNineWitnessTable.tripleDigits
            (orderFortyNineLabeledHighSupport G e x),
         OrderFortyNineWitnessTable.tripleDigits
            (orderFortyNineLabeledHighSupport G e y),
         OrderFortyNineWitnessTable.tripleDigits S,
         OrderFortyNineWitnessTable.tripleDigits R] ∈
          OrderFortyNineWitnessTable.rawT4 := by
      simpa [hA, hB, OrderFortyNineWitnessTable.firstTriple] using hraw
    obtain ⟨row, hrow, hroweq⟩ :=
      OrderFortyNineWitnessTable.exists_tableT4_row_of_mem_rawT4 hraw'
    exact ⟨e, row, hrow, Or.inr hroweq⟩

/-- L1 for the four-triple profile: four disjoint triples cannot fit on the
nine high vertices, so an intersecting pair exists and the complete system is
represented by a verified `tableT4` row. -/
theorem orderFortyNine_exists_tableT4_row_of_tripleSupportCount_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ x y z w : V,
      let T := (orderFortyNineLowVertices G).filter fun u =>
        (orderFortyNineHighSupport G u).card = 3
      T = {x, y, z, w} ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        ∃ row ∈ OrderFortyNineWitnessTable.tableT4,
          (row.1 =
            [OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e x),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e y),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e z),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e w)] ∨
           row.1 =
            [OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e x),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e y),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e w),
             OrderFortyNineWitnessTable.tripleDigits
                (orderFortyNineLabeledHighSupport G e z)]) := by
  let T := (orderFortyNineLowVertices G).filter fun u =>
    (orderFortyNineHighSupport G u).card = 3
  have hTcard : T.card = 4 := by
    change orderFortyNineHighIncidenceCount G 3 = 4
    exact hcount
  rcases orderFortyNine_tripleSupports_intersecting_or_pairwise_disjoint G with
    hinter | hdisjoint
  · obtain ⟨x, hx, y, hy, hxy, hnonempty⟩ := hinter
    have hxT : x ∈ T := hx
    have hyT : y ∈ T := hy
    have hx3 : (orderFortyNineHighSupport G x).card = 3 :=
      (Finset.mem_filter.mp hxT).2
    have hy3 : (orderFortyNineHighSupport G y).card = 3 :=
      (Finset.mem_filter.mp hyT).2
    have hxyLe := orderFortyNine_card_inter_highSupport_le_one G hfree hxy
    have hxy1 : ((orderFortyNineHighSupport G x) ∩
        orderFortyNineHighSupport G y).card = 1 := by
      have hpos := Finset.card_pos.mpr hnonempty
      omega
    have hpairSub : ({x, y} : Finset V) ⊆ T := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hxT
      · exact hyT
    have hrestCard : (T \ {x, y}).card = 2 := by
      rw [Finset.card_sdiff_of_subset hpairSub, hTcard]
      simp [hxy]
    obtain ⟨z, w, hzw, hrest⟩ := Finset.card_eq_two.mp hrestCard
    have hzRest : z ∈ T \ {x, y} := by rw [hrest]; simp
    have hwRest : w ∈ T \ {x, y} := by rw [hrest]; simp
    have hzT := (Finset.mem_sdiff.mp hzRest).1
    have hwT := (Finset.mem_sdiff.mp hwRest).1
    have hz3 : (orderFortyNineHighSupport G z).card = 3 :=
      (Finset.mem_filter.mp hzT).2
    have hw3 : (orderFortyNineHighSupport G w).card = 3 :=
      (Finset.mem_filter.mp hwT).2
    have hzx : z ≠ x := by
      intro h
      exact (Finset.mem_sdiff.mp hzRest).2 (by simp [h])
    have hzy : z ≠ y := by
      intro h
      exact (Finset.mem_sdiff.mp hzRest).2 (by simp [h])
    have hwx : w ≠ x := by
      intro h
      exact (Finset.mem_sdiff.mp hwRest).2 (by simp [h])
    have hwy : w ≠ y := by
      intro h
      exact (Finset.mem_sdiff.mp hwRest).2 (by simp [h])
    have hxz := orderFortyNine_card_inter_highSupport_le_one G hfree hzx.symm
    have hyz := orderFortyNine_card_inter_highSupport_le_one G hfree hzy.symm
    have hxw := orderFortyNine_card_inter_highSupport_le_one G hfree hwx.symm
    have hyw := orderFortyNine_card_inter_highSupport_le_one G hfree hwy.symm
    have hzwLin := orderFortyNine_card_inter_highSupport_le_one G hfree hzw
    obtain ⟨e, row, hrow, hroweq⟩ :=
      orderFortyNine_exists_tableT4_row_of_intersecting_prefix
        G hHigh hx3 hy3 hz3 hw3 hxy1 hxz hyz hxw hyw hzwLin
    refine ⟨x, y, z, w, ?_, e, row, hrow, hroweq⟩
    change T = {x, y, z, w}
    have hunion := Finset.sdiff_union_of_subset hpairSub
    rw [hrest] at hunion
    rw [← hunion]
    ext u
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hT⟩ :=
      Finset.card_eq_four.mp hTcard
    have ha : a ∈ T := by rw [hT]; simp
    have hb : b ∈ T := by rw [hT]; simp
    have hc : c ∈ T := by rw [hT]; simp
    have hd : d ∈ T := by rw [hT]; simp
    let A := orderFortyNineHighSupport G a
    let B := orderFortyNineHighSupport G b
    let C := orderFortyNineHighSupport G c
    let D := orderFortyNineHighSupport G d
    have hA : A.card = 3 := (Finset.mem_filter.mp ha).2
    have hB : B.card = 3 := (Finset.mem_filter.mp hb).2
    have hC : C.card = 3 := (Finset.mem_filter.mp hc).2
    have hD : D.card = 3 := (Finset.mem_filter.mp hd).2
    have hAB0 := hdisjoint a ha b hb hab
    have hAC0 := hdisjoint a ha c hc hac
    have hAD0 := hdisjoint a ha d hd had
    have hBC0 := hdisjoint b hb c hc hbc
    have hBD0 := hdisjoint b hb d hd hbd
    have hCD0 := hdisjoint c hc d hd hcd
    have hAB : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.card_eq_zero.mp hAB0)
    have hABC : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]
      intro u hu huc
      rcases Finset.mem_union.mp hu with hua | hub
      · have : u ∈ A ∩ C := Finset.mem_inter.mpr ⟨hua, huc⟩
        have hempty : A ∩ C = ∅ := Finset.card_eq_zero.mp hAC0
        rw [hempty] at this
        simpa using this
      · have : u ∈ B ∩ C := Finset.mem_inter.mpr ⟨hub, huc⟩
        have hempty : B ∩ C = ∅ := Finset.card_eq_zero.mp hBC0
        rw [hempty] at this
        simpa using this
    have hABCD : Disjoint (A ∪ B ∪ C) D := by
      rw [Finset.disjoint_left]
      intro u hu hud
      rcases Finset.mem_union.mp hu with huab | huc
      · rcases Finset.mem_union.mp huab with hua | hub
        · have : u ∈ A ∩ D := Finset.mem_inter.mpr ⟨hua, hud⟩
          have hempty : A ∩ D = ∅ := Finset.card_eq_zero.mp hAD0
          rw [hempty] at this
          simpa using this
        · have : u ∈ B ∩ D := Finset.mem_inter.mpr ⟨hub, hud⟩
          have hempty : B ∩ D = ∅ := Finset.card_eq_zero.mp hBD0
          rw [hempty] at this
          simpa using this
      · have : u ∈ C ∩ D := Finset.mem_inter.mpr ⟨huc, hud⟩
        have hempty : C ∩ D = ∅ := Finset.card_eq_zero.mp hCD0
        rw [hempty] at this
        simpa using this
    have hUnionCard : (A ∪ B ∪ C ∪ D).card = 12 := by
      rw [Finset.card_union_of_disjoint hABCD,
        Finset.card_union_of_disjoint hABC,
        Finset.card_union_of_disjoint hAB, hA, hB, hC, hD]
    have hUnionSub : A ∪ B ∪ C ∪ D ⊆ orderFortyNineHighVertices G := by
      intro u hu
      simp only [Finset.mem_union] at hu
      rcases hu with ((huA | huB) | huC) | huD
      · exact (Finset.mem_inter.mp huA).2
      · exact (Finset.mem_inter.mp huB).2
      · exact (Finset.mem_inter.mp huC).2
      · exact (Finset.mem_inter.mp huD).2
    have := Finset.card_le_card hUnionSub
    rw [hUnionCard, hHigh] at this
    omega

end

end Erdos85
