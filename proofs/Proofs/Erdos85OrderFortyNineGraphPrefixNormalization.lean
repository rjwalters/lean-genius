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

end

end Erdos85
