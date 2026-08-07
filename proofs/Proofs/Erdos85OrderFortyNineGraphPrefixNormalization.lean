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

end

end Erdos85
