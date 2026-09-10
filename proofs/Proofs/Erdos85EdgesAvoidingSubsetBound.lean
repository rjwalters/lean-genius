import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

/-! Edges avoiding U use pairs from the complement of U. -/
namespace Erdos85
open SimpleGraph

theorem edges_avoiding_subset_card_le_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    (G.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)).card ≤
      (Fintype.card V - U.card).choose 2 := by
  classical
  let A := G.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)
  have hinj : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
    intro e f h
    apply Sym2.ext
    intro v
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]
  have hsub : A.image Sym2.toFinset ⊆ (Finset.univ \ U).powersetCard 2 := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    have hp := Finset.mem_filter.mp he
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun hu => hp.2 v hu (Sym2.mem_toFinset.mp hv)⟩
    · exact G.card_toFinset_mem_edgeFinset ⟨e, hp.1⟩
  calc
    A.card = (A.image Sym2.toFinset).card :=
      (Finset.card_image_of_injective A hinj).symm
    _ ≤ ((Finset.univ \ U).powersetCard 2).card := Finset.card_le_card hsub
    _ = (Fintype.card V - U.card).choose 2 := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ U)]
      simp

end Erdos85
#print axioms Erdos85.edges_avoiding_subset_card_le_choose
