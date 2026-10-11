import Proofs.Erdos85H3TripleCompletionEngine
import Proofs.Erdos85OrderFortyNineBitRelabel
import Proofs.Erdos85OrderFortyNineThreeHighOneFiber

/-!
# Bridge from the order-49 Boolean constraints to the triple-cell engine

The canonical `t = 1` three-high representative masks give exactly the
labelling fixed in `Erdos85H3TripleCompletionEngine`.  Every edge vector satisfying the
order-49 Boolean constraints for those masks is a `Model` compatible with
the initial partial graph `s0` (the high–low edges).  Consequently a `true`
result of the engine search on `s0` excludes the canonical representative,
and hence the whole `(h, t) = (3, 1)` cell.

No finite search is run in this file.
-/

namespace Erdos85
namespace H3TripleCompletion

open OrderFortyNineSmallHighCensus

def hi (w : Fin 3) : V := ⟨w.val, by omega⟩

theorem s0_adj (a b : V) : s0.adj a b = (initRow a).testBit b.val := by
  unfold St.adj s0
  simp only [Vector.getElem_ofFn]

theorem s0_nbr (a : V) :
    s0.nbr[a.val] = (List.finRange 49).filter fun b => (initRow a).testBit b.val := by
  unfold s0
  simp only [Vector.getElem_ofFn]

theorem initRow_symm : ∀ a b : V,
    (initRow a).testBit b.val = (initRow b).testBit a.val := by
  decide +kernel

theorem initRow_edges : ∀ a b : V, (initRow a).testBit b.val = true →
    (∃ w : Fin 3, b = hi w ∧ col a w = true) ∨
      (∃ w : Fin 3, a = hi w ∧ col b w = true) := by
  decide +kernel

theorem s0_wf : s0.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rw [s0_adj, s0_adj]
    exact initRow_symm a b
  · intro a
    rw [s0_nbr]
    exact (List.nodup_finRange 49).filter _
  · intro a b
    rw [s0_nbr, s0_adj, List.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨List.mem_finRange b, h⟩

theorem mask_col : ∀ (k : V) (w : Fin 3),
    (orderFortyNineSupportMask (threeHighRepresentativeMasks 1) k).getLsbD w.val =
      col k w := by
  decide +kernel

/-- The relation-level order-49 constraints for the canonical `t = 1`
three-high masks give an engine model compatible with `s0`. -/
theorem model_of_constraints {adj : V → V → Bool}
    (hsymm : ∀ a b, adj a b = adj b a) (hirr : ∀ a, adj a a = false)
    (h : orderFortyNineRelationConstraints 3 (threeHighRepresentativeMasks 1) adj) :
    Model adj ∧ Compat s0 adj := by
  obtain ⟨_, _, hdeg, hc4, hsup, hpart⟩ := h
  refine ⟨⟨hsymm, hirr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j k l hij hkl h1 h2 h3 h4
    have hcard := hc4 i j hij
    have hk : k ∈ Finset.univ.filter (fun k => adj i k && adj j k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, by rw [h1, h2]; rfl⟩
    have hl : l ∈ Finset.univ.filter (fun k => adj i k && adj j k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, by rw [h3, h4]; rfl⟩
    exact hkl (Finset.card_le_one.mp hcard k hk l hl)
  · intro i hi3 w
    have hcard := hpart i hi3 ⟨w.val, by omega⟩ w.isLt
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hmem := Finset.mem_singleton_self k
    rw [← hk] at hmem
    have hmem' := (Finset.mem_filter.mp hmem).2
    simp only [Bool.and_eq_true] at hmem'
    exact ⟨k, hmem'.1, (mask_col k w).symm.trans hmem'.2⟩
  · intro i hi3 w k l hk hkw hl hlw
    have hcard := hpart i hi3 ⟨w.val, by omega⟩ w.isLt
    have hk' : k ∈ Finset.univ.filter (fun k => adj i k &&
        (orderFortyNineSupportMask (threeHighRepresentativeMasks 1) k).getLsbD
          (⟨w.val, by omega⟩ : Fin 9).val) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hk, (mask_col k w).trans hkw⟩
    have hl' : l ∈ Finset.univ.filter (fun k => adj i k &&
        (orderFortyNineSupportMask (threeHighRepresentativeMasks 1) k).getLsbD
          (⟨w.val, by omega⟩ : Fin 9).val) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hl, (mask_col l w).trans hlw⟩
    exact Finset.card_le_one.mp (le_of_eq hcard) k hk' l hl'
  · intro i
    refine ⟨(Finset.univ.filter fun j => adj i j).toList, Finset.nodup_toList _, ?_, ?_⟩
    · rw [Finset.length_toList, hdeg i]
      rfl
    · intro j
      rw [Finset.mem_toList, Finset.mem_filter]
      constructor
      · intro hj
        exact hj.2
      · intro hj
        exact ⟨Finset.mem_univ j, hj⟩
  · intro a b hab
    rw [s0_adj] at hab
    rcases initRow_edges a b hab with ⟨w, hb, hw⟩ | ⟨w, ha, hw⟩
    · rw [hb]
      have := hsup a ⟨w.val, by omega⟩ w.isLt
      exact this.trans ((mask_col a w).trans hw)
    · rw [ha, hsymm]
      have := hsup b ⟨w.val, by omega⟩ w.isLt
      exact this.trans ((mask_col b w).trans hw)

/-- Fuel selected for the triple-cell search; success remains a premise. -/
def tripleSearch : Bool := search 70 30 40 s0

/-- A successful engine search excludes the canonical `t = 1` three-high
representative. -/
theorem threeHighCanonicalRepresentativeExcluded_one_of_tripleSearch
    (h : tripleSearch = true) : ThreeHighCanonicalRepresentativeExcluded 1 := by
  intro edges hc
  obtain ⟨M, hcompat⟩ := model_of_constraints (adj := orderFortyNineBitAdj edges)
    (orderFortyNineBitAdj_comm edges)
    (fun a => by simp [orderFortyNineBitAdj]) hc
  exact search_sound 70 30 40 s0 s0_wf h _ M hcompat

/-- A successful engine search excludes the `(h, t) = (3, 1)` cell. -/
theorem orderFortyNineTripleCellExcluded_three_one_of_tripleSearch
    (h : tripleSearch = true) : OrderFortyNineTripleCellExcluded 3 1 :=
  orderFortyNineTripleCellExcluded_three_of_canonical
    threeHighCanonicalGraphCover_one
    (threeHighCanonicalRepresentativeExcluded_one_of_tripleSearch h)

end H3TripleCompletion
end Erdos85

#print axioms Erdos85.H3TripleCompletion.threeHighCanonicalRepresentativeExcluded_one_of_tripleSearch
#print axioms Erdos85.H3TripleCompletion.orderFortyNineTripleCellExcluded_three_one_of_tripleSearch
