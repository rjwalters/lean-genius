import Proofs.Erdos85H5Engine
import Proofs.Erdos85OrderFortyNineBitRelabel
import Proofs.Erdos85OrderFortyNineSmallHighCanonicalCapstone

/-!
# Bridge from the order-49 Boolean constraints to the five-high engine

For each `c = 0, 1, 2` the canonical five-high representative masks
`fiveHighRepresentativeMasks c` give exactly the labelling fixed in
`Erdos85H5Engine`.  Every edge vector satisfying the order-49 Boolean
constraints for those masks is a `Model c` compatible with the initial
partial graph `s0 c` (the high–low edges).  Consequently, if all parts of a
split search from `s0 c` return `true`, the canonical representative `c` is
excluded.

No finite search is run in this file.
-/

namespace Erdos85
namespace H5

open H3Pair (V St Compat)
open OrderFortyNineSmallHighCensus

def hi (w : Fin 5) : V := ⟨w.val, by omega⟩

/-- Initial bit row: a high vertex sees its colour fibre, a low vertex sees
the high vertices in its mask. -/
def initRow (c : Fin 3) (a : V) : Nat :=
  if h : a.val < 5 then fiberMask c ⟨a.val, h⟩ else maskOf c a

/-- The initial partial graph: exactly the high–low edges. -/
def s0 (c : Fin 3) : St where
  rows := Vector.ofFn (initRow c)
  nbr := Vector.ofFn fun a => (List.finRange 49).filter fun b => (initRow c a).testBit b.val

theorem s0_adj (c : Fin 3) (a b : V) : (s0 c).adj a b = (initRow c a).testBit b.val := by
  unfold H3Pair.St.adj s0
  simp only [Vector.getElem_ofFn]

theorem s0_nbr (c : Fin 3) (a : V) :
    (s0 c).nbr[a.val] = (List.finRange 49).filter fun b => (initRow c a).testBit b.val := by
  unfold s0
  simp only [Vector.getElem_ofFn]

theorem initRow_symm : ∀ (c : Fin 3) (a b : V),
    (initRow c a).testBit b.val = (initRow c b).testBit a.val := by
  decide +kernel

theorem initRow_edges : ∀ (c : Fin 3) (a b : V), (initRow c a).testBit b.val = true →
    (∃ w : Fin 5, b = hi w ∧ col c a w = true) ∨
      (∃ w : Fin 5, a = hi w ∧ col c b w = true) := by
  decide +kernel

theorem s0_wf (c : Fin 3) : (s0 c).WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rw [s0_adj, s0_adj]
    exact initRow_symm c a b
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

theorem mask_col : ∀ (c : Fin 3) (k : V) (w : Fin 5),
    (orderFortyNineSupportMask (fiveHighRepresentativeMasks c.val) k).getLsbD w.val =
      col c k w := by
  decide +kernel

/-- The relation-level order-49 constraints for the canonical five-high
masks give an engine model compatible with `s0 c`. -/
theorem model_of_constraints (c : Fin 3) {adj : V → V → Bool}
    (hsymm : ∀ a b, adj a b = adj b a) (hirr : ∀ a, adj a a = false)
    (h : orderFortyNineRelationConstraints 5 (fiveHighRepresentativeMasks c.val) adj) :
    Model c adj ∧ Compat (s0 c) adj := by
  obtain ⟨_, _, hdeg, hc4, hsup, hpart⟩ := h
  refine ⟨⟨hsymm, hirr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j k l hij hkl h1 h2 h3 h4
    have hcard := hc4 i j hij
    have hk : k ∈ Finset.univ.filter (fun k => adj i k && adj j k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, by rw [h1, h2]; rfl⟩
    have hl : l ∈ Finset.univ.filter (fun k => adj i k && adj j k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, by rw [h3, h4]; rfl⟩
    exact hkl (Finset.card_le_one.mp hcard k hk l hl)
  · intro i hi5 w
    have hcard := hpart i hi5 ⟨w.val, by omega⟩ w.isLt
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hmem := Finset.mem_singleton_self k
    rw [← hk] at hmem
    have hmem' := (Finset.mem_filter.mp hmem).2
    simp only [Bool.and_eq_true] at hmem'
    exact ⟨k, hmem'.1, (mask_col c k w).symm.trans hmem'.2⟩
  · intro i hi5 w k l hk hkw hl hlw
    have hcard := hpart i hi5 ⟨w.val, by omega⟩ w.isLt
    have hk' : k ∈ Finset.univ.filter (fun k => adj i k &&
        (orderFortyNineSupportMask (fiveHighRepresentativeMasks c.val) k).getLsbD
          (⟨w.val, by omega⟩ : Fin 9).val) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hk, (mask_col c k w).trans hkw⟩
    have hl' : l ∈ Finset.univ.filter (fun k => adj i k &&
        (orderFortyNineSupportMask (fiveHighRepresentativeMasks c.val) k).getLsbD
          (⟨w.val, by omega⟩ : Fin 9).val) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hl, (mask_col c l w).trans hlw⟩
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
    rcases initRow_edges c a b hab with ⟨w, hb, hw⟩ | ⟨w, ha, hw⟩
    · rw [hb]
      have := hsup a ⟨w.val, by omega⟩ w.isLt
      exact this.trans ((mask_col c a w).trans hw)
    · rw [ha, hsymm]
      have := hsup b ⟨w.val, by omega⟩ w.isLt
      exact this.trans ((mask_col c b w).trans hw)

/-- Part `r` of the `m`-way split (prefix of `k` core vertices) of the search
for cell `c` from its initial state. -/
def cellPart (c : Fin 3) (k m r : Nat) : Bool := part c k m r (s0 c)

/-- If all parts of a split search return `true`, the canonical five-high
representative `c` is excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_of_parts (c : Fin 3) (k m : Nat)
    (hm : 0 < m) (h : ∀ r, r < m → cellPart c k m r = true) :
    FiveHighCanonicalRepresentativeExcluded c.val := by
  intro edges hc
  obtain ⟨M, hcompat⟩ := model_of_constraints c (adj := orderFortyNineBitAdj edges)
    (orderFortyNineBitAdj_comm edges)
    (fun a => by simp [orderFortyNineBitAdj]) hc
  exact parts_sound k m hm (s0 c) (s0_wf c) h _ M hcompat

end H5
end Erdos85

#print axioms Erdos85.H5.model_of_constraints
#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_of_parts
