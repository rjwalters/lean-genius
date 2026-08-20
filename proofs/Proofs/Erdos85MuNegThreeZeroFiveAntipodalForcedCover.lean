import Proofs.Erdos85MuNegThreeZeroFiveAntipodalForcedTypeCounts
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Global cover by the antipodal forced target sets -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The union of the forced antipodal target sets over all shore coordinates.
Although indexed eight times, opposite indices give the same two-star union. -/
def h305AntipodalForcedCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) : Finset (Sym2 V) :=
  (Finset.univ : Finset (ZMod 8)).biUnion fun i ↦
    h305AntipodalSaturatedStarUnion R u i

/-- Globally, the antipodal forced sets cover exactly the exterior edges
having at least one endpoint on the selected shore. -/
theorem h305_antipodalForcedCover_eq_positiveShoreTypes
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
    h305AntipodalForcedCover R u =
      ((shoreTypeEdgeFinset R U 1) ∪
        shoreTypeEdgeFinset R U 2).map eR := by
  classical
  dsimp only
  ext e
  simp only [h305AntipodalForcedCover, Finset.mem_biUnion,
    Finset.mem_map, shoreTypeEdgeFinset,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hei⟩
    change e ∈ h305AntipodalSaturatedStarUnion R u i at hei
    rw [h305AntipodalSaturatedStarUnion, Finset.mem_union] at hei
    rcases hei with hei | hei
    · rw [R.incidenceFinset_eq_filter] at hei
      have hei' := Finset.mem_filter.mp hei
      let a : R.edgeFinset := ⟨e, hei'.1⟩
      refine ⟨a, ?_, rfl⟩
      have huMem : u (i + 2) ∈ e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u :=
        Finset.mem_inter.mpr ⟨Sym2.mem_toFinset.mpr hei'.2,
          Finset.mem_image.mpr ⟨i + 2, Finset.mem_univ _, rfl⟩⟩
      have hpos : 0 < (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card :=
        Finset.card_pos.mpr ⟨u (i + 2), huMem⟩
      have hle : (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card ≤ 2 := by
        calc
          _ ≤ e.toFinset.card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := R.card_toFinset_mem_edgeFinset a
      have honeTwo : (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card = 1 ∨
          (e.toFinset ∩
            (Finset.univ : Finset (ZMod 8)).image u).card = 2 := by omega
      rcases honeTwo with h | h
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using h⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using h⟩))
    · rw [R.incidenceFinset_eq_filter] at hei
      have hei' := Finset.mem_filter.mp hei
      let a : R.edgeFinset := ⟨e, hei'.1⟩
      refine ⟨a, ?_, rfl⟩
      have huMem : u (i + 6) ∈ e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u :=
        Finset.mem_inter.mpr ⟨Sym2.mem_toFinset.mpr hei'.2,
          Finset.mem_image.mpr ⟨i + 6, Finset.mem_univ _, rfl⟩⟩
      have hpos : 0 < (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card :=
        Finset.card_pos.mpr ⟨u (i + 6), huMem⟩
      have hle : (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card ≤ 2 := by
        calc
          _ ≤ e.toFinset.card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := R.card_toFinset_mem_edgeFinset a
      have honeTwo : (e.toFinset ∩
          (Finset.univ : Finset (ZMod 8)).image u).card = 1 ∨
          (e.toFinset ∩
            (Finset.univ : Finset (ZMod 8)).image u).card = 2 := by omega
      rcases honeTwo with h | h
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using h⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using h⟩))
  · rintro ⟨a, ha, rfl⟩
    change a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1 ∪
        shoreTypeEdgeFinset R ((Finset.univ : Finset (ZMod 8)).image u) 2 at ha
    rw [Finset.mem_union] at ha
    simp only [shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha
    have hpos : 0 < (a.1.toFinset ∩
        (Finset.univ : Finset (ZMod 8)).image u).card := by
      rcases ha with ha | ha <;> omega
    obtain ⟨x, hxU⟩ := Finset.card_pos.mp hpos
    have hxImage := (Finset.mem_inter.mp hxU).2
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hxImage
    refine ⟨k - 2, ?_⟩
    rw [h305AntipodalSaturatedStarUnion, Finset.mem_union]
    apply Or.inl
    rw [R.incidenceFinset_eq_filter]
    exact Finset.mem_filter.mpr ⟨a.2, by
      simpa using Sym2.mem_toFinset.mp (Finset.mem_inter.mp hxU).1⟩

/-- The four distinct antipodal forced sets collectively cover 36 exterior
edges: all twelve same-shore and all twenty-four cross-shore edges. -/
theorem h305_antipodalForcedCover_card_thirtySix
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hreg : ∀ x, R.degree x = 6) :
    (h305AntipodalForcedCover R u).card = 36 := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  rw [h305_antipodalForcedCover_eq_positiveShoreTypes R u]
  rw [Finset.card_map]
  obtain ⟨h2, h1, _⟩ :=
    h305_correctShoreModes_typePopulations_of_coordinates R u v
      huinj hvinj hdisj hcover humode hvmode hreg
  have hdis : Disjoint (shoreTypeEdgeFinset R U 1)
      (shoreTypeEdgeFinset R U 2) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha1 ha2
    omega
  rw [Finset.card_union_of_disjoint hdis, h1, h2]

end

end Erdos85

#print axioms Erdos85.h305_antipodalForcedCover_eq_positiveShoreTypes
#print axioms Erdos85.h305_antipodalForcedCover_card_thirtySix
