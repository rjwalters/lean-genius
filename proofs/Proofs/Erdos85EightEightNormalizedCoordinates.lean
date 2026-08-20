import Proofs.Erdos85DefectCycleBlock
import Proofs.Erdos85IsCyclesComponentCharpoly
import Proofs.Erdos85EightEightConcreteTerminalAssembly
import Proofs.Erdos85OrderSixtyFourSizeSixteenOutsideFeasibility

/-!
# Additive coordinates for two eight-cycle components

The structural `8+8` terminal consumes explicit `ZMod 8` parametrizations
whose predecessor and successor are the exact two internal neighbors.  This
file extracts those coordinates from the abstract connected components of a
finite two-regular graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An eight-vertex component of a finite two-regular graph admits the exact
additive `ZMod 8` coordinate package used by the `8+8` terminal. -/
theorem exists_zmodEight_component_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a : H.ConnectedComponent) (ha : a.supp.ncard = 8) :
    ∃ u : ZMod 8 → V,
      Function.Injective u ∧
      Set.range u = a.supp ∧
      ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)} := by
  obtain ⟨x, p, hp, hpverts, _hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph H hdeg a
  have hlen : p.length = 8 := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = a.supp.ncard := congrArg Set.ncard hpverts
      _ = 8 := ha
  obtain ⟨u₀, hu₀inj, hu₀range, hu₀⟩ :=
    exists_zmod_cycleParam_neighborFinset hp hdeg
  let cast : ZMod 8 ≃+* ZMod p.length :=
    ZMod.ringEquivCongr hlen.symm
  let u : ZMod 8 → V := fun z => u₀ (cast z)
  have huinj : Function.Injective u := hu₀inj.comp cast.injective
  have hurange : Set.range u = a.supp := by
    rw [show Set.range u = Set.range u₀ by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨cast z, rfl⟩
      · rintro ⟨w, rfl⟩
        obtain ⟨z, rfl⟩ := cast.surjective w
        exact ⟨z, rfl⟩]
    exact hu₀range.trans hpverts
  refine ⟨u, huinj, hurange, ?_⟩
  intro z
  rw [hu₀]
  congr 1
  · simp [u, cast]
  · simp [u, cast]

/-- Two eight-vertex components can be coordinatized simultaneously in the
form expected by the concrete `8+8` terminal. -/
theorem exists_zmodEight_twoComponent_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a b : H.ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) :
    ∃ (u v : ZMod 8 → V),
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = a.supp ∧ Set.range v = b.supp ∧
      (∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)}) ∧
      ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)} := by
  obtain ⟨u, huinj, hurange, hu⟩ :=
    exists_zmodEight_component_coordinates H hdeg a ha
  obtain ⟨v, hvinj, hvrange, hv⟩ :=
    exists_zmodEight_component_coordinates H hdeg b hb
  exact ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩

end

end Erdos85

#print axioms Erdos85.exists_zmodEight_component_coordinates
#print axioms Erdos85.exists_zmodEight_twoComponent_coordinates
