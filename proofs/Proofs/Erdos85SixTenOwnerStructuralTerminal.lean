import Proofs.Erdos85SixTenCoordinateCover
import Proofs.Erdos85SixTenMixedOwnerTerminalCapstone
import Proofs.Erdos85SixTenAllTfOwnerTerminalCapstone

/-!
# Normalized structural terminals for the six-plus-ten branches

The structural exterior-model theorems describe cross pairs through the
alternating eigenline sign.  The checked owner models use coordinate parity.
This file identifies those descriptions in sign-normalized cyclic
coordinates and supplies the internal-cycle model required by both checked
terminals.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

open SixTenMixedOwnerBridge

set_option maxHeartbeats 0

def sixTenParitySign (i : Nat) : ℤ :=
  if i % 2 = 0 then 1 else -1

theorem sixTenParitySign_neg_iff
    (i : ZMod 6) (j : ZMod 10) :
    sixTenParitySign ((ZMod.finEquiv 10).symm j).val =
        -sixTenParitySign ((ZMod.finEquiv 6).symm i).val ↔
      ((ZMod.finEquiv 6).symm i).val % 2 ≠
        ((ZMod.finEquiv 10).symm j).val % 2 := by
  revert i j
  decide

theorem sixTenCycleAdj_left (i j : ZMod 6) :
    sixTenCycleAdj (zmodSixLeftFin16 i) (zmodSixLeftFin16 j) = true ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

theorem sixTenCycleAdj_right (i j : ZMod 10) :
    sixTenCycleAdj (zmodTenRightFin16 i) (zmodTenRightFin16 j) = true ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

theorem sixTenCycleAdj_cross (i : ZMod 6) (j : ZMod 10) :
    sixTenCycleAdj (zmodSixLeftFin16 i) (zmodTenRightFin16 j) = false := by
  revert i j
  decide

theorem sixTenCycleAdj_cross_rev (i : ZMod 10) (j : ZMod 6) :
    sixTenCycleAdj (zmodTenRightFin16 i) (zmodSixLeftFin16 j) = false := by
  revert i j
  decide

theorem sixTenAllTfCycleAdj_eq_sixTenCycleAdj (a b : Fin 16) :
    sixTenAllTfCycleAdj a b = sixTenCycleAdj a b := by
  revert a b
  decide

/-- The canonical C6+C10 shore equivalence transports the induced ambient
graph to the Boolean cycle predicate used by both owner generators. -/
theorem sixTenCycleAdj_of_shoreCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let coord := sixTenShoreCoordinateEquiv
      G c hc a b hab u v huinj hvinj hurange hvrange
    ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenCycleAdj (coord x) (coord y) = true := by
  dsimp only
  let H := G.induce c.supp
  let coord := sixTenShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcover := sixTen_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [sixTenShoreCoordinateEquiv_apply_u,
      sixTenShoreCoordinateEquiv_apply_u, sixTenCycleAdj_left]
    change H.Adj (u i) (u j) ↔ _
    rw [← H.mem_neighborFinset, hu]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (huinj h)
      · exact Or.inr (huinj h)
    · rintro (rfl | rfl) <;> simp

  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    constructor
    · intro huv
      have hvA : v j ∈ a.supp :=
        (ConnectedComponent.mem_supp_congr_adj a huv).mp (by
          rw [← hurange]; exact ⟨i, rfl⟩)
      exact (hab (ConnectedComponent.eq_of_common_vertex hvA (by
        rw [← hvrange]; exact ⟨j, rfl⟩))).elim
    · intro hfixed
      have hfalse := sixTenCycleAdj_cross i j
      rw [sixTenShoreCoordinateEquiv_apply_u,
        sixTenShoreCoordinateEquiv_apply_v, hfalse] at hfixed
      exact (Bool.false_ne_true hfixed).elim
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hya
    constructor
    · intro hvu
      have huB : u j ∈ b.supp :=
        (ConnectedComponent.mem_supp_congr_adj b hvu).mp (by
          rw [← hvrange]; exact ⟨i, rfl⟩)
      exact (hab (ConnectedComponent.eq_of_common_vertex (by
        rw [← hurange]; exact ⟨j, rfl⟩) huB)).elim
    · intro hfixed
      have hfalse := sixTenCycleAdj_cross_rev i j
      rw [sixTenShoreCoordinateEquiv_apply_v,
        sixTenShoreCoordinateEquiv_apply_u, hfalse] at hfixed
      exact (Bool.false_ne_true hfixed).elim
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [sixTenShoreCoordinateEquiv_apply_v,
      sixTenShoreCoordinateEquiv_apply_v, sixTenCycleAdj_right]
    change H.Adj (v i) (v j) ↔ _
    rw [← H.mem_neighborFinset, hv]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (hvinj h)
      · exact Or.inr (hvinj h)
    · rintro (rfl | rfl) <;> simp

/-- A sign-normalized realization of the mixed C6+C10 exterior model is
contradictory by the checked mixed-owner certificate. -/
theorem sixTenMixedExteriorPairModel_false_of_normalized_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ)
    (hsu : ∀ i, s (u i).1 =
      sixTenParitySign ((ZMod.finEquiv 6).symm i).val)
    (hsv : ∀ j, s (v j).1 =
      sixTenParitySign ((ZMod.finEquiv 10).symm j).val)
    (hleft : ∀ i j : ZMod 6,
      (exteriorPairGraph G c).Adj (u i) (u j) ↔ j - i = 3)
    (hright : ∀ i j : ZMod 10,
      (exteriorPairGraph G c).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 5 ∨ j - i = 9)
    (hcross : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        s (v j).1 = -s (u i).1) : False := by
  let coord := sixTenShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcover := sixTen_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcrossParity : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        ((ZMod.finEquiv 6).symm i).val % 2 ≠
          ((ZMod.finEquiv 10).symm j).val % 2 := by
    intro i j
    rw [hcross, hsu, hsv]
    exact sixTenParitySign_neg_iff i j
  apply sixTenMixedExteriorPairModel_false_of_shoreCoordinates
    G hfree c hcard hinc hqcard hRedges a b u v hurange hvrange
      hcover coord
  · exact sixTenShoreCoordinateEquiv_apply_u
      G c hc a b hab u v huinj hvinj hurange hvrange
  · exact sixTenShoreCoordinateEquiv_apply_v
      G c hc a b hab u v huinj hvinj hurange hvrange
  · exact hleft
  · exact hright
  · exact hcrossParity
  · exact sixTenCycleAdj_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv

/-- A sign-normalized realization of the all-triangle-free C6+C10 exterior
model is contradictory by the checked all-TF owner certificate. -/
theorem sixTenAllTfExteriorPairModel_false_of_normalized_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ)
    (hsu : ∀ i, s (u i).1 =
      sixTenParitySign ((ZMod.finEquiv 6).symm i).val)
    (hsv : ∀ j, s (v j).1 =
      sixTenParitySign ((ZMod.finEquiv 10).symm j).val)
    (hleft : ∀ i j : ZMod 6,
      (exteriorPairGraph G c).Adj (u i) (u j) ↔ j - i = 3)
    (hright : ∀ i j : ZMod 10,
      (exteriorPairGraph G c).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (hcross : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        s (v j).1 = -s (u i).1) : False := by
  let coord := sixTenShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcover := sixTen_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcrossParity : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        ((ZMod.finEquiv 6).symm i).val % 2 ≠
          ((ZMod.finEquiv 10).symm j).val % 2 := by
    intro i j
    rw [hcross, hsu, hsv]
    exact sixTenParitySign_neg_iff i j
  apply sixTenAllTfExteriorPairModel_false_of_shoreCoordinates
    G hfree c hcard hinc hqcard hRedges a b u v hurange hvrange
      hcover coord
  · exact sixTenShoreCoordinateEquiv_apply_u
      G c hc a b hab u v huinj hvinj hurange hvrange
  · exact sixTenShoreCoordinateEquiv_apply_v
      G c hc a b hab u v huinj hvinj hurange hvrange
  · exact hleft
  · exact hright
  · exact hcrossParity
  · intro x y
    rw [sixTenAllTfCycleAdj_eq_sixTenCycleAdj]
    exact sixTenCycleAdj_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv x y

end


end Erdos85

#print axioms Erdos85.sixTenCycleAdj_of_shoreCoordinates
#print axioms Erdos85.sixTenMixedExteriorPairModel_false_of_normalized_shores
#print axioms Erdos85.sixTenAllTfExteriorPairModel_false_of_normalized_shores
