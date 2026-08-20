import Proofs.Erdos85MuNegOneOneFourOwnerTypedModel
import Proofs.Erdos85SizeTwoOwnerVertexDictionary
import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterCrossBlock

/-!
# Code-vertex map for the μ=-1 `(1,4)` owner grid

Node: outline F.3 (bridge increment 3c-ii-b; squad msgs 13994/14013).

Maps the generator's `Nat` codes `0..15` onto the two graph shores and
proves the adjacency correspondence: ambient `G`-adjacency between code
vertices matches the generator's `muNegOneGAdj` table exactly (octagon
within each shore, nothing across).  This is the translation layer the
service and C4 instantiations read through.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

/-- Nat codes below eight inject into `ZMod 8`. -/
theorem natCode_zmodEight_inj :
    ∀ x : Nat, x < 8 → ∀ y : Nat, y < 8 →
      (((x : ZMod 8) = (y : ZMod 8)) → x = y) := by
  decide

/-- Left-shore bridge between the generator's octagon table and cyclic
successor arithmetic. -/
theorem muNegOneGAdj_bridge_left :
    ∀ x, x < 8 → ∀ y, y < 8 →
      (muNegOneGAdj x y = true ↔
        ((y : ZMod 8) = (x : ZMod 8) - 1 ∨ (y : ZMod 8) = (x : ZMod 8) + 1)) := by
  decide

/-- Right-shore bridge. -/
theorem muNegOneGAdj_bridge_right :
    ∀ x, x < 8 → ∀ y, y < 8 →
      (muNegOneGAdj (8 + x) (8 + y) = true ↔
        ((y : ZMod 8) = (x : ZMod 8) - 1 ∨ (y : ZMod 8) = (x : ZMod 8) + 1)) := by
  decide

/-- The generator has no cross-shore octagon edges. -/
theorem muNegOneGAdj_cross_false :
    ∀ x, x < 16 → ∀ y, y < 16 → (x < 8 ↔ ¬ y < 8) →
      muNegOneGAdj x y = false := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- The generator's internal codes as component vertices: `0..7` on the
first shore, `8..15` on the second. -/
def muNegOneCodeVertex (u v : ZMod 8 → c.supp) (x : Nat) : V :=
  if x < 8 then (u (x : ZMod 8)).1 else (v ((x - 8 : Nat) : ZMod 8)).1

theorem muNegOneCodeVertex_mem_supp (u v : ZMod 8 → c.supp) (x : Nat) :
    muNegOneCodeVertex G c u v x ∈ c.supp := by
  unfold muNegOneCodeVertex
  split
  · exact (u _).2
  · exact (v _).2

section Shores

variable [DecidableEq (G.induce c.supp).ConnectedComponent]
  (a b : (G.induce c.supp).ConnectedComponent)
  (u v : ZMod 8 → c.supp)

/-- One shore's ambient adjacency is the cyclic octagon. -/
theorem shore_ambient_adj_iff
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)}) (i j : ZMod 8) :
    G.Adj (w i).1 (w j).1 ↔ (j = i - 1 ∨ j = i + 1) := by
  have hind : G.Adj (w i).1 (w j).1 ↔ (G.induce c.supp).Adj (w i) (w j) := by
    constructor
    · intro h
      exact h
    · intro h
      exact h
  rw [hind, ← SimpleGraph.mem_neighborFinset, hw i]
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl (hwinj h)
    · rw [Finset.mem_singleton] at h
      exact Or.inr (hwinj h)
  · intro h
    rcases h with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))

/-- No ambient edges across the two shores. -/
theorem cross_ambient_not_adj (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : ZMod 8) : ¬ G.Adj (u i).1 (v j).1 := by
  intro h
  have hind : (G.induce c.supp).Adj (u i) (v j) := h
  have hmk := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hind
  have hua : (G.induce c.supp).connectedComponentMk (u i) = a :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff a (u i)).mp
      (hurange ▸ Set.mem_range_self i)
  have hvb : (G.induce c.supp).connectedComponentMk (v j) = b :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff b (v j)).mp
      (hvrange ▸ Set.mem_range_self j)
  exact hab (hua ▸ hvb ▸ hmk)

/-- The two shores are vertex-disjoint. -/
theorem shore_vertices_ne (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : ZMod 8) : (u i).1 ≠ (v j).1 := by
  intro h
  have huv : u i = v j := Subtype.ext h
  have hua : (G.induce c.supp).connectedComponentMk (u i) = a :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff a (u i)).mp
      (hurange ▸ Set.mem_range_self i)
  have hvb : (G.induce c.supp).connectedComponentMk (v j) = b :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff b (v j)).mp
      (hvrange ▸ Set.mem_range_self j)
  rw [huv] at hua
  exact hab (hua ▸ hvb)

/-- The code-vertex map is injective on internal codes. -/
theorem muNegOneCodeVertex_inj (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x, x < 16 → ∀ y, y < 16 →
      muNegOneCodeVertex G c u v x = muNegOneCodeVertex G c u v y → x = y := by
  intro x hx y hy h
  unfold muNegOneCodeVertex at h
  by_cases hx8 : x < 8 <;> by_cases hy8 : y < 8
  · rw [if_pos hx8, if_pos hy8] at h
    exact natCode_zmodEight_inj x hx8 y hy8 (huinj (Subtype.ext h))
  · rw [if_pos hx8, if_neg hy8] at h
    exact absurd h (shore_vertices_ne G c a b u v hab hurange hvrange _ _)
  · rw [if_neg hx8, if_pos hy8] at h
    exact absurd h.symm (shore_vertices_ne G c a b u v hab hurange hvrange _ _)
  · rw [if_neg hx8, if_neg hy8] at h
    have := natCode_zmodEight_inj (x - 8) (by omega) (y - 8) (by omega)
      (hvinj (Subtype.ext h))
    omega

/-- **Adjacency correspondence.**  Ambient adjacency between code
vertices matches the generator's octagon table. -/
theorem muNegOneCodeVertex_adj_iff (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ x, x < 16 → ∀ y, y < 16 →
      (G.Adj (muNegOneCodeVertex G c u v x) (muNegOneCodeVertex G c u v y) ↔
        muNegOneGAdj x y = true) := by
  intro x hx y hy
  unfold muNegOneCodeVertex
  by_cases hx8 : x < 8 <;> by_cases hy8 : y < 8
  · rw [if_pos hx8, if_pos hy8,
      shore_ambient_adj_iff G c u huinj hu,
      muNegOneGAdj_bridge_left x hx8 y hy8]
  · rw [if_pos hx8, if_neg hy8,
      muNegOneGAdj_cross_false x (by omega) y (by omega) (by omega)]
    simp only [Bool.false_eq_true, iff_false]
    exact cross_ambient_not_adj G c a b u v hab hurange hvrange _ _
  · rw [if_neg hx8, if_pos hy8,
      muNegOneGAdj_cross_false x (by omega) y (by omega) (by omega)]
    simp only [Bool.false_eq_true, iff_false]
    intro h
    exact cross_ambient_not_adj G c a b u v hab hurange hvrange _ _ h.symm
  · rw [if_neg hx8, if_neg hy8,
      shore_ambient_adj_iff G c v hvinj hv]
    have h := muNegOneGAdj_bridge_right (x - 8) (by omega) (y - 8) (by omega)
    rw [show 8 + (x - 8) = x from by omega,
      show 8 + (y - 8) = y from by omega] at h
    exact h.symm

end Shores

end

end Erdos85

#print axioms Erdos85.muNegOneCodeVertex_adj_iff
#print axioms Erdos85.muNegOneCodeVertex_inj
