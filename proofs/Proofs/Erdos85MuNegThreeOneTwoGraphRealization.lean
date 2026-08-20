import Proofs.Erdos85MuNegThreeOneTwoOwnerBridge
import Proofs.Erdos85SizeTwoMuNegThreeAlignedShoreSwitch

/-!
# Graph realization of the `mu=-3`, `(k,r)=(1,2)` owner relations

This layer fixes the graph meaning of the two finite relations consumed by
`muNegThreeOneTwoFiniteSemantics_false`.  A defect bit is signed cross-defect
adjacency between the two cyclic shores.  An owner hit means that the two
active cross cells have a common exterior owner vertex.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- The vertex pair named by cross-cell `a = 8i+j`. -/
def muNegThreeOwnerEndpoints (u v : ZMod 8 → c.supp) (a : Nat) : V × V :=
  ((u (muNegThreeCellRow a : ZMod 8)).1,
    (v (muNegThreeCellCol a : ZMod 8)).1)

/-- A graph vertex realizing a cross-cell owner. -/
def MuNegThreeOwnerVertex (u v : ZMod 8 → c.supp)
    (a : Nat) (z : V) : Prop :=
  z ∉ c.supp ∧
    G.Adj (muNegThreeOwnerEndpoints G c u v a).1 z ∧
    G.Adj (muNegThreeOwnerEndpoints G c u v a).2 z

/-- The signed cross-defect relation in cyclic coordinates. -/
def muNegThreeCrossDefectRel (s : V → ℤ)
    (u v : ZMod 8 → c.supp) (i j : Nat) : Bool :=
  decide (s (u (i : ZMod 8)).1 = s (v (j : ZMod 8)).1 ∧
    (secondOrderDefectGraph G).Adj
      (u (i : ZMod 8)).1 (v (j : ZMod 8)).1)

/-- Two cross-cell owners hit when their exterior owner vertices are
adjacent in the ambient graph. -/
noncomputable def muNegThreeOwnerHitRel (u v : ZMod 8 → c.supp)
    (a b : Nat) : Bool := by
  classical
  exact decide (∃ z w : V,
    MuNegThreeOwnerVertex G c u v a z ∧
    MuNegThreeOwnerVertex G c u v b w ∧ G.Adj z w)

@[simp] theorem muNegThreeCrossDefectRel_eq_true
    (s : V → ℤ) (u v : ZMod 8 → c.supp) (i j : Nat) :
    muNegThreeCrossDefectRel G c s u v i j = true ↔
      s (u (i : ZMod 8)).1 = s (v (j : ZMod 8)).1 ∧
        (secondOrderDefectGraph G).Adj
          (u (i : ZMod 8)).1 (v (j : ZMod 8)).1 := by
  simp [muNegThreeCrossDefectRel]

@[simp] theorem muNegThreeOwnerHitRel_eq_true
    (u v : ZMod 8 → c.supp) (a b : Nat) :
    muNegThreeOwnerHitRel G c u v a b = true ↔
      ∃ z w : V, MuNegThreeOwnerVertex G c u v a z ∧
        MuNegThreeOwnerVertex G c u v b w ∧ G.Adj z w := by
  classical
  simp [muNegThreeOwnerHitRel]

theorem muNegThreeOwnerEndpoints_row_col
    (u v : ZMod 8 → c.supp) {a : Nat} (ha : a < 64) :
    muNegThreeOwnerEndpoints G c u v a =
      ((u (muNegThreeCellRow a : ZMod 8)).1,
        (v (muNegThreeCellCol a : ZMod 8)).1) := by
  rfl

/-- In the induced valuation, a cross cell is active exactly when its
signed defect adjacency is absent. -/
theorem muNegThreeOwnerActive_graph_iff
    (s : V → ℤ) (u v : ZMod 8 → c.supp) (a : Nat) :
    muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) a = true ↔
      ¬ (s (u (muNegThreeCellRow a : ZMod 8)).1 =
          s (v (muNegThreeCellCol a : ZMod 8)).1 ∧
        (secondOrderDefectGraph G).Adj
          (u (muNegThreeCellRow a : ZMod 8)).1
          (v (muNegThreeCellCol a : ZMod 8)).1) := by
  simp [muNegThreeOwnerActive, muNegThreeCrossDefectRel]
  tauto

/-- Hit symmetry is inherited from sharing the same exterior vertex. -/
theorem muNegThreeOwnerHitRel_comm
    (u v : ZMod 8 → c.supp) (a b : Nat) :
    muNegThreeOwnerHitRel G c u v a b =
      muNegThreeOwnerHitRel G c u v b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [muNegThreeOwnerHitRel_eq_true]
  constructor
  · rintro ⟨z, w, hz, hw, hzw⟩
    exact ⟨w, z, hw, hz, hzw.symm⟩
  · rintro ⟨w, z, hw, hz, hwz⟩
    exact ⟨z, w, hz, hw, hwz.symm⟩

/-- A true hit decodes to adjacent concrete exterior vertices realizing
the two cross-cell owners. -/
theorem muNegThreeOwnerHitRel_witness
    (u v : ZMod 8 → c.supp) {a b : Nat}
    (h : muNegThreeOwnerHitRel G c u v a b = true) :
    ∃ z w : V, z ∉ c.supp ∧ w ∉ c.supp ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).1 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).2 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).1 w ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).2 w ∧ G.Adj z w := by
  obtain ⟨z, w, ha, hb, hzw⟩ :=
    (muNegThreeOwnerHitRel_eq_true G c u v a b).mp h
  exact ⟨z, w, ha.1, hb.1, ha.2.1, ha.2.2, hb.2.1, hb.2.2, hzw⟩

section StructuralFields

variable [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- Cross-cell endpoints lie on distinct internal components. -/
theorem muNegThreeOwnerEndpoints_ne
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (x : Nat) :
    (muNegThreeOwnerEndpoints G c u v x).1 ≠
      (muNegThreeOwnerEndpoints G c u v x).2 := by
  intro huv
  apply hab
  let i : ZMod 8 := muNegThreeCellRow x
  let j : ZMod 8 := muNegThreeCellCol x
  have hui : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvj : v j ∈ b.supp := by
    rw [← hvrange]
    exact ⟨j, rfl⟩
  have huv' : u i = v j := Subtype.ext huv
  exact ConnectedComponent.eq_of_common_vertex (huv' ▸ hui) hvj

/-- A realized exterior owner rules out defect adjacency of its endpoint
pair, since it supplies a common neighbor. -/
theorem muNegThreeOwnerVertex_not_defect
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {x : Nat} {z : V} (hz : MuNegThreeOwnerVertex G c u v x z) :
    ¬ (secondOrderDefectGraph G).Adj
      (muNegThreeOwnerEndpoints G c u v x).1
      (muNegThreeOwnerEndpoints G c u v x).2 := by
  intro hD
  have hne := muNegThreeOwnerEndpoints_ne G c a b hab u v hurange hvrange x
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree hne).mp hD
  have hzmem : z ∈
      G.neighborFinset (muNegThreeOwnerEndpoints G c u v x).1 ∩
        G.neighborFinset (muNegThreeOwnerEndpoints G c u v x).2 := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hz.2.1, hz.2.2⟩
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hzmem
  exact Finset.notMem_empty z hzmem

/-- The graph hit relation satisfies the finite socket's hit-activity
field. -/
theorem muNegThreeGraph_hit_active
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (s : V → ℤ) (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x y, (x, y) ∈ muNegThreeHitPairs →
      muNegThreeOwnerHitRel G c u v x y = true →
      muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) x = true ∧
        muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) y = true := by
  intro x y _hkey hX
  obtain ⟨z, w, hx, hy, _hzw⟩ :=
    (muNegThreeOwnerHitRel_eq_true G c u v x y).mp hX
  constructor
  · rw [muNegThreeOwnerActive_graph_iff]
    intro hD
    exact muNegThreeOwnerVertex_not_defect G c hfree a b hab u v
      hurange hvrange hx hD.2
  · rw [muNegThreeOwnerActive_graph_iff]
    intro hD
    exact muNegThreeOwnerVertex_not_defect G c hfree a b hab u v
      hurange hvrange hy hD.2

end StructuralFields

end

end Erdos85

#print axioms Erdos85.muNegThreeOwnerActive_graph_iff
#print axioms Erdos85.muNegThreeOwnerHitRel_comm
#print axioms Erdos85.muNegThreeOwnerHitRel_witness
#print axioms Erdos85.muNegThreeGraph_hit_active
