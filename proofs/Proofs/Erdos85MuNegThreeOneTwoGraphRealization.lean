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

/-- Two cross-cell owners hit when they share an exterior owner vertex. -/
noncomputable def muNegThreeOwnerHitRel (u v : ZMod 8 → c.supp)
    (a b : Nat) : Bool := by
  classical
  exact decide (∃ z : V,
    MuNegThreeOwnerVertex G c u v a z ∧
    MuNegThreeOwnerVertex G c u v b z)

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
      ∃ z : V, MuNegThreeOwnerVertex G c u v a z ∧
        MuNegThreeOwnerVertex G c u v b z := by
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
  constructor <;> rintro ⟨z, ha, hb⟩ <;> exact ⟨z, hb, ha⟩

/-- A true hit decodes to one concrete exterior vertex realizing both
cross-cell owners. -/
theorem muNegThreeOwnerHitRel_witness
    (u v : ZMod 8 → c.supp) {a b : Nat}
    (h : muNegThreeOwnerHitRel G c u v a b = true) :
    ∃ z : V, z ∉ c.supp ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).1 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).2 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).1 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).2 z := by
  obtain ⟨z, ha, hb⟩ :=
    (muNegThreeOwnerHitRel_eq_true G c u v a b).mp h
  exact ⟨z, ha.1, ha.2.1, ha.2.2, hb.2.1, hb.2.2⟩

end

end Erdos85

#print axioms Erdos85.muNegThreeOwnerActive_graph_iff
#print axioms Erdos85.muNegThreeOwnerHitRel_comm
#print axioms Erdos85.muNegThreeOwnerHitRel_witness
