import Proofs.Erdos85MuNegOneOneFourServerClassification
import Proofs.Erdos85MuNegOneOneFourFiniteSemantics

/-!
# Concrete graph relations for the μ=-1 `(1,4)` finite semantics

Node: outline F.3 (bridge increment 3c-ii-f; squad msg 14093).

Fixes the graph meaning of the two `Nat`-coded relations consumed by
the finite-semantics record: `D` is the complement of cross
exterior-pair adjacency on shore coordinates (matching the banked count
fields), `X` holds when both owners are realized by ambient-adjacent
owner vertices.  Provides the extraction and activity laws every field
proof reads through.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- The cross-defect relation: complement of cross exterior-pair
adjacency (the banked count-field shape). -/
def muNegOneDGraph (u v : ZMod 8 → c.supp) : Nat → Nat → Bool :=
  fun i j ↦ !(decide ((exteriorPairGraph G c.supp).Adj
    (u (i : ZMod 8)) (v (j : ZMod 8))))

open Classical in
/-- The hit relation: both owners realized by adjacent owner
vertices. -/
noncomputable def muNegOneXGraph (u v : ZMod 8 → c.supp)
    (uTri vTri : Bool) : Nat → Nat → Bool :=
  fun aa bb ↦ decide (∃ (ha : aa < 80) (hb : bb < 80) (te tf : V),
    MuNegOneOwnerVertex G c u v uTri vTri ⟨aa, ha⟩ te ∧
    MuNegOneOwnerVertex G c u v uTri vTri ⟨bb, hb⟩ tf ∧ G.Adj te tf)

section Laws

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

theorem muNegOneXGraph_true_iff (aa bb : Nat) :
    muNegOneXGraph G c u v uTri vTri aa bb = true ↔
      ∃ (ha : aa < 80) (hb : bb < 80) (te tf : V),
        MuNegOneOwnerVertex G c u v uTri vTri ⟨aa, ha⟩ te ∧
        MuNegOneOwnerVertex G c u v uTri vTri ⟨bb, hb⟩ tf ∧ G.Adj te tf := by
  classical
  unfold muNegOneXGraph
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

/-- A realized cross owner is exterior-pair adjacent across the
shores. -/
theorem muNegOne_cross_R_of_ownerVertex
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e : Fin 80} (he : 16 ≤ e.val) {t : V}
    (ht : MuNegOneOwnerVertex G c u v uTri vTri e t) :
    (exteriorPairGraph G c.supp).Adj
      (u ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8))
      (v (((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8)) := by
  obtain ⟨h1, h2a, h2b⟩ := muNegOneOwner_cross_codes uTri vTri e he
  have hfst : muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1 =
      (u ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8)).1 := by
    unfold muNegOneCodeVertex
    rw [if_pos h1]
  have hsnd : muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2 =
      (v (((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8)).1 := by
    unfold muNegOneCodeVertex
    rw [if_neg (by omega)]
  refine ⟨?_, t, ht.1, ?_, ?_⟩
  · intro h
    exact shore_vertices_ne G c a b u v hab hurange hvrange _ _
      (congrArg Subtype.val h)
  · rw [← hfst]
    exact ht.2.1
  · rw [← hsnd]
    exact ht.2.2

/-- A realized owner is active. -/
theorem muNegOneOwnerActive_of_ownerVertex
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e : Fin 80} {t : V}
    (ht : MuNegOneOwnerVertex G c u v uTri vTri e t) :
    muNegOneOwnerActive (muNegOneDGraph G c u v) e.val = true := by
  unfold muNegOneOwnerActive
  by_cases he16 : e.val < 16
  · rw [if_pos he16]
  · rw [if_neg he16]
    have he : 16 ≤ e.val := by omega
    have hR := muNegOne_cross_R_of_ownerVertex G c u v uTri vTri
      a b hab hurange hvrange he ht
    have hcross := muNegOneOwnerAt_cross uTri vTri e he
    unfold muNegOneDGraph
    rw [Bool.not_not]
    apply decide_eq_true
    have h1 : (muNegOneOwnerAt uTri vTri e).1 = (e.val - 16) / 8 := by
      rw [hcross]
    have h2 : (muNegOneOwnerAt uTri vTri e).2 - 8 = (e.val - 16) % 8 := by
      rw [hcross]
      show 8 + (e.val - 16) % 8 - 8 = (e.val - 16) % 8
      omega
    rw [h1, h2] at hR
    exact hR

/-- An active owner is realized. -/
theorem muNegOne_ownerVertex_of_active
    (hfree : ¬ containsC4 V G)
    (hmodeu : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v)
    {e : Fin 80}
    (hact : muNegOneOwnerActive (muNegOneDGraph G c u v) e.val = true) :
    ∃ t : V, MuNegOneOwnerVertex G c u v uTri vTri e t ∧
      ∀ t' : V,
        G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1) t' →
        G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2) t' →
        t' = t := by
  by_cases he8 : e.val < 8
  · exact muNegOneOwnerVertex_of_R_adj G c u v uTri vTri hfree e
      (muNegOneOwner_R_adj_left G c u v uTri vTri hmodeu e he8)
  · by_cases he16 : e.val < 16
    · exact muNegOneOwnerVertex_of_R_adj G c u v uTri vTri hfree e
        (muNegOneOwner_R_adj_right G c u v uTri vTri hmodev e
          (by omega) he16)
    · have he : 16 ≤ e.val := by omega
      have hcross := muNegOneOwnerAt_cross uTri vTri e he
      have hR : (exteriorPairGraph G c.supp).Adj
          (u ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8))
          (v (((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8)) := by
        unfold muNegOneOwnerActive at hact
        rw [if_neg (by omega)] at hact
        unfold muNegOneDGraph at hact
        rw [Bool.not_not] at hact
        have h1 : (muNegOneOwnerAt uTri vTri e).1 = (e.val - 16) / 8 := by
          rw [hcross]
        have h2 : (muNegOneOwnerAt uTri vTri e).2 - 8 = (e.val - 16) % 8 := by
          rw [hcross]
          show 8 + (e.val - 16) % 8 - 8 = (e.val - 16) % 8
          omega
        rw [h1, h2]
        exact of_decide_eq_true hact
      exact muNegOneOwnerVertex_of_R_adj G c u v uTri vTri hfree e
        (muNegOneOwner_R_adj_cross G c u v uTri vTri e he hR)

/-- The hit-activity field for the concrete relations. -/
theorem muNegOne_hit_active_graph
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ aa bb : Nat, (aa, bb) ∈ muNegOneHitPairs uTri vTri →
      muNegOneXGraph G c u v uTri vTri aa bb = true →
        muNegOneOwnerActive (muNegOneDGraph G c u v) aa = true ∧
        muNegOneOwnerActive (muNegOneDGraph G c u v) bb = true := by
  intro aa bb _ hX
  obtain ⟨ha, hb, te, tf, hte, htf, _⟩ :=
    (muNegOneXGraph_true_iff G c u v uTri vTri aa bb).mp hX
  exact ⟨muNegOneOwnerActive_of_ownerVertex G c u v uTri vTri
      a b hab hurange hvrange hte,
    muNegOneOwnerActive_of_ownerVertex G c u v uTri vTri
      a b hab hurange hvrange htf⟩

end Laws

end

end Erdos85

#print axioms Erdos85.muNegOne_ownerVertex_of_active
#print axioms Erdos85.muNegOneOwnerActive_of_ownerVertex
#print axioms Erdos85.muNegOne_hit_active_graph
