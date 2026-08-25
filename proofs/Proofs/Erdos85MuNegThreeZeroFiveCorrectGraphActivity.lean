import Proofs.Erdos85MuNegThreeZeroFiveCorrectFiniteSemantics
import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphRealization

/-! # Corrected h305 graph activity and realization -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

theorem muNegThreeZeroFiveCorrectGuard?_fixed :
    ∀ (uTri vTri : Bool) (e : Fin 88), e.val < 24 →
      muNegThreeZeroFiveCorrectGuard?
        (muNegThreeZeroFiveCorrectOwners uTri vTri) e.val = none := by
  decide

theorem muNegThreeZeroFiveCorrectGuard?_cross :
    ∀ (uTri vTri : Bool) (e : Fin 88), 24 ≤ e.val →
      muNegThreeZeroFiveCorrectGuard?
        (muNegThreeZeroFiveCorrectOwners uTri vTri) e.val =
      some (muNegOneDVar
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1
        ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8)) := by
  decide

theorem muNegThreeZeroFiveCorrectOwners_getElem!
    (uTri vTri : Bool) (e : Fin 88) :
    (muNegThreeZeroFiveCorrectOwners uTri vTri)[e.val]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri e := by
  have h : e.val < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
    rw [muNegThreeZeroFiveCorrectOwners_length]
    exact e.isLt
  rw [getElem!_pos (c := muNegThreeZeroFiveCorrectOwners uTri vTri)
    (i := e.val) h]
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

section Activity

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

/-- The h305 cross-defect relation: complement of cross exterior adjacency. -/
def muNegThreeZeroFiveCorrectDGraph : Nat → Nat → Bool :=
  fun i j ↦ !(decide ((exteriorPairGraph G c.supp).Adj
    (u (i : ZMod 8)) (v (j : ZMod 8))))

theorem muNegThreeZeroFiveCorrectOwnerActive_of_ownerVertex
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e : Fin 88} {t : V}
    (ht : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t) :
    muNegThreeZeroFiveCorrectOwnerActive uTri vTri
      (muNegThreeZeroFiveCorrectDGraph G c u v) e.val = true := by
  dsimp only [muNegThreeZeroFiveCorrectOwnerActive]
  rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri e]
  by_cases he : e.val < 24
  · rw [muNegThreeZeroFiveCorrectGuard?_fixed uTri vTri e he]
  · have he24 : 24 ≤ e.val := by omega
    rw [muNegThreeZeroFiveCorrectGuard?_cross uTri vTri e he24]
    have hR : (exteriorPairGraph G c.supp).Adj
        (u ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 : ZMod 8))
        (v (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8 : Nat) :
          ZMod 8)) := by
      obtain ⟨h1, h2a, h2b⟩ :=
        muNegThreeZeroFiveCorrectOwner_cross_codes uTri vTri e he24
      have hfst : muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 =
          (u ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 :
            ZMod 8)).1 := by
        unfold muNegOneCodeVertex
        rw [if_pos h1]
      have hsnd : muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 =
          (v (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8 : Nat) :
            ZMod 8)).1 := by
        unfold muNegOneCodeVertex
        rw [if_neg (by omega)]
      refine ⟨?_,
        t, ht.1, by simpa [hfst] using ht.2.1,
        by simpa [hsnd] using ht.2.2⟩
      intro h
      exact shore_vertices_ne G c a b u v hab hurange hvrange _ _
        (congrArg Subtype.val h)
    unfold muNegThreeZeroFiveCorrectDGraph
    rw [Bool.not_not]
    exact decide_eq_true hR

theorem muNegThreeZeroFiveCorrect_ownerVertex_of_active
    (hfree : ¬ containsC4 V G)
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v)
    {e : Fin 88}
    (hact : muNegThreeZeroFiveCorrectOwnerActive uTri vTri
      (muNegThreeZeroFiveCorrectDGraph G c u v) e.val = true) :
    ∃ t : V, MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t ∧
      ∀ t' : V,
        G.Adj (muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1) t' →
        G.Adj (muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) t' → t' = t := by
  by_cases he12 : e.val < 12
  · exact muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj G c u v uTri vTri
      hfree e (muNegThreeZeroFiveCorrectOwner_R_adj_left G c u v uTri vTri
        hmodeu e he12)
  · by_cases he24 : e.val < 24
    · exact muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj G c u v uTri vTri
        hfree e (muNegThreeZeroFiveCorrectOwner_R_adj_right G c u v uTri vTri
          hmodev e (by omega) he24)
    · have he : 24 ≤ e.val := by omega
      have hR : (exteriorPairGraph G c.supp).Adj
          (u ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 : ZMod 8))
          (v (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8 : Nat) :
            ZMod 8)) := by
        dsimp only [muNegThreeZeroFiveCorrectOwnerActive] at hact
        rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri e] at hact
        rw [muNegThreeZeroFiveCorrectGuard?_cross uTri vTri e he] at hact
        unfold muNegThreeZeroFiveCorrectDGraph at hact
        rw [Bool.not_not] at hact
        exact of_decide_eq_true hact
      exact muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj G c u v uTri vTri
        hfree e (muNegThreeZeroFiveCorrectOwner_R_adj_cross G c u v
          uTri vTri e he hR)

end Activity

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerActive_of_ownerVertex
#print axioms Erdos85.muNegThreeZeroFiveCorrect_ownerVertex_of_active
