import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf
import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85MuNegOneOneFourOwnerRealization

/-!
# Graph realization for the honest h305 owner table

This file starts the graph-to-CNF transport for the corrected 88-owner
encoding.  In particular it realizes the eight antipodal shore owners which
are absent from the old 80-owner h114 table.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

theorem muNegThreeZeroFiveCorrectOwners_length (uTri vTri : Bool) :
    (muNegThreeZeroFiveCorrectOwners uTri vTri).length = 88 := by
  cases uTri <;> cases vTri <;> decide

/-- The owner pair at a typed index in the corrected table. -/
def muNegThreeZeroFiveCorrectOwnerAt (uTri vTri : Bool) (e : Fin 88) :
    Nat × Nat :=
  (muNegThreeZeroFiveCorrectOwners uTri vTri)[e.val]'(by
    rw [muNegThreeZeroFiveCorrectOwners_length]
    exact e.isLt)

theorem muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen :
    ∀ (uTri vTri : Bool) (e : Fin 88),
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 < 16 ∧
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 < 16 := by
  decide

theorem muNegThreeZeroFiveCorrectOwnerAt_fst_lt_snd :
    ∀ (uTri vTri : Bool) (e : Fin 88),
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 <
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 := by
  decide

set_option maxRecDepth 5000 in
theorem muNegThreeZeroFiveCorrectOwnerAt_injective :
    ∀ (uTri vTri : Bool) (e f : Fin 88),
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri e =
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f → e = f := by
  decide

theorem muNegThreeZeroFiveCorrectOwnerAt_left_bounds :
    ∀ (uTri vTri : Bool) (e : Fin 88), e.val < 12 →
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 < 8 ∧
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 < 8 := by
  decide

theorem muNegThreeZeroFiveCorrectOwnerAt_right_bounds :
    ∀ (uTri vTri : Bool) (e : Fin 88), 12 ≤ e.val → e.val < 24 →
      (8 ≤ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 ∧
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 < 16) ∧
      (8 ≤ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 ∧
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 < 16) := by
  decide

theorem muNegThreeZeroFiveCorrectOwnerAt_left_diff :
    ∀ (uTri vTri : Bool) (e : Fin 88), e.val < 12 →
      let d := ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 : ZMod 8) -
        ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 : ZMod 8)
      (if uTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) := by
  decide

theorem muNegThreeZeroFiveCorrectOwnerAt_right_diff :
    ∀ (uTri vTri : Bool) (e : Fin 88), 12 ≤ e.val → e.val < 24 →
      let d :=
        (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8) -
        (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 - 8 : Nat) : ZMod 8)
      (if vTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) := by
  decide

theorem muNegThreeZeroFiveCorrectOwner_cross_codes :
    ∀ (uTri vTri : Bool) (e : Fin 88), 24 ≤ e.val →
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 < 8 ∧
      8 ≤ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 ∧
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 < 16 := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- A graph owner vertex for the corrected owner table. -/
def MuNegThreeZeroFiveCorrectOwnerVertex (u v : ZMod 8 → c.supp)
    (uTri vTri : Bool) (e : Fin 88) (t : V) : Prop :=
  t ∉ c.supp ∧
    G.Adj (muNegOneCodeVertex G c u v
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1) t ∧
    G.Adj (muNegOneCodeVertex G c u v
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) t

section Realization

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

theorem muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj
    (hfree : ¬ containsC4 V G) (e : Fin 88)
    (hR : (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2)) :
    ∃ t : V, MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t ∧
      ∀ t' : V,
        G.Adj (muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1) t' →
        G.Adj (muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) t' → t' = t := by
  obtain ⟨t, htout, htx, hty, huniq⟩ :=
    exteriorPairGraph_ownerVertex G hfree c.supp hR
  rw [muNegOneCodeSub_val] at htx huniq
  rw [muNegOneCodeSub_val] at hty huniq
  exact ⟨t, ⟨htout, htx, hty⟩, huniq⟩

theorem muNegThreeZeroFiveCorrectOwner_R_adj_left
    (hmode : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (e : Fin 88) (he : e.val < 12) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) := by
  obtain ⟨h1, h2⟩ :=
    muNegThreeZeroFiveCorrectOwnerAt_left_bounds uTri vTri e he
  have hd := muNegThreeZeroFiveCorrectOwnerAt_left_diff uTri vTri e he
  rw [muNegOneCodeSub, muNegOneCodeSub, if_pos h1, if_pos h2]
  cases uTri <;> exact (hmode _ _).mpr hd

theorem muNegThreeZeroFiveCorrectOwner_R_adj_right
    (hmode : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v)
    (e : Fin 88) (he12 : 12 ≤ e.val) (he : e.val < 24) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) := by
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ :=
    muNegThreeZeroFiveCorrectOwnerAt_right_bounds uTri vTri e he12 he
  have hd := muNegThreeZeroFiveCorrectOwnerAt_right_diff uTri vTri e he12 he
  rw [muNegOneCodeSub, muNegOneCodeSub, if_neg (by omega), if_neg (by omega)]
  cases vTri <;> exact (hmode _ _).mpr hd

theorem muNegThreeZeroFiveCorrectOwner_R_adj_cross
    (e : Fin 88) (he : 24 ≤ e.val)
    (hR : (exteriorPairGraph G c.supp).Adj
      (u ((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 : ZMod 8))
      (v (((muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8))) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2) := by
  obtain ⟨h1, h2a, h2b⟩ :=
    muNegThreeZeroFiveCorrectOwner_cross_codes uTri vTri e he
  rw [muNegOneCodeSub, muNegOneCodeSub, if_pos h1, if_neg (by omega)]
  exact hR

end Realization

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwner_R_adj_left
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwner_R_adj_right
