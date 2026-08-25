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

theorem muNegThreeZeroFiveCorrectOwner_endpoints_ne
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 88) :
    muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 ≠
      muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 := by
  intro h
  have hlt := muNegThreeZeroFiveCorrectOwnerAt_fst_lt_snd uTri vTri e
  have hb := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri e
  have heq := muNegOneCodeVertex_inj G c a b u v hab huinj hvinj
    hurange hvrange _ hb.1 _ hb.2 h
  omega

theorem muNegThreeZeroFiveCorrectOwnerVertex_unique
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 88) {t t' : V}
    (ht : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t)
    (ht' : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t') :
    t = t' :=
  commonServer_unique G hfree
    (muNegThreeZeroFiveCorrectOwner_endpoints_ne G c u v uTri vTri
      a b hab huinj hvinj hurange hvrange e)
    ht.2.1 ht.2.2 ht'.2.1 ht'.2.2

theorem muNegThreeZeroFiveCorrectOwnerVertex_inj
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (hsize : c.supp.ncard = q * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e f : Fin 88} {t : V}
    (ht : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e t)
    (ht' : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f t) :
    e = f := by
  have hbE := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri e
  have hbF := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri f
  have hpair := ownerVertex_pair_eq G hfree hq hreg hcard c hsize
    (muNegThreeZeroFiveCorrectOwner_endpoints_ne G c u v uTri vTri
      a b hab huinj hvinj hurange hvrange e)
    (muNegThreeZeroFiveCorrectOwner_endpoints_ne G c u v uTri vTri
      a b hab huinj hvinj hurange hvrange f)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    ht.2.1.symm ht.2.2.symm ht'.2.1.symm ht'.2.2.symm
  have hltE := muNegThreeZeroFiveCorrectOwnerAt_fst_lt_snd uTri vTri e
  have hltF := muNegThreeZeroFiveCorrectOwnerAt_fst_lt_snd uTri vTri f
  have hinj := muNegOneCodeVertex_inj G c a b u v hab huinj hvinj
    hurange hvrange
  have hf1 : muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).1 ∈
      ({muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1,
        muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2} : Finset V) := by
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hf2 : muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).2 ∈
      ({muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1,
        muNegOneCodeVertex G c u v
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2} : Finset V) := by
    rw [hpair]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hf1' := Finset.mem_insert.mp hf1
  have hf2' := Finset.mem_insert.mp hf2
  rw [Finset.mem_singleton] at hf1' hf2'
  have hpairs :
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 =
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).1 ∧
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 =
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).2 := by
    rcases hf1' with h1 | h1 <;> rcases hf2' with h2 | h2
    · have hff := hinj _ hbF.1 _ hbF.2 (h1.trans h2.symm)
      omega
    · exact ⟨(hinj _ hbF.1 _ hbE.1 h1).symm,
        (hinj _ hbF.2 _ hbE.2 h2).symm⟩
    · have e1 := hinj _ hbF.1 _ hbE.2 h1
      have e2 := hinj _ hbF.2 _ hbE.1 h2
      omega
    · have hff := hinj _ hbF.1 _ hbF.2 (h1.trans h2.symm)
      omega
  exact muNegThreeZeroFiveCorrectOwnerAt_injective uTri vTri e f
    (Prod.ext hpairs.1 hpairs.2)

end Realization

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerVertex_of_R_adj
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwner_R_adj_left
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwner_R_adj_right
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerVertex_inj
