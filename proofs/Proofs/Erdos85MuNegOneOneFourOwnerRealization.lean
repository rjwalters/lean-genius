import Proofs.Erdos85MuNegOneOneFourCodeVertexMap
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourModeRouting

/-!
# Owner realization for the μ=-1 `(1,4)` grid

Node: outline F.3 (bridge increment 3c-ii-c; squad msgs 14013/14046).

Realizes the generator's eighty typed owners as graph objects: under
the canonical shore modes, every within-shore owner pair is an
exterior-pair edge, an active cross owner is exactly an exterior-pair
cross cell, and each such owner has a unique exterior *owner vertex*
adjacent to both endpoints.  The service and C4 instantiations read the
hit relation `X` through these owner vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

/-- Within-shore owner endpoints of the first shore stay below eight. -/
theorem muNegOneOwnerAt_left_bounds :
    ∀ (uTri vTri : Bool) (e : Fin 80), e.val < 8 →
      (muNegOneOwnerAt uTri vTri e).1 < 8 ∧
        (muNegOneOwnerAt uTri vTri e).2 < 8 := by
  decide

/-- Within-shore owner endpoints of the second shore live in `8..15`. -/
theorem muNegOneOwnerAt_right_bounds :
    ∀ (uTri vTri : Bool) (e : Fin 80), 8 ≤ e.val → e.val < 16 →
      (8 ≤ (muNegOneOwnerAt uTri vTri e).1 ∧
        (muNegOneOwnerAt uTri vTri e).1 < 16) ∧
      (8 ≤ (muNegOneOwnerAt uTri vTri e).2 ∧
        (muNegOneOwnerAt uTri vTri e).2 < 16) := by
  decide

set_option maxRecDepth 4000 in
/-- The ordered owner table has no duplicates. -/
theorem muNegOneOwnerAt_injective :
    ∀ (uTri vTri : Bool) (e f : Fin 80),
      muNegOneOwnerAt uTri vTri e = muNegOneOwnerAt uTri vTri f → e = f := by
  decide

/-- Every owner pair is strictly ordered. -/
theorem muNegOneOwnerAt_fst_lt_snd :
    ∀ (uTri vTri : Bool) (e : Fin 80),
      (muNegOneOwnerAt uTri vTri e).1 < (muNegOneOwnerAt uTri vTri e).2 := by
  decide

/-- First-shore owner offsets match the mode: the cyclic difference of
the endpoints is the mode offset or its negation. -/
theorem muNegOneOwnerAt_left_diff :
    ∀ (uTri vTri : Bool) (e : Fin 80), e.val < 8 →
      ((((muNegOneOwnerAt uTri vTri e).2 : ZMod 8) -
          ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8) =
            (if uTri then 1 else 3)) ∨
        (((muNegOneOwnerAt uTri vTri e).2 : ZMod 8) -
          ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8) =
            (if uTri then 7 else 5))) := by
  decide

/-- Second-shore owner offsets match the mode on shifted coordinates. -/
theorem muNegOneOwnerAt_right_diff :
    ∀ (uTri vTri : Bool) (e : Fin 80), 8 ≤ e.val → e.val < 16 →
      (((((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8) -
          (((muNegOneOwnerAt uTri vTri e).1 - 8 : Nat) : ZMod 8) =
            (if vTri then 1 else 3)) ∨
        ((((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8) -
          (((muNegOneOwnerAt uTri vTri e).1 - 8 : Nat) : ZMod 8) =
            (if vTri then 7 else 5))) := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- Subtype-valued code map. -/
def muNegOneCodeSub (u v : ZMod 8 → c.supp) (x : Nat) : c.supp :=
  if x < 8 then u (x : ZMod 8) else v (((x - 8 : Nat) : ZMod 8))

theorem muNegOneCodeSub_val (u v : ZMod 8 → c.supp) (x : Nat) :
    (muNegOneCodeSub G c u v x).1 = muNegOneCodeVertex G c u v x := by
  unfold muNegOneCodeSub muNegOneCodeVertex
  split <;> rfl

/-- A graph owner vertex for a typed owner index. -/
def MuNegOneOwnerVertex (u v : ZMod 8 → c.supp) (uTri vTri : Bool)
    (e : Fin 80) (t : V) : Prop :=
  t ∉ c.supp ∧
    G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1) t ∧
    G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2) t

section Realization

variable [DecidableEq (G.induce c.supp).ConnectedComponent]
  (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

/-- Owner realization from an exterior-pair edge between the two code
endpoints. -/
theorem muNegOneOwnerVertex_of_R_adj
    (hfree : ¬ containsC4 V G) (e : Fin 80)
    (hR : (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).2)) :
    ∃ t : V, MuNegOneOwnerVertex G c u v uTri vTri e t ∧
      ∀ t' : V,
        G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1) t' →
        G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2) t' →
        t' = t := by
  obtain ⟨t, htout, htx, hty, huniq⟩ :=
    exteriorPairGraph_ownerVertex G hfree c.supp hR
  rw [muNegOneCodeSub_val] at htx huniq
  rw [muNegOneCodeSub_val] at hty huniq
  exact ⟨t, ⟨htout, htx, hty⟩, huniq⟩

/-- The first-shore owners are exterior-pair edges under the shore
mode. -/
theorem muNegOneOwner_R_adj_left
    (hmode : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (e : Fin 80) (he : e.val < 8) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).2) := by
  obtain ⟨h1, h2⟩ := muNegOneOwnerAt_left_bounds uTri vTri e he
  have hdiff := muNegOneOwnerAt_left_diff uTri vTri e he
  rw [muNegOneCodeSub, muNegOneCodeSub, if_pos h1, if_pos h2]
  cases uTri
  · exact (hmode _ _).mpr hdiff
  · exact (hmode _ _).mpr hdiff

/-- The second-shore owners are exterior-pair edges under the shore
mode. -/
theorem muNegOneOwner_R_adj_right
    (hmode : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v)
    (e : Fin 80) (he8 : 8 ≤ e.val) (he : e.val < 16) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).2) := by
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ :=
    muNegOneOwnerAt_right_bounds uTri vTri e he8 he
  have hdiff := muNegOneOwnerAt_right_diff uTri vTri e he8 he
  rw [muNegOneCodeSub, muNegOneCodeSub,
    if_neg (by omega), if_neg (by omega)]
  cases vTri
  · exact (hmode _ _).mpr hdiff
  · exact (hmode _ _).mpr hdiff

/-- Cross owners in explicit coordinates: the code pair of a cross
owner names one first-shore and one second-shore vertex. -/
theorem muNegOneOwner_cross_codes (e : Fin 80) (he : 16 ≤ e.val) :
    (muNegOneOwnerAt uTri vTri e).1 < 8 ∧
      8 ≤ (muNegOneOwnerAt uTri vTri e).2 ∧
      (muNegOneOwnerAt uTri vTri e).2 < 16 := by
  revert uTri vTri e
  decide

/-- An active cross owner (exterior-pair adjacent across the shores) is
realized. -/
theorem muNegOneOwner_R_adj_cross
    (e : Fin 80) (he : 16 ≤ e.val)
    (hact : (exteriorPairGraph G c.supp).Adj
      (u ((muNegOneOwnerAt uTri vTri e).1 : ZMod 8))
      (v (((muNegOneOwnerAt uTri vTri e).2 - 8 : Nat) : ZMod 8))) :
    (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).1)
      (muNegOneCodeSub G c u v (muNegOneOwnerAt uTri vTri e).2) := by
  obtain ⟨h1, h2a, h2b⟩ := muNegOneOwner_cross_codes uTri vTri e he
  rw [muNegOneCodeSub, muNegOneCodeSub, if_pos h1, if_neg (by omega)]
  exact hact

/-- The two code endpoints of any owner are distinct vertices. -/
theorem muNegOneOwner_endpoints_ne
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 80) :
    muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1 ≠
      muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2 := by
  intro h
  have hlt := muNegOneOwnerAt_fst_lt_snd uTri vTri e
  have hbound := muNegOneOwnerAt_lt_sixteen uTri vTri e
  have := muNegOneCodeVertex_inj G c a b u v hab huinj hvinj hurange hvrange
    (muNegOneOwnerAt uTri vTri e).1 (by omega)
    (muNegOneOwnerAt uTri vTri e).2 (by omega) h
  omega

/-- Owner vertices are unique. -/
theorem muNegOneOwnerVertex_unique
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (e : Fin 80) {t t' : V}
    (ht : MuNegOneOwnerVertex G c u v uTri vTri e t)
    (ht' : MuNegOneOwnerVertex G c u v uTri vTri e t') : t = t' :=
  commonServer_unique G hfree
    (muNegOneOwner_endpoints_ne G c u v uTri vTri a b hab
      huinj hvinj hurange hvrange e)
    ht.2.1 ht.2.2 ht'.2.1 ht'.2.2

/-- Owner vertices determine the owner: two owners sharing an owner
vertex have equal code pairs, hence equal indices. -/
theorem muNegOneOwnerVertex_inj
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (hsize : c.supp.ncard = q * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {e f : Fin 80} {t : V}
    (ht : MuNegOneOwnerVertex G c u v uTri vTri e t)
    (ht' : MuNegOneOwnerVertex G c u v uTri vTri f t) : e = f := by
  have hboundE := muNegOneOwnerAt_lt_sixteen uTri vTri e
  have hboundF := muNegOneOwnerAt_lt_sixteen uTri vTri f
  have hpair := ownerVertex_pair_eq G hfree hq hreg hcard c hsize
    (muNegOneOwner_endpoints_ne G c u v uTri vTri a b hab
      huinj hvinj hurange hvrange e)
    (muNegOneOwner_endpoints_ne G c u v uTri vTri a b hab
      huinj hvinj hurange hvrange f)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    (muNegOneCodeVertex_mem_supp G c u v _)
    ht.2.1.symm ht.2.2.symm ht'.2.1.symm ht'.2.2.symm
  -- unordered pair equality on distinct code vertices gives the two
  -- code equalities in order, by the strict ordering of pairs.
  have hlt := muNegOneOwnerAt_fst_lt_snd uTri vTri e
  have hltf := muNegOneOwnerAt_fst_lt_snd uTri vTri f
  have hinj := muNegOneCodeVertex_inj G c a b u v hab huinj hvinj
    hurange hvrange
  have hf1 : muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri f).1 ∈
      ({muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1,
        muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2} :
          Finset V) := by
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hf2 : muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri f).2 ∈
      ({muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1,
        muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2} :
          Finset V) := by
    rw [hpair]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  have hf1' := Finset.mem_insert.mp hf1
  have hf2' := Finset.mem_insert.mp hf2
  rw [Finset.mem_singleton] at hf1' hf2'
  have hpairs : (muNegOneOwnerAt uTri vTri e).1 =
      (muNegOneOwnerAt uTri vTri f).1 ∧
      (muNegOneOwnerAt uTri vTri e).2 = (muNegOneOwnerAt uTri vTri f).2 := by
    rcases hf1' with h1 | h1 <;> rcases hf2' with h2 | h2
    · have hff := hinj _ (by omega) _ (by omega) (h1.trans h2.symm)
      omega
    · exact ⟨(hinj _ (by omega) _ (by omega) h1).symm,
        (hinj _ (by omega) _ (by omega) h2).symm⟩
    · have e1 := hinj _ (by omega) _ (by omega) h1
      have e2 := hinj _ (by omega) _ (by omega) h2
      omega
    · have hff := hinj _ (by omega) _ (by omega) (h1.trans h2.symm)
      omega
  exact muNegOneOwnerAt_injective uTri vTri e f
    (Prod.ext hpairs.1 hpairs.2)

end Realization

end

end Erdos85

#print axioms Erdos85.muNegOneOwnerVertex_of_R_adj
#print axioms Erdos85.muNegOneOwner_R_adj_left
#print axioms Erdos85.muNegOneOwner_R_adj_right
#print axioms Erdos85.muNegOneOwnerVertex_inj
