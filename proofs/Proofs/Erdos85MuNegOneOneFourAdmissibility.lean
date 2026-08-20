import Proofs.Erdos85MuNegOneOneFourOwnerRealization

/-!
# Admissibility of served owner pairs in the μ=-1 `(1,4)` grid

Node: outline F.3 (bridge increment 3c-ii-d; squad msg 14056).

The owner CNFs only carry hit variables for *admissible* owner pairs —
each owner's pair inside the other's twelve-set.  This file proves the
geometric fact that makes the encoding faithful: adjacent owner
vertices force admissibility.  Both failure shapes produce a C4 through
the two owner vertices (via an internal octagon edge, or via the
internal edge of a triangle-mode pair), collapsing to the
common-server uniqueness law.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

set_option maxRecDepth 10000 in
/-- Boolean characterization of the generator's twelve-set. -/
theorem muNegOneTwelve_contains_iff :
    ∀ (uTri vTri : Bool) (e : Fin 80) (w : Nat), w < 16 →
      ((muNegOneTwelve (muNegOneOwnerAt uTri vTri e)).contains w = true ↔
        (muNegOneGAdj (muNegOneOwnerAt uTri vTri e).1 w = false ∧
          muNegOneGAdj (muNegOneOwnerAt uTri vTri e).2 w = false ∧
          (muNegOneAdjacentPair (muNegOneOwnerAt uTri vTri e) = true →
            (w ≠ (muNegOneOwnerAt uTri vTri e).1 ∧
              w ≠ (muNegOneOwnerAt uTri vTri e).2)))) := by
  decide

/-- Structural membership law for the admissible hit-pair table. -/
theorem mem_muNegOneHitPairs_iff (uTri vTri : Bool) (a b : Nat) :
    (a, b) ∈ muNegOneHitPairs uTri vTri ↔
      a < 80 ∧ b < 80 ∧ a < b ∧
        muNegOneAdm ((muNegOneOwners uTri vTri)[a]!)
          ((muNegOneOwners uTri vTri)[b]!) = true := by
  unfold muNegOneHitPairs
  constructor
  · intro h
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, List.mem_range, muNegOneOwners_length,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨a', ha', b', ⟨⟨hb', hlt, hadm⟩, heq⟩⟩ := h
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨ha', hb', hlt, hadm⟩
  · rintro ⟨ha, hb, hab, hadm⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, List.mem_range, muNegOneOwners_length,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨a, ha, b, ⟨⟨hb, hab, hadm⟩, rfl⟩⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

section Admissibility

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

/-- No endpoint of one owner is ambient-adjacent to an endpoint of an
owner-vertex-adjacent partner: such an edge closes a C4 through the two
owner vertices. -/
theorem muNegOne_no_cross_endpoint_edge
    (hfree : ¬ containsC4 V G)
    {e f : Fin 80} {te tf : V}
    (hte : MuNegOneOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegOneOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf)
    {y x : Nat}
    (hy : y = (muNegOneOwnerAt uTri vTri e).1 ∨
      y = (muNegOneOwnerAt uTri vTri e).2)
    (hx : x = (muNegOneOwnerAt uTri vTri f).1 ∨
      x = (muNegOneOwnerAt uTri vTri f).2) :
    ¬ G.Adj (muNegOneCodeVertex G c u v y) (muNegOneCodeVertex G c u v x) := by
  intro hedge
  have htey : G.Adj te (muNegOneCodeVertex G c u v y) := by
    rcases hy with rfl | rfl
    · exact hte.2.1.symm
    · exact hte.2.2.symm
  have htfx : G.Adj tf (muNegOneCodeVertex G c u v x) := by
    rcases hx with rfl | rfl
    · exact htf.2.1.symm
    · exact htf.2.2.symm
  -- `cv y` and `tf` are two common neighbors of `te` and `cv x`.
  have hne : te ≠ muNegOneCodeVertex G c u v x := by
    intro h
    apply hte.1
    rw [h]
    exact muNegOneCodeVertex_mem_supp G c u v x
  have heq := commonServer_unique G hfree hne
    htey hedge.symm hadj htfx.symm
  apply htf.1
  rw [← heq]
  exact muNegOneCodeVertex_mem_supp G c u v y

/-- A triangle-mode partner cannot share an endpoint with an
owner-vertex-adjacent owner: the shared endpoint closes a C4 through
the partner's internal edge. -/
theorem muNegOne_no_shared_endpoint_of_adjacentPair
    (hfree : ¬ containsC4 V G)
    {e f : Fin 80} {te tf : V}
    (hte : MuNegOneOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegOneOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf)
    (hpair : G.Adj (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).1)
      (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri e).2))
    {x : Nat}
    (hx : x = (muNegOneOwnerAt uTri vTri f).1 ∨
      x = (muNegOneOwnerAt uTri vTri f).2) :
    x ≠ (muNegOneOwnerAt uTri vTri e).1 ∧
      x ≠ (muNegOneOwnerAt uTri vTri e).2 := by
  have htfx : G.Adj tf (muNegOneCodeVertex G c u v x) := by
    rcases hx with rfl | rfl
    · exact htf.2.1.symm
    · exact htf.2.2.symm
  constructor
  · intro hx1
    -- common neighbors of `tf` and `cv e.2`: `cv e.1` and `te`.
    have hne : tf ≠ muNegOneCodeVertex G c u v
        (muNegOneOwnerAt uTri vTri e).2 := by
      intro h
      apply htf.1
      rw [h]
      exact muNegOneCodeVertex_mem_supp G c u v _
    have heq := commonServer_unique G hfree hne
      (by rw [← hx1]; exact htfx) hpair.symm hadj.symm hte.2.2
    apply hte.1
    rw [← heq]
    exact muNegOneCodeVertex_mem_supp G c u v _
  · intro hx2
    have hne : tf ≠ muNegOneCodeVertex G c u v
        (muNegOneOwnerAt uTri vTri e).1 := by
      intro h
      apply htf.1
      rw [h]
      exact muNegOneCodeVertex_mem_supp G c u v _
    have heq := commonServer_unique G hfree hne
      (by rw [← hx2]; exact htfx) hpair hadj.symm hte.2.1
    apply hte.1
    rw [← heq]
    exact muNegOneCodeVertex_mem_supp G c u v _

/-- **Adjacent owner vertices force admissibility.** -/
theorem muNegOneAdm_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 80} (hef : e ≠ f) {te tf : V}
    (hte : MuNegOneOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegOneOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf) :
    muNegOneAdm (muNegOneOwnerAt uTri vTri e)
      (muNegOneOwnerAt uTri vTri f) = true := by
  have hcorr := muNegOneCodeVertex_adj_iff G c a b u v hab huinj hvinj
    hurange hvrange hu hv
  have hboundE := muNegOneOwnerAt_lt_sixteen uTri vTri e
  have hboundF := muNegOneOwnerAt_lt_sixteen uTri vTri f
  -- each endpoint of one owner lies in the other's twelve-set.
  have htwelve : ∀ p q : Fin 80, ∀ tp tq : V,
      MuNegOneOwnerVertex G c u v uTri vTri p tp →
      MuNegOneOwnerVertex G c u v uTri vTri q tq →
      G.Adj tp tq →
      ∀ x : Nat, (x = (muNegOneOwnerAt uTri vTri q).1 ∨
        x = (muNegOneOwnerAt uTri vTri q).2) →
      (muNegOneTwelve (muNegOneOwnerAt uTri vTri p)).contains x = true := by
    intro p q tp tq htp htq hpq x hx
    have hxbound : x < 16 := by
      have := muNegOneOwnerAt_lt_sixteen uTri vTri q
      rcases hx with rfl | rfl <;> omega
    rw [muNegOneTwelve_contains_iff uTri vTri p x hxbound]
    have hboundP := muNegOneOwnerAt_lt_sixteen uTri vTri p
    refine ⟨?_, ?_, ?_⟩
    · by_contra hg
      rw [Bool.not_eq_false] at hg
      exact muNegOne_no_cross_endpoint_edge G c u v uTri vTri hfree
        htp htq hpq (Or.inl rfl) hx
        ((hcorr _ (by omega) _ (by omega)).mpr hg)
    · by_contra hg
      rw [Bool.not_eq_false] at hg
      exact muNegOne_no_cross_endpoint_edge G c u v uTri vTri hfree
        htp htq hpq (Or.inr rfl) hx
        ((hcorr _ (by omega) _ (by omega)).mpr hg)
    · intro hadjP
      have hpairP : G.Adj
          (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri p).1)
          (muNegOneCodeVertex G c u v (muNegOneOwnerAt uTri vTri p).2) :=
        (hcorr _ (by omega) _ (by omega)).mpr hadjP
      exact muNegOne_no_shared_endpoint_of_adjacentPair G c u v uTri vTri
        hfree htp htq hpq hpairP hx
  have hne : muNegOneOwnerAt uTri vTri e ≠ muNegOneOwnerAt uTri vTri f :=
    fun h => hef (muNegOneOwnerAt_injective uTri vTri e f h)
  unfold muNegOneAdm
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨bne_iff_ne.mpr hne,
    htwelve e f te tf hte htf hadj _ (Or.inl rfl)⟩,
    htwelve e f te tf hte htf hadj _ (Or.inr rfl)⟩,
    htwelve f e tf te htf hte hadj.symm _ (Or.inl rfl)⟩,
    htwelve f e tf te htf hte hadj.symm _ (Or.inr rfl)⟩

/-- Adjacent owner vertices give a generated hit pair. -/
theorem mem_muNegOneHitPairs_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 80} (hef : e.val < f.val) {te tf : V}
    (hte : MuNegOneOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegOneOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf) :
    (e.val, f.val) ∈ muNegOneHitPairs uTri vTri := by
  rw [mem_muNegOneHitPairs_iff]
  refine ⟨e.2, f.2, hef, ?_⟩
  have := muNegOneAdm_of_ownerVertices_adj G c u v uTri vTri hfree
    a b hab huinj hvinj hurange hvrange hu hv
    (e := e) (f := f) (by intro h; rw [h] at hef; omega)
    hte htf hadj
  simpa [muNegOneOwnerAt] using this

end Admissibility

end

end Erdos85

#print axioms Erdos85.muNegOneTwelve_contains_iff
#print axioms Erdos85.mem_muNegOneHitPairs_iff
#print axioms Erdos85.muNegOne_no_cross_endpoint_edge
#print axioms Erdos85.muNegOne_no_shared_endpoint_of_adjacentPair
#print axioms Erdos85.muNegOneAdm_of_ownerVertices_adj
#print axioms Erdos85.mem_muNegOneHitPairs_of_ownerVertices_adj
