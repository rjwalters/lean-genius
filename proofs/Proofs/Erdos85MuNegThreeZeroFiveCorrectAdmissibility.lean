import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphRelations
import Proofs.Erdos85MuNegOneOneFourAdmissibility

/-! # Admissibility for the honest h305 owner table -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrectTwelve_contains_iff :
    ∀ (uTri vTri : Bool) (e : Fin 88) (w : Nat), w < 16 →
      ((muNegOneTwelve
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e)).contains w = true ↔
        (muNegOneGAdj
              (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 w = false ∧
          muNegOneGAdj
              (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 w = false ∧
          (muNegOneAdjacentPair
                (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e) = true →
            (w ≠ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 ∧
              w ≠ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2)))) := by
  decide

theorem mem_muNegThreeZeroFiveCorrectHitPairs_iff
    (uTri vTri : Bool) (a b : Nat) :
    (a, b) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri ↔
      a < 88 ∧ b < 88 ∧ a < b ∧
        muNegOneAdm
          ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!)
          ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) = true := by
  unfold muNegThreeZeroFiveCorrectHitPairs
  constructor
  · intro h
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, muNegThreeZeroFiveCorrectOwners_length,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨a', ha', b', ⟨⟨hb', hlt, hadm⟩, heq⟩⟩ := h
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨ha', hb', hlt, hadm⟩
  · rintro ⟨ha, hb, hab, hadm⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, muNegThreeZeroFiveCorrectOwners_length,
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

theorem muNegThreeZeroFiveCorrect_no_cross_endpoint_edge
    (hfree : ¬ containsC4 V G)
    {e f : Fin 88} {te tf : V}
    (hte : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf)
    {y x : Nat}
    (hy : y = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 ∨
      y = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2)
    (hx : x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).1 ∨
      x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).2) :
    ¬ G.Adj (muNegOneCodeVertex G c u v y)
      (muNegOneCodeVertex G c u v x) := by
  intro hedge
  have htey : G.Adj te (muNegOneCodeVertex G c u v y) := by
    rcases hy with rfl | rfl
    · exact hte.2.1.symm
    · exact hte.2.2.symm
  have htfx : G.Adj tf (muNegOneCodeVertex G c u v x) := by
    rcases hx with rfl | rfl
    · exact htf.2.1.symm
    · exact htf.2.2.symm
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

theorem muNegThreeZeroFiveCorrect_no_shared_endpoint_of_adjacentPair
    (hfree : ¬ containsC4 V G)
    {e f : Fin 88} {te tf : V}
    (hte : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf)
    (hpair : G.Adj
      (muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1)
      (muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2))
    {x : Nat}
    (hx : x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).1 ∨
      x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f).2) :
    x ≠ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 ∧
      x ≠ (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 := by
  have htfx : G.Adj tf (muNegOneCodeVertex G c u v x) := by
    rcases hx with rfl | rfl
    · exact htf.2.1.symm
    · exact htf.2.2.symm
  constructor
  · intro hx1
    have hne : tf ≠ muNegOneCodeVertex G c u v
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).2 := by
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
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e).1 := by
      intro h
      apply htf.1
      rw [h]
      exact muNegOneCodeVertex_mem_supp G c u v _
    have heq := commonServer_unique G hfree hne
      (by rw [← hx2]; exact htfx) hpair hadj.symm hte.2.1
    apply hte.1
    rw [← heq]
    exact muNegOneCodeVertex_mem_supp G c u v _

theorem muNegThreeZeroFiveCorrectAdm_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 88} (hef : e ≠ f) {te tf : V}
    (hte : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf) :
    muNegOneAdm (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e)
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f) = true := by
  have hcorr := muNegOneCodeVertex_adj_iff G c a b u v hab huinj hvinj
    hurange hvrange hu hv
  have htwelve : ∀ p q : Fin 88, ∀ tp tq : V,
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri p tp →
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri q tq →
      G.Adj tp tq →
      ∀ x : Nat, (x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri q).1 ∨
        x = (muNegThreeZeroFiveCorrectOwnerAt uTri vTri q).2) →
      (muNegOneTwelve
        (muNegThreeZeroFiveCorrectOwnerAt uTri vTri p)).contains x = true := by
    intro p q tp tq htp htq hpq x hx
    have hxb : x < 16 := by
      have hb := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri q
      rcases hx with rfl | rfl <;> omega
    rw [muNegThreeZeroFiveCorrectTwelve_contains_iff uTri vTri p x hxb]
    have hbP := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri p
    refine ⟨?_, ?_, ?_⟩
    · by_contra hg
      rw [Bool.not_eq_false] at hg
      exact muNegThreeZeroFiveCorrect_no_cross_endpoint_edge G c u v
        uTri vTri hfree htp htq hpq (Or.inl rfl) hx
        ((hcorr _ (by omega) _ (by omega)).mpr hg)
    · by_contra hg
      rw [Bool.not_eq_false] at hg
      exact muNegThreeZeroFiveCorrect_no_cross_endpoint_edge G c u v
        uTri vTri hfree htp htq hpq (Or.inr rfl) hx
        ((hcorr _ (by omega) _ (by omega)).mpr hg)
    · intro hadjP
      have hpairP : G.Adj
          (muNegOneCodeVertex G c u v
            (muNegThreeZeroFiveCorrectOwnerAt uTri vTri p).1)
          (muNegOneCodeVertex G c u v
            (muNegThreeZeroFiveCorrectOwnerAt uTri vTri p).2) :=
        (hcorr _ (by omega) _ (by omega)).mpr hadjP
      exact muNegThreeZeroFiveCorrect_no_shared_endpoint_of_adjacentPair
        G c u v uTri vTri hfree htp htq hpq hpairP hx
  have hne : muNegThreeZeroFiveCorrectOwnerAt uTri vTri e ≠
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri f :=
    fun h => hef
      (muNegThreeZeroFiveCorrectOwnerAt_injective uTri vTri e f h)
  unfold muNegOneAdm
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨bne_iff_ne.mpr hne,
    htwelve e f te tf hte htf hadj _ (Or.inl rfl)⟩,
    htwelve e f te tf hte htf hadj _ (Or.inr rfl)⟩,
    htwelve f e tf te htf hte hadj.symm _ (Or.inl rfl)⟩,
    htwelve f e tf te htf hte hadj.symm _ (Or.inr rfl)⟩

theorem mem_muNegThreeZeroFiveCorrectHitPairs_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {e f : Fin 88} (hef : e.val < f.val) {te tf : V}
    (hte : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e te)
    (htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf)
    (hadj : G.Adj te tf) :
    (e.val, f.val) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri := by
  rw [mem_muNegThreeZeroFiveCorrectHitPairs_iff]
  refine ⟨e.2, f.2, hef, ?_⟩
  have h := muNegThreeZeroFiveCorrectAdm_of_ownerVertices_adj G c u v
    uTri vTri hfree a b hab huinj hvinj hurange hvrange hu hv
    (e := e) (f := f) (by intro h; rw [h] at hef; omega) hte htf hadj
  have he : (muNegThreeZeroFiveCorrectOwners uTri vTri)[e.val]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri e := by
    have he' : e.val < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
      rw [muNegThreeZeroFiveCorrectOwners_length]
      exact e.isLt
    rw [getElem!_pos (c := muNegThreeZeroFiveCorrectOwners uTri vTri)
      (i := e.val) he']
    rfl
  have hf : (muNegThreeZeroFiveCorrectOwners uTri vTri)[f.val]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri f := by
    have hf' : f.val < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
      rw [muNegThreeZeroFiveCorrectOwners_length]
      exact f.isLt
    rw [getElem!_pos (c := muNegThreeZeroFiveCorrectOwners uTri vTri)
      (i := f.val) hf']
    rfl
  rw [he, hf]
  exact h

end Admissibility

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectAdm_of_ownerVertices_adj
#print axioms Erdos85.mem_muNegThreeZeroFiveCorrectHitPairs_of_ownerVertices_adj
