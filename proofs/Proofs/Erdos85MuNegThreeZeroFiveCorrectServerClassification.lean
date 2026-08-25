import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphActivity
import Proofs.Erdos85MuNegOneOneFourServerClassification

/-!
# Corrected h305 server classification

The first step is the exact completeness of the honest 88-owner table.  The
three lemmas below include the antipodal difference `4`, which is precisely
the case omitted by the old h114 table and its server-classification theorem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_within_left_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8), x.val < y.val →
      let d := (y.val : ZMod 8) - (x.val : ZMod 8)
      (if uTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) →
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f = (x.val, y.val) := by
  decide

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_within_right_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8), x.val < y.val →
      let d := (y.val : ZMod 8) - (x.val : ZMod 8)
      (if vTri then d = 1 ∨ d = 4 ∨ d = 7
       else d = 3 ∨ d = 4 ∨ d = 5) →
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f =
          (8 + x.val, 8 + y.val) := by
  decide

set_option maxRecDepth 12000 in
theorem muNegThreeZeroFiveCorrect_cross_mem_table :
    ∀ (uTri vTri : Bool) (x y : Fin 8),
      ∃ f : Fin 88,
        muNegThreeZeroFiveCorrectOwnerAt uTri vTri f =
          (x.val, 8 + y.val) := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

theorem muNegThreeZeroFiveCorrect_server_classification
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (uTri vTri : Bool)
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v)
    {e : Fin 88} {te : V}
    (hte : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri e te)
    {w : Nat} (hw16 : w < 16)
    (hw : (muNegOneTwelve (muNegThreeZeroFiveCorrectOwnerAt uTri vTri e)).contains w = true) :
    ∃ f : Fin 88, f ≠ e ∧ ∃ tf : V,
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf ∧ G.Adj te tf ∧
      muNegOnePairMem (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f) w = true := by
  classical
  have hcorr := muNegOneCodeVertex_adj_iff G c a b u v hab huinj hvinj
    hurange hvrange hu hv
  have hboundE := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen uTri vTri e
  obtain ⟨hg1, hg2, _⟩ :=
    (muNegThreeZeroFiveCorrectTwelve_contains_iff uTri vTri e w hw16).mp hw
  set cw := muNegOneCodeVertex G c u v w with hcw
  have hcwmem : cw ∈ c.supp := muNegOneCodeVertex_mem_supp G c u v w
  -- the unique ambient server of the exterior-internal pair (te, cw).
  have hteout : (secondOrderDefectGraph G).connectedComponentMk te ≠ c := by
    intro h
    exact hte.1 ((SimpleGraph.ConnectedComponent.mem_supp_iff c te).mpr h)
  have hcwin : (secondOrderDefectGraph G).connectedComponentMk cw = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c cw).mp hcwmem
  obtain ⟨z, ⟨htez, hzcw⟩, huniq⟩ :=
    binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
      G hfree (by omega) hreg hcard c hc hteout hcwin
  -- the server cannot be internal: it would be an owner endpoint
  -- octagon-adjacent to a twelve-set target.
  have hzout : z ∉ c.supp := by
    intro hzc
    have hztile := sizeTwoPart_server_mem_tile_of_internal G c htez hzc
    have hpairE := sizeTwoPart_tile_eq_pair G hfree (by omega : 3 ≤ 8)
      hreg hcard c hc
      (muNegThreeZeroFiveCorrectOwner_endpoints_ne G c u v uTri vTri a b hab
        huinj hvinj hurange hvrange e)
      (muNegOneCodeVertex_mem_supp G c u v _)
      (muNegOneCodeVertex_mem_supp G c u v _)
      hte.2.1.symm hte.2.2.symm
    rw [hpairE] at hztile
    rcases Finset.mem_insert.mp hztile with rfl | hz2
    · have hadj := (hcorr _ (by omega) _ (by omega)).mp hzcw
      rw [hadj] at hg1
      exact Bool.true_eq_false ▸ hg1.symm ▸ rfl
    · rw [Finset.mem_singleton] at hz2
      subst hz2
      have hadj := (hcorr _ (by omega) _ (by omega)).mp hzcw
      rw [hadj] at hg2
      exact Bool.true_eq_false ▸ hg2.symm ▸ rfl
  -- the server's tile is a coded pair containing the target.
  have hcwtile := sizeTwoPart_server_mem_tile_of_internal G c hzcw hcwmem
  have htile2 := sizeTwoPart_tile_card_two G hfree (by omega : 3 ≤ 8)
    hreg hcard c hc z
  obtain ⟨w', hw'tile, hw'ne⟩ : ∃ w' ∈ componentNeighborFinset G
      (secondOrderDefectGraph G) c z, w' ≠ cw := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (componentNeighborFinset G
        (secondOrderDefectGraph G) c z).card)
    by_cases hpcw : p = cw
    · exact ⟨q, hq, by rw [← hpcw]; exact hpq.symm⟩
    · exact ⟨p, hp, hpcw⟩
  have hw'data : G.Adj z w' ∧ w' ∈ c.supp := by
    rw [componentNeighborFinset, Finset.mem_filter,
      mem_neighborFinset] at hw'tile
    exact ⟨hw'tile.1, (SimpleGraph.ConnectedComponent.mem_supp_iff
      c w').mpr hw'tile.2⟩
  obtain ⟨wc, hwc16, hwceq⟩ := muNegOneCodeSub_surjective G c hc a b hab
    u v huinj hvinj hurange hvrange ⟨w', hw'data.2⟩
  have hwcv : muNegOneCodeVertex G c u v wc = w' := by
    rw [← muNegOneCodeSub_val, hwceq]
  have hwcne : wc ≠ w := by
    intro h
    subst h
    exact hw'ne (hwcv.symm.trans hcw.symm)
  -- the pair {w, wc} is a generator owner.
  have hzadj_w : G.Adj z (muNegOneCodeVertex G c u v w) := hzcw
  have hzadj_wc : G.Adj z (muNegOneCodeVertex G c u v wc) := by
    rw [hwcv]
    exact hw'data.1
  -- adjacency of the server to the two coded endpoints, min/max form.
  have hzadj_min : G.Adj (muNegOneCodeVertex G c u v (min w wc)) z := by
    rcases Nat.le_total w wc with h | h
    · rw [Nat.min_eq_left h]
      exact hzadj_w.symm
    · rw [Nat.min_eq_right h]
      exact hzadj_wc.symm
  have hzadj_max : G.Adj (muNegOneCodeVertex G c u v (max w wc)) z := by
    rcases Nat.le_total w wc with h | h
    · rw [Nat.max_eq_right h]
      exact hzadj_wc.symm
    · rw [Nat.max_eq_left h]
      exact hzadj_w.symm
  have hx1x2 : min w wc < max w wc :=
    min_lt_max.mpr (fun h => hwcne h.symm)
  have hx2b : max w wc < 16 := by
    rw [Nat.max_lt]
    omega
  -- the coded pair is an exterior-pair edge.
  have hRadj : (exteriorPairGraph G c.supp).Adj
      (muNegOneCodeSub G c u v (min w wc))
      (muNegOneCodeSub G c u v (max w wc)) := by
    refine ⟨?_, z, hzout, ?_, ?_⟩
    · intro h
      have := muNegOneCodeVertex_inj G c a b u v hab huinj hvinj
        hurange hvrange (min w wc) (by omega) (max w wc) (by omega)
        (by rw [← muNegOneCodeSub_val, ← muNegOneCodeSub_val, h])
      omega
    · rw [muNegOneCodeSub_val]
      exact hzadj_min
    · rw [muNegOneCodeSub_val]
      exact hzadj_max
  -- the pair {w, wc} is a generator owner.
  have howner : ∃ f : Fin 88,
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri f = (min w wc, max w wc) := by
    by_cases hmax8 : max w wc < 8
    · -- both codes on the first shore.
      have hmin8 : min w wc < 8 := by omega
      have hRuu : (exteriorPairGraph G c.supp).Adj
          (u ((min w wc : Nat) : ZMod 8)) (u ((max w wc : Nat) : ZMod 8)) := by
        have h1 := hRadj
        rwa [muNegOneCodeSub, muNegOneCodeSub, if_pos hmin8, if_pos hmax8]
          at h1
      have hdiff :
          if uTri then
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 1) ∨
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 4) ∨
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 7)
          else
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 3) ∨
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 4) ∨
            (((max w wc : Nat) : ZMod 8) -
                ((min w wc : Nat) : ZMod 8) = 5) := by
        cases uTri
        · exact (hmodeu _ _).mp hRuu
        · exact (hmodeu _ _).mp hRuu
      obtain ⟨f, hf⟩ := muNegThreeZeroFiveCorrect_within_left_mem_table uTri vTri
        ⟨min w wc, hmin8⟩ ⟨max w wc, hmax8⟩
        hx1x2 hdiff
      exact ⟨f, hf⟩
    · by_cases hmin8 : min w wc < 8
      · -- cross pair.
        have hmax8' : 8 ≤ max w wc := by omega
        obtain ⟨f, hf⟩ := muNegThreeZeroFiveCorrect_cross_mem_table uTri vTri
          ⟨min w wc, hmin8⟩ ⟨max w wc - 8, by omega⟩
        refine ⟨f, ?_⟩
        rw [hf]
        show ((min w wc : Nat), 8 + (max w wc - 8)) = (min w wc, max w wc)
        exact Prod.ext rfl (by omega)
      · -- both codes on the second shore.
        have hmin8' : 8 ≤ min w wc := by omega
        have hRvv : (exteriorPairGraph G c.supp).Adj
            (v ((min w wc - 8 : Nat) : ZMod 8))
            (v ((max w wc - 8 : Nat) : ZMod 8)) := by
          have h1 := hRadj
          rwa [muNegOneCodeSub, muNegOneCodeSub,
            if_neg (by omega), if_neg (by omega)] at h1
        have hdiff :
            if vTri then
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 1) ∨
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 4) ∨
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 7)
            else
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 3) ∨
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 4) ∨
              (((max w wc - 8 : Nat) : ZMod 8) -
                  ((min w wc - 8 : Nat) : ZMod 8) = 5) := by
          cases vTri
          · exact (hmodev _ _).mp hRvv
          · exact (hmodev _ _).mp hRvv
        have hsub : min w wc - 8 < max w wc - 8 := by omega
        obtain ⟨f, hf⟩ := muNegThreeZeroFiveCorrect_within_right_mem_table uTri vTri
          ⟨min w wc - 8, by omega⟩ ⟨max w wc - 8, by omega⟩
          hsub hdiff
        refine ⟨f, ?_⟩
        rw [hf]
        show (8 + (min w wc - 8), 8 + (max w wc - 8)) = (min w wc, max w wc)
        exact Prod.ext (by omega) (by omega)
  obtain ⟨f, hf⟩ := howner
  -- the server realizes the found owner.
  have htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f z := by
    refine ⟨hzout, ?_, ?_⟩
    · rw [hf]
      exact hzadj_min
    · rw [hf]
      exact hzadj_max
  refine ⟨f, ?_, z, htf, htez, ?_⟩
  · intro hfe
    subst hfe
    have hzte := muNegThreeZeroFiveCorrectOwnerVertex_unique G c u v uTri vTri hfree
      a b hab huinj hvinj hurange hvrange f htf hte
    rw [hzte] at htez
    exact G.irrefl htez
  · unfold muNegOnePairMem
    rw [hf, Bool.or_eq_true]
    rcases Nat.le_total w wc with h | h
    · left
      rw [Nat.min_eq_left h]
      show (w == w) = true
      exact beq_self_eq_true w
    · right
      rw [Nat.max_eq_left h]
      show (w == w) = true
      exact beq_self_eq_true w

end


end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_within_left_mem_table
#print axioms Erdos85.muNegThreeZeroFiveCorrect_within_right_mem_table
#print axioms Erdos85.muNegThreeZeroFiveCorrect_cross_mem_table
#print axioms Erdos85.muNegThreeZeroFiveCorrect_server_classification
