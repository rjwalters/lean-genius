import Proofs.Erdos85OrderFortyNineDefectPerfectCodes

/-!
# Triangle partners bound high incidence at order 49

Every high neighbor of a low vertex has a distinct low triangle partner.
Consequently a degree-seven vertex has at most three high neighbors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A low vertex has at most three high neighbors. -/
theorem orderFortyNine_highNeighborCount_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card ≤ 3 := by
  classical
  let S : Finset V :=
    G.neighborFinset x ∩ orderFortyNineHighVertices G
  have hS_high : ∀ v ∈ S, G.degree v = 8 := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  have hS_adj : ∀ v ∈ S, G.Adj v x := by
    intro v hv
    have := (Finset.mem_inter.mp hv).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hpartner_card : ∀ v : {v // v ∈ S},
      (G.neighborFinset v.1 ∩ G.neighborFinset x).card = 1 := by
    intro v
    let xv : {z : V // z ∈ G.neighborSet v.1} :=
      ⟨x, hS_adj v.1 v.2⟩
    have hdeg := orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard (hS_high v.1 v.2) xv
    rwa [degree_induce_neighborSet_eq_card_common] at hdeg
  let partner : {v // v ∈ S} → V := fun v =>
    ((Finset.card_pos.mp (by rw [hpartner_card v]; norm_num)).choose)
  have hpartner_mem : ∀ v : {v // v ∈ S},
      partner v ∈ G.neighborFinset v.1 ∩ G.neighborFinset x := by
    intro v
    exact (Finset.card_pos.mp (by rw [hpartner_card v]; norm_num)).choose_spec
  have hpartner_low : ∀ v : {v // v ∈ S},
      partner v ∉ orderFortyNineHighVertices G := by
    intro v hvhigh
    have hp8 : G.degree (partner v) = 8 :=
      (Finset.mem_filter.mp hvhigh).2
    have hvp : G.Adj v.1 (partner v) := by
      have := (Finset.mem_inter.mp (hpartner_mem v)).1
      simpa [SimpleGraph.mem_neighborFinset] using this
    exact orderFortyNine_not_adj_degreeEight_degreeEight
      G hfree hmin hcard (hS_high v.1 v.2) hp8 hvp
  have hpartner_injective : Function.Injective partner := by
    intro v w hp
    apply Subtype.ext
    by_contra hvw
    have hcommon := orderFortyNine_card_common_degreeEight_eq_one
      G hfree hmin hcard (hS_high v.1 v.2) (hS_high w.1 w.2) hvw
    rcases Finset.card_eq_one.mp hcommon with ⟨q, hq⟩
    have hxmem : x ∈ G.neighborFinset v.1 ∩ G.neighborFinset w.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hS_adj v.1 v.2, hS_adj w.1 w.2⟩
    have hpmem : partner v ∈
        G.neighborFinset v.1 ∩ G.neighborFinset w.1 := by
      simp only [Finset.mem_inter]
      have hvp := (Finset.mem_inter.mp (hpartner_mem v)).1
      have hwp := (Finset.mem_inter.mp (hpartner_mem w)).1
      rw [← hp] at hwp
      exact ⟨hvp, hwp⟩
    have hxq : x = q := by simpa [hq] using hxmem
    have hpq : partner v = q := by simpa [hq] using hpmem
    have hpx : partner v = x := hpq.trans hxq.symm
    have hpadj : G.Adj x (partner v) := by
      have := (Finset.mem_inter.mp (hpartner_mem v)).2
      simpa [SimpleGraph.mem_neighborFinset] using this
    exact G.loopless.irrefl x (hpx ▸ hpadj)
  let T : Finset V :=
    G.neighborFinset x \ orderFortyNineHighVertices G
  let partnerLow : {v // v ∈ S} → {y // y ∈ T} := fun v =>
    ⟨partner v, by
      simp only [T, Finset.mem_sdiff]
      exact ⟨(Finset.mem_inter.mp (hpartner_mem v)).2,
        hpartner_low v⟩⟩
  have hpartnerLow_injective : Function.Injective partnerLow := by
    intro v w hp
    apply hpartner_injective
    exact congrArg Subtype.val hp
  have hST : S.card ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      partnerLow hpartnerLow_injective
  have hTcard : T.card = 7 - S.card := by
    dsimp [T]
    rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree, hx]
    congr 1
    rw [Finset.inter_comm]
  rw [hTcard] at hST
  change S.card ≤ 3
  omega

end

end Erdos85
