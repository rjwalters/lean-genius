import Proofs.Erdos85OneHighV2F3bGraphSide
import Proofs.Erdos85OneHighV2TableTransport

/-! # Concrete raw-graph construction of the v2 F3b ledger -/

namespace Erdos85

noncomputable section

open SimpleGraph

theorem oneHighFamilyGraphTable_eq_highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (profile : Nat)
    (hc : OneHighPureFamilyCnfConstraints profile
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)))
    (s u : {z : V // z ∈ G.neighborSet v})
    (hus : u ≠ s) (hum : u ≠ mate s) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    oneHighFamilyGraphTable R profile (branchLabel s).val
        (branchLabel u).val = highBranchMissCount G v s u := by
  intro E R
  have hjc : branchLabel u ≠ branchLabel s := fun h =>
    hus (branchLabel.injective h)
  have hjm : branchLabel u ≠ oneHighStandardMate (branchLabel s) := by
    rw [← hbranchMate s]
    exact fun h => hum (branchLabel.injective h)
  rw [oneHighFamilyGraphTable_eq_workerMissFinset_card]
  rw [oneHighFamilyWorkerMissFinset_card_eq_fullMissDeficit
    profile R hc (branchLabel s) (branchLabel u) hjc hjm]
  exact oneHighFamilyEncodedFullDeficit_eq_highBranchMissCount
    G hfree v branchLabel leafLabel s u

theorem oneHighFamilyTableGet_graphTable_eq
    (profile : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints profile R)
    (c j : Fin 8) (hjc : j ≠ c)
    (hjm : j ≠ oneHighStandardMate c) :
    oneHighFamilyTableGet (oneHighFamilyGraphTable R profile) c.val j.val =
      oneHighFamilyGraphTable R profile c.val j.val := by
  have f₁ := oneHighFamilyV2F1Ledger_of_constraints profile R hc
  unfold oneHighFamilyTableGet
  by_cases hle : c.val ≤ j.val
  · rw [min_eq_left hle, max_eq_right hle]
  · have hjle : j.val ≤ c.val := by omega
    rw [min_eq_right hjle, max_eq_left hjle]
    exact (f₁.table_symm c j hjc hjm).symm

theorem oneHighFamilyV2F3bLedger_of_rawGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (profile : Nat)
    (hc : OneHighPureFamilyCnfConstraints profile
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    OneHighFamilyV2F3bLedger R profile := by
  intro E R
  apply oneHighFamilyV2F3bLedger_of_constraints_of_card_eq profile R hc
  intro pair hpair
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  let a : Fin 8 := ⟨pair.1, hp.1⟩
  let b : Fin 8 := ⟨pair.2, hp.2.1⟩
  let s := branchLabel.symm a
  let t := branchLabel.symm b
  have hts : t ≠ s := by
    intro h
    have this : b = a := branchLabel.symm.injective h
    exact (Nat.ne_of_lt hp.2.2.1) (congrArg Fin.val this).symm
  have htm : t ≠ mate s := by
    intro h
    have hb : b = oneHighStandardMate a := by
      calc
        b = branchLabel t := by simp [t]
        _ = branchLabel (mate s) := congrArg branchLabel h
        _ = oneHighStandardMate (branchLabel s) := hbranchMate s
        _ = oneHighStandardMate a := by simp [s]
    have hvb := congrArg Fin.val hb
    rw [oneHighStandardMate_val_eq_xor] at hvb
    exact hp.2.2.2 hvb
  have hmateT_ne_s : mate t ≠ s := by
    intro h
    apply htm
    rw [← h, hmateInv t]
  have hmateT_ne_mateS : mate t ≠ mate s := by
    intro h
    exact hts (hmateInv.injective h)
  have hmateS_ne_t : mate s ≠ t := Ne.symm htm
  have hmateS_ne_mateT : mate s ≠ mate t := Ne.symm hmateT_ne_mateS
  have hraw := card_oneHighEncodedCommonPairBlock_eq_twenty_add_missCounts
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj branchLabel leafLabel s t hts htm
  have htab₁ := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v mate branchLabel hbranchMate leafLabel profile hc
      s (mate t) hmateT_ne_s hmateT_ne_mateS
  have htab₂ := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v mate branchLabel hbranchMate leafLabel profile hc
      t (mate s) hmateS_ne_t hmateS_ne_mateT
  have hlabelS : branchLabel s = a := branchLabel.apply_symm_apply a
  have hlabelT : branchLabel t = b := branchLabel.apply_symm_apply b
  have hlabelMateS : (branchLabel (mate s)).val = pair.1 ^^^ 1 := by
    rw [hbranchMate s, oneHighStandardMate_val_eq_xor, hlabelS]
  have hlabelMateT : (branchLabel (mate t)).val = pair.2 ^^^ 1 := by
    rw [hbranchMate t, oneHighStandardMate_val_eq_xor, hlabelT]
  have hlabelMateS' : (branchLabel (mate s)).val =
      (branchLabel s).val ^^^ 1 := by
    rw [hbranchMate s, oneHighStandardMate_val_eq_xor]
  have hlabelMateT' : (branchLabel (mate t)).val =
      (branchLabel t).val ^^^ 1 := by
    rw [hbranchMate t, oneHighStandardMate_val_eq_xor]
  have hj₁c : branchLabel (mate t) ≠ branchLabel s := fun h =>
    hmateT_ne_s (branchLabel.injective h)
  have hj₁m : branchLabel (mate t) ≠
      oneHighStandardMate (branchLabel s) := by
    rw [← hbranchMate s]
    exact fun h => hmateT_ne_mateS (branchLabel.injective h)
  have hj₂c : branchLabel (mate s) ≠ branchLabel t := fun h =>
    hmateS_ne_t (branchLabel.injective h)
  have hj₂m : branchLabel (mate s) ≠
      oneHighStandardMate (branchLabel t) := by
    rw [← hbranchMate t]
    exact fun h => hmateS_ne_mateT (branchLabel.injective h)
  have hget₁ := oneHighFamilyTableGet_graphTable_eq profile R hc
    (branchLabel s) (branchLabel (mate t)) hj₁c hj₁m
  have hget₂ := oneHighFamilyTableGet_graphTable_eq profile R hc
    (branchLabel t) (branchLabel (mate s)) hj₂c hj₂m
  change (oneHighEncodedCommonPairBlock R a b).card = _
  rw [← hlabelS, ← hlabelT]
  rw [← show (branchLabel s).val = pair.1 from congrArg Fin.val hlabelS,
    ← show (branchLabel t).val = pair.2 from congrArg Fin.val hlabelT,
    ← hlabelMateT', ← hlabelMateS']
  rw [hget₁, hget₂, htab₁, htab₂]
  simpa [E, R, s, t, a, b] using hraw

end

end Erdos85
