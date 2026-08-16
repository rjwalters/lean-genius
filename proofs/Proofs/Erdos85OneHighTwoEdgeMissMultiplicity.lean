import Proofs.Erdos85OneHighExchangedPairParity
import Proofs.Erdos85OneHighCanonicalMate

/-! # Miss multiplicity in a canonical two-edge branch -/

namespace Erdos85

noncomputable section

theorem card_filter_finFive_lt_four_eq_fourEndpointLabelMultiplicity
    {L : Type*} [DecidableEq L] (f : Fin 5 → L) (u : L) :
    ((Finset.univ : Finset (Fin 5)).filter fun r =>
      r.val < 4 ∧ f r = u).card =
      fourEndpointLabelMultiplicity (f 0) (f 1) (f 2) (f 3) u := by
  rw [Finset.card_filter, Fin.sum_univ_five]
  simp [fourEndpointLabelMultiplicity, eq_comm]

theorem exists_oneHighCanonicalBranchAdj_true_of_lt_four
    (r : Fin 5) (hr : r.val < 4) :
    ∃ j : Fin 5, oneHighCanonicalBranchAdj true r j = true := by
  fin_cases r <;> simp [oneHighCanonicalBranchAdj] at hr ⊢

theorem oneHighCanonicalBranchAdj_true_four
    (j : Fin 5) : oneHighCanonicalBranchAdj true 4 j = false := by
  fin_cases j <;> decide

theorem card_neighbor_inter_branch_eq_one_of_canonicalTrue_lt_four
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (s : {z : V // z ∈ G.neighborSet v})
    (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj true (e x) (e y))
    (r : Fin 5) (hr : r.val < 4) :
    (G.neighborFinset ((e.symm r).1) ∩
      secondLayerBranch G v s).card = 1 := by
  have hle := degree_induce_secondLayerBranch_le_one
    G hfree v s (e.symm r)
  rw [degree_induce_secondLayerBranch_eq_card_inter] at hle
  obtain ⟨j, hj⟩ := exists_oneHighCanonicalBranchAdj_true_of_lt_four r hr
  have hc := hcanonical (e.symm r) (e.symm j)
  rw [e.apply_symm_apply, e.apply_symm_apply] at hc
  have hadj : G.Adj (e.symm r).1 (e.symm j).1 := by
    apply of_decide_eq_true
    rw [hc]
    exact hj
  have hpos : 0 < (G.neighborFinset ((e.symm r).1) ∩
      secondLayerBranch G v s).card := by
    apply Finset.card_pos.mpr
    exact ⟨(e.symm j).1, Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset _ _).mpr hadj, (e.symm j).2⟩⟩
  omega

theorem highBranchMissCount_eq_fourEndpointLabelMultiplicity
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj true (e x) (e y))
    (u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (rootMate s))) :
    highBranchMissCount G v s u = fourEndpointLabelMultiplicity
      (oneHighMissingBranch G v rootMate s ((e.symm 0).1))
      (oneHighMissingBranch G v rootMate s ((e.symm 1).1))
      (oneHighMissingBranch G v rootMate s ((e.symm 2).1))
      (oneHighMissingBranch G v rootMate s ((e.symm 3).1)) u := by
  classical
  let label : Fin 5 → {z : V // z ∈ G.neighborSet v} := fun r =>
    oneHighMissingBranch G v rootMate s ((e.symm r).1)
  let T : Finset (Fin 5) := Finset.univ.filter fun r =>
    r.val < 4 ∧ label r = u
  have hinter (r : Fin 5) :
      (G.neighborFinset ((e.symm r).1) ∩
        secondLayerBranch G v s).card = if r.val < 4 then 1 else 0 := by
    have hle := degree_induce_secondLayerBranch_le_one
      G hfree v s (e.symm r)
    rw [degree_induce_secondLayerBranch_eq_card_inter] at hle
    by_cases hr : r.val < 4
    · have hone := card_neighbor_inter_branch_eq_one_of_canonicalTrue_lt_four
        G hfree v s e hcanonical r hr
      simp only [if_pos hr]
      exact hone
    · have hr4 : r = 4 := by apply Fin.ext; omega
      subst r
      have hempty : G.neighborFinset ((e.symm 4).1) ∩
          secondLayerBranch G v s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hyParts := Finset.mem_inter.mp hy
        let yb : secondLayerBranch G v s := ⟨y, hyParts.2⟩
        have hc := hcanonical (e.symm 4) yb
        rw [e.apply_symm_apply] at hc
        have hleft : decide (G.Adj (e.symm 4).1 yb.1) = true :=
          decide_eq_true ((G.mem_neighborFinset _ _).mp hyParts.1)
        rw [hleft, oneHighCanonicalBranchAdj_true_four] at hc
        contradiction
      rw [hempty]
      simp
  have hmiss_iff (r : Fin 5) :
      (G.neighborFinset ((e.symm r).1) ∩
          secondLayerBranch G v u).card = 0 ↔
        r.val < 4 ∧ label r = u := by
    have hrBranch := (e.symm r).2
    have hrSecond : (e.symm r).1 ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hrBranch⟩
    by_cases hr : r.val < 4
    · have hrMatched :
          (G.neighborFinset ((e.symm r).1) ∩
            secondLayerBranch G v s).card = 1 := by simp [hinter r, hr]
      constructor
      · intro hmiss
        have huMem : u ∈ oneHighFarMissBranches G v rootMate s
            ((e.symm r).1) := Finset.mem_filter.mpr ⟨hu, hmiss⟩
        have heq := eq_oneHighMissingBranch_of_matched_of_mem
          G hfree hv hexternal houterDegree rootMate hrootAdj s
          ((e.symm r).1) hrBranch hrMatched u huMem
        exact ⟨hr, by simpa [label] using heq.symm⟩
      · rintro ⟨_, hlabel⟩
        have hmem := oneHighMissingBranch_mem_of_matched
          G hfree hv hexternal houterDegree rootMate hrootAdj s
          ((e.symm r).1) hrBranch hrMatched
        have hmiss := (Finset.mem_filter.mp hmem).2
        simpa [label, hlabel] using hmiss
    · constructor
      · intro hmiss
        have hcard := card_farBranch_misses_eq_internalDegree
          G hfree (d := 7) (by omega) hexternal s (rootMate s)
          (hrootAdj s) ((e.symm r).1) hrBranch
          (houterDegree hrSecond)
        have huMem : u ∈ (((Finset.univ.erase s).erase (rootMate s)).filter
            fun w => (G.neighborFinset ((e.symm r).1) ∩
              secondLayerBranch G v w).card = 0) :=
          Finset.mem_filter.mpr ⟨hu, hmiss⟩
        have hpos := Finset.card_pos.mpr ⟨u, huMem⟩
        rw [hinter r, if_neg hr] at hcard
        omega
      · rintro ⟨hlt, _⟩
        exact (hr hlt).elim
  have hcard : highBranchMissCount G v s u = T.card := by
    unfold highBranchMissCount
    apply Finset.card_bij (fun a ha =>
      e ⟨a, (Finset.mem_filter.mp ha).1⟩)
    · intro a ha
      have haParts := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      have hmiss :
          (G.neighborFinset ((e.symm (e ⟨a, haParts.1⟩)).1) ∩
            secondLayerBranch G v u).card = 0 := by
        have he := e.symm_apply_apply ⟨a, haParts.1⟩
        have hval : (e.symm (e ⟨a, haParts.1⟩)).1 = a :=
          congrArg Subtype.val he
        rw [hval]
        exact haParts.2
      simpa [T, label] using
        (hmiss_iff (e ⟨a, haParts.1⟩)).mp hmiss
    · intro a _ b _ hab
      exact congrArg Subtype.val (e.injective hab)
    · intro r hr
      have hrParts := Finset.mem_filter.mp hr
      let a : secondLayerBranch G v s := e.symm r
      refine ⟨a.1, Finset.mem_filter.mpr ⟨a.2, ?_⟩, ?_⟩
      · exact (hmiss_iff r).mpr hrParts.2
      · exact e.apply_symm_apply r
  rw [hcard]
  change T.card = _
  simpa [T, label] using
    card_filter_finFive_lt_four_eq_fourEndpointLabelMultiplicity label u

/-- In a canonical two-edge branch, if every far miss count is even and
both internal edges are nonconstant, the two exchanged miss-label pairs are
the same unordered pair. -/
theorem canonicalTwoEdge_missingPair_eq_of_even
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj true (e x) (e y))
    (heven : ∀ u ∈ ((Finset.univ.erase s).erase (rootMate s)),
      Even (highBranchMissCount G v s u))
    (h01 : oneHighMissingBranch G v rootMate s ((e.symm 0).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 1).1))
    (h23 : oneHighMissingBranch G v rootMate s ((e.symm 2).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 3).1)) :
    (min (oneHighMissingBranch G v rootMate s ((e.symm 0).1))
        (oneHighMissingBranch G v rootMate s ((e.symm 1).1)),
      max (oneHighMissingBranch G v rootMate s ((e.symm 0).1))
        (oneHighMissingBranch G v rootMate s ((e.symm 1).1))) =
    (min (oneHighMissingBranch G v rootMate s ((e.symm 2).1))
        (oneHighMissingBranch G v rootMate s ((e.symm 3).1)),
      max (oneHighMissingBranch G v rootMate s ((e.symm 2).1))
        (oneHighMissingBranch G v rootMate s ((e.symm 3).1))) := by
  let label : Fin 5 → {z : V // z ∈ G.neighborSet v} := fun r =>
    oneHighMissingBranch G v rootMate s ((e.symm r).1)
  have hlabelMem (r : Fin 5) (hr : r.val < 4) :
      label r ∈ ((Finset.univ.erase s).erase (rootMate s)) := by
    have hrMatched :
        (G.neighborFinset ((e.symm r).1) ∩
          secondLayerBranch G v s).card = 1 := by
      exact card_neighbor_inter_branch_eq_one_of_canonicalTrue_lt_four
        G hfree v s e hcanonical r hr
    have hm := oneHighMissingBranch_mem_of_matched G hfree hv hexternal
      houterDegree rootMate hrootAdj s ((e.symm r).1) (e.symm r).2 hrMatched
    exact (Finset.mem_filter.mp hm).1
  apply minMax_pair_eq_of_fourEndpointMultiplicity_even _ _ _ _ h01 h23
  intro u
  by_cases hu : u ∈ ((Finset.univ.erase s).erase (rootMate s))
  · have hEven := heven u hu
    have hEq := highBranchMissCount_eq_fourEndpointLabelMultiplicity
      G hfree hv hexternal houterDegree rootMate hrootAdj s e hcanonical u hu
    rw [hEq] at hEven
    rcases hEven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    by_cases h0 : u = label 0 <;> by_cases h1 : u = label 1 <;>
      by_cases h2 : u = label 2 <;> by_cases h3 : u = label 3 <;>
      simpa [fourEndpointLabelMultiplicity, label, h0, h1, h2, h3] using hk
  · have h0 : u ≠ label 0 := fun h => hu (h ▸ hlabelMem 0 (by decide))
    have h1 : u ≠ label 1 := fun h => hu (h ▸ hlabelMem 1 (by decide))
    have h2 : u ≠ label 2 := fun h => hu (h ▸ hlabelMem 2 (by decide))
    have h3 : u ≠ label 3 := fun h => hu (h ▸ hlabelMem 3 (by decide))
    refine ⟨0, ?_⟩
    simp [fourEndpointLabelMultiplicity, label, h0, h1, h2, h3]

end

end Erdos85
