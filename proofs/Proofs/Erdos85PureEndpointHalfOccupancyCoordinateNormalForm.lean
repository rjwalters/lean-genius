import Proofs.Erdos85PureEndpointHalfOccupancyPrivateDefectDuality

/-!
# Coordinate normal form at the forced half-occupancy vertex

The shore neighbors split into singleton-owner and pair-owner blocks.  The
pair blocks form a matching on precisely the centers which are neither used
by singleton blocks nor defect-adjacent to the half-occupancy vertex.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Local singleton-plus-matching normal form. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_coordinateNormalForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let owner := fun y => G.neighborFinset y ∩ F
    ∃ w,
      let B := G.neighborFinset w ∩ S
      let P := B.filter fun y => (owner y).card = 1
      let Q := B.filter fun y => (owner y).card = 2
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      B.card = m ∧
      2 ≤ P.card ∧ K.card = P.card ∧
      Q.card + K.card = m ∧
      (((B : Finset V) : Set V).PairwiseDisjoint owner) ∧
      B.biUnion owner = F \ K ∧
      (((Q : Finset V) : Set V).PairwiseDisjoint owner) ∧
      (∀ y ∈ Q, (owner y).card = 2) ∧
      Q.biUnion owner = F \ (K ∪ P.biUnion owner) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, hwCard, hwNotFull, hlabels, hpair⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let P := B.filter fun y => (owner y).card = 1
  let Q := B.filter fun y => (owner y).card = 2
  let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
  have hsize : ∀ y ∈ B, (owner y).card = 1 ∨ (owner y).card = 2 := by
    intro y hy
    simpa [B, owner, F] using hlabels y (by simpa [B] using hy)
  have hBsplit : B = P ∪ Q := by
    ext y
    simp only [mem_union]
    constructor
    · intro hy
      rcases hsize y hy with h | h
      · exact Or.inl (by exact mem_filter.mpr ⟨hy, h⟩)
      · exact Or.inr (by exact mem_filter.mpr ⟨hy, h⟩)
    · rintro (hy | hy)
      · exact (mem_filter.mp hy).1
      · exact (mem_filter.mp hy).1
  have hPQdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro y hyP hyQ
    have h1 := (mem_filter.mp hyP).2
    have h2 := (mem_filter.mp hyQ).2
    omega
  have hQpair : (((Q : Finset V) : Set V).PairwiseDisjoint owner) := by
    intro y hy z hz hyz
    apply hpair y (by exact (mem_filter.mp hy).1) z
      (by exact (mem_filter.mp hz).1) hyz
  have hPpair : (((P : Finset V) : Set V).PairwiseDisjoint owner) := by
    intro y hy z hz hyz
    apply hpair y (by exact (mem_filter.mp hy).1) z
      (by exact (mem_filter.mp hz).1) hyz
  have hxP : x ∈ P := mem_filter.mpr
    ⟨mem_inter.mpr ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxS⟩,
      by simpa [owner, F] using hxOne⟩
  have hx'P : x' ∈ P := mem_filter.mpr
    ⟨mem_inter.mpr ⟨(G.mem_neighborFinset w x').mpr hx'w.symm, hx'S⟩,
      by simpa [owner, F] using hx'One⟩
  have hPtwo : 2 ≤ P.card := by
    have hs : ({x, x'} : Finset V) ⊆ P := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxP
      · exact hx'P
    have := card_le_card hs
    rwa [card_pair hxx'] at this
  have hKfilter := c4Free_fullCenter_defectNeighbors_eq_unusedOwners
    G hfree S hreg hwNotFull
  have hKmem : ∀ i, i ∈ K ↔ i ∈ F ∧ i ∉ B.biUnion owner := by
    intro i
    rw [show K = (secondOrderDefectGraph G).neighborFinset w ∩ F by rfl,
      hKfilter]
    simp only [mem_filter, mem_biUnion, not_exists, not_and]
    constructor
    · rintro ⟨hiF, hi⟩
      refine ⟨hiF, ?_⟩
      intro y hyB hiy
      exact hi y hyB (mem_inter.mp hiy).1
    · rintro ⟨hiF, hi⟩
      refine ⟨hiF, ?_⟩
      intro y hyB hiy
      exact hi y hyB (mem_inter.mpr ⟨hiy, hiF⟩)
  have hUnionSub : B.biUnion owner ⊆ F := by
    intro i hi
    obtain ⟨y, _hy, hiy⟩ := mem_biUnion.mp hi
    exact (mem_inter.mp hiy).2
  have hpairB : (((B : Finset V) : Set V).PairwiseDisjoint owner) := by
    intro y hy z hz hyz
    exact hpair y hy z hz hyz
  have hUnionCard : (B.biUnion owner).card =
      ∑ y ∈ B, (owner y).card := card_biUnion hpairB
  have hmass := sum_card_add_singletonBlock_card_eq_two_mul_card
    B owner hsize
  have hBcard : B.card = m := by simpa [B] using hwCard
  have hKcard : K.card = P.card := by
    have hKset : K = F \ B.biUnion owner := by
      ext i
      simpa [mem_sdiff] using hKmem i
    rw [hKset, card_sdiff_of_subset hUnionSub, hUnionCard]
    have hFcard : F.card = q := by simpa [F] using hCcard
    change (∑ y ∈ B, (owner y).card) + P.card = 2 * B.card at hmass
    rw [hFcard, hBcard, ← hqm] at *
    omega
  have hNearParallel : B.biUnion owner = F \ K := by
    ext i
    constructor
    · intro hiUsed
      have hiF := hUnionSub hiUsed
      apply mem_sdiff.mpr
      refine ⟨hiF, ?_⟩
      intro hiK
      exact (hKmem i).mp hiK |>.2 hiUsed
    · intro hi
      have hiData := mem_sdiff.mp hi
      by_contra hiNotUsed
      exact hiData.2 ((hKmem i).mpr ⟨hiData.1, hiNotUsed⟩)
  have hQplusK : Q.card + K.card = m := by
    have hcardSplit := card_union_of_disjoint hPQdisj
    rw [← hBsplit, hBcard] at hcardSplit
    omega
  have hcover : Q.biUnion owner = F \ (K ∪ P.biUnion owner) := by
    ext i
    constructor
    · intro hiQ
      obtain ⟨y, hyQ, hiy⟩ := mem_biUnion.mp hiQ
      have hiF := (mem_inter.mp hiy).2
      apply mem_sdiff.mpr
      refine ⟨hiF, ?_⟩
      intro hiUnion
      rcases mem_union.mp hiUnion with hiK | hiP
      · exact (hKmem i).mp hiK |>.2 (by
          apply mem_biUnion.mpr
          exact ⟨y, (mem_filter.mp hyQ).1, hiy⟩)
      · obtain ⟨z, hzP, hiz⟩ := mem_biUnion.mp hiP
        have hyz : y ≠ z := by
          intro h
          subst z
          exact (Finset.disjoint_left.mp hPQdisj hzP hyQ).elim
        exact (Finset.disjoint_left.mp
          (hpair y (mem_filter.mp hyQ).1 z (mem_filter.mp hzP).1 hyz)
          hiy hiz).elim
    · intro hi
      have hiData := mem_sdiff.mp hi
      have hiNotK : i ∉ K := fun hiK => hiData.2 (mem_union_left _ hiK)
      have hiUsed : i ∈ B.biUnion owner := by
        by_contra hiNotUsed
        exact hiNotK ((hKmem i).mpr ⟨hiData.1, hiNotUsed⟩)
      obtain ⟨y, hyB, hiy⟩ := mem_biUnion.mp hiUsed
      have hyNotP : y ∉ P := by
        intro hyP
        apply hiData.2
        apply mem_union_right
        exact mem_biUnion.mpr ⟨y, hyP, hiy⟩
      have hyQ : y ∈ Q := by
        rw [hBsplit] at hyB
        rcases mem_union.mp hyB with hyP | hyQ
        · exact (hyNotP hyP).elim
        · exact hyQ
      exact mem_biUnion.mpr ⟨y, hyQ, hiy⟩
  refine ⟨w, hBcard, hPtwo, hKcard, hQplusK, hpairB,
    hNearParallel, hQpair, ?_, hcover⟩
  intro y hy
  exact (mem_filter.mp hy).2

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_coordinateNormalForm
