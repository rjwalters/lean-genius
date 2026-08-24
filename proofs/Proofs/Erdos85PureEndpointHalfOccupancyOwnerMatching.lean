import Proofs.Erdos85PureEndpointHalfOccupancyPrivateDefectDuality

/-!
# Local matching normal form at the forced half-occupancy vertex

The shore neighbors of the forced vertex have pairwise-disjoint one- or
two-element owner sets.  The singleton blocks are equinumerous with the
unused/full-center defect neighbors.  The remaining blocks are therefore a
matching which partitions every center left after those two classes.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- The forced local owner packing splits into singleton blocks and a
two-uniform matching, together with the unused defect-center class. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerMatching
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
      let B₁ := B.filter fun y => (owner y).card = 1
      let B₂ := B.filter fun y => (owner y).card = 2
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      B.card = m ∧ 2 ≤ K.card ∧ B₁.card = K.card ∧
      B₂.card = m - K.card ∧
      (∀ y ∈ B₂, (owner y).card = 2) ∧
      ((B₂ : Set V).PairwiseDisjoint owner) ∧
      F = K ∪ B₁.biUnion owner ∪ B₂.biUnion owner := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, hwCard, hwNotFull, hlabels, hpair⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let B₁ := B.filter fun y => (owner y).card = 1
  let B₂ := B.filter fun y => (owner y).card = 2
  let U := B.biUnion owner
  let U₁ := B₁.biUnion owner
  let U₂ := B₂.biUnion owner
  let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
  have hsize : ∀ y ∈ B, (owner y).card = 1 ∨ (owner y).card = 2 := by
    intro y hy
    simpa [B, owner, F] using hlabels y (by simpa [B] using hy)
  have hBpart : B = B₁ ∪ B₂ := by
    ext y
    constructor
    · intro hy
      rcases hsize y hy with hyOne | hyTwo
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hyOne⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hyTwo⟩)
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (Finset.mem_filter.mp hy).1
      · exact (Finset.mem_filter.mp hy).1
  have hBdisj : Disjoint B₁ B₂ := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy₁ hy₂
    have hOne := (Finset.mem_filter.mp hy₁).2
    have hTwo := (Finset.mem_filter.mp hy₂).2
    omega
  have hpairSet : ((B : Finset V) : Set V).PairwiseDisjoint owner := by
    intro y hy z hz hyz
    exact hpair y (by simpa [B] using hy) z (by simpa [B] using hz) hyz
  have hpairTwo : ((B₂ : Finset V) : Set V).PairwiseDisjoint owner := by
    intro y hy z hz hyz
    exact hpairSet (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hz).1 hyz
  have hUnionCard : U.card = ∑ y ∈ B, (owner y).card := by
    exact Finset.card_biUnion hpairSet
  have hmass : U.card + B₁.card = q := by
    have h := sum_card_add_singletonBlock_card_eq_two_mul_card B owner hsize
    rw [← hUnionCard] at h
    have hBcard : B.card = m := by simpa [B] using hwCard
    rw [hBcard, ← hqm] at h
    simpa [U, B₁] using h
  have hUSub : U ⊆ F := by
    intro i hi
    obtain ⟨y, _hy, hiy⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_inter.mp hiy).2
  have hK : K = F \ U := by
    have hDefectEq := c4Free_fullCenter_defectNeighbors_eq_unusedOwners
      G hfree S hreg hwNotFull
    change (secondOrderDefectGraph G).neighborFinset w ∩ F = F \ U
    rw [show (secondOrderDefectGraph G).neighborFinset w ∩ F =
        F.filter (fun i => ∀ y ∈ G.neighborFinset w ∩ S,
          i ∉ G.neighborFinset y) by simpa [F] using hDefectEq]
    ext i
    constructor
    · intro hi
      have hiData := Finset.mem_filter.mp hi
      apply Finset.mem_sdiff.mpr
      refine ⟨hiData.1, ?_⟩
      intro hiU
      obtain ⟨y, hyB, hiy⟩ := Finset.mem_biUnion.mp
        (show i ∈ B.biUnion owner by simpa [U] using hiU)
      exact hiData.2 y (by simpa [B] using hyB)
        (Finset.mem_inter.mp hiy).1
    · intro hi
      have hiData := Finset.mem_sdiff.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨hiData.1, ?_⟩
      intro y hyB hiy
      apply hiData.2
      show i ∈ U
      apply Finset.mem_biUnion.mpr
      exact ⟨y, by simpa [B] using hyB,
        Finset.mem_inter.mpr ⟨hiy, hiData.1⟩⟩
  have hKcard : K.card = B₁.card := by
    rw [hK, Finset.card_sdiff_of_subset hUSub]
    have hFcard : F.card = q := by simpa [F] using hCcard
    omega
  have hBcards : B₁.card + B₂.card = B.card := by
    rw [hBpart, Finset.card_union_of_disjoint hBdisj]
  have hB₂card : B₂.card = m - K.card := by
    have hBcard : B.card = m := by simpa [B] using hwCard
    omega
  have hUdecomp : U = U₁ ∪ U₂ := by
    ext i
    simp only [U, U₁, U₂, Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨y, hyB, hiy⟩
      rw [hBpart] at hyB
      rcases Finset.mem_union.mp hyB with hy₁ | hy₂
      · exact Or.inl ⟨y, hy₁, hiy⟩
      · exact Or.inr ⟨y, hy₂, hiy⟩
    · rintro (⟨y, hy₁, hiy⟩ | ⟨y, hy₂, hiy⟩)
      · exact ⟨y, hBpart.symm ▸ Finset.mem_union_left B₂ hy₁, hiy⟩
      · exact ⟨y, hBpart.symm ▸ Finset.mem_union_right B₁ hy₂, hiy⟩
  have hcover : F = K ∪ U₁ ∪ U₂ := by
    ext i
    rw [hK, hUdecomp]
    by_cases hiF : i ∈ F
    · simp [hiF]
    · have hiU₁ : i ∉ U₁ := by
        intro hi
        apply hiF (hUSub ?_)
        rw [hUdecomp]
        exact Finset.mem_union_left U₂ hi
      have hiU₂ : i ∉ U₂ := by
        intro hi
        apply hiF (hUSub ?_)
        rw [hUdecomp]
        exact Finset.mem_union_right U₁ hi
      simp [hiF, hiU₁, hiU₂]
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B] using hwCard
  · rw [hKcard]
    have hxB₁ : x ∈ B₁ := Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxS⟩,
       by simpa [owner, F] using hxOne⟩
    have hx'B₁ : x' ∈ B₁ := Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w x').mpr hx'w.symm, hx'S⟩,
       by simpa [owner, F] using hx'One⟩
    have hsub : ({x, x'} : Finset V) ⊆ B₁ := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxB₁
      · exact hx'B₁
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair hxx'] at hc
  · exact hKcard.symm
  · exact hB₂card
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · exact hpairTwo
  · simpa [U₁, U₂] using hcover

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerMatching
