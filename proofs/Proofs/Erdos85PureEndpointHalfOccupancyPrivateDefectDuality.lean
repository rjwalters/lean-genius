import Proofs.Erdos85PureEndpointNeighborOwnerPacking
import Proofs.Erdos85PureEndpointHalfOccupancyDefectOwners

/-!
# Private-neighbor / defect-center duality at half occupancy

For a pairwise-disjoint family of blocks of size one or two, the unused
ground-set mass equals the number of singleton blocks when the ground set has
twice as many elements as there are blocks.  Applied to the forced local
owner packing, this identifies private graph neighbors of the half-occupancy
vertex with its full-center defect-neighbor count.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A family of one/two-element blocks has total block mass plus its number
of singleton blocks equal to twice its index-set size. -/
theorem sum_card_add_singletonBlock_card_eq_two_mul_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β)
    (hsize : ∀ x ∈ s, (f x).card = 1 ∨ (f x).card = 2) :
    (∑ x ∈ s, (f x).card) +
        (s.filter fun x => (f x).card = 1).card = 2 * s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haSize := hsize a (Finset.mem_insert_self a s)
      have hsSize : ∀ x ∈ s, (f x).card = 1 ∨ (f x).card = 2 := by
        intro x hx
        exact hsize x (Finset.mem_insert_of_mem hx)
      have hi := ih hsSize
      rcases haSize with haOne | haTwo
      · simp [Finset.filter_insert, ha, haOne]
        omega
      · simp [Finset.filter_insert, ha, haTwo]
        omega

/-- A preconnected pure endpoint contains a half-occupancy vertex for which
the number of private shore neighbors is exactly the number of full-center
second-order defect neighbors; this common number is at least two. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_privateDefect_duality
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
    let R₁ := S.filter fun y =>
      (G.neighborFinset y ∩ F).card = 1
    ∃ w,
      (G.neighborFinset w ∩ S).card = m ∧
      ((secondOrderDefectGraph G).neighborFinset w ∩ F).card =
        (G.neighborFinset w ∩ R₁).card ∧
      2 ≤ (G.neighborFinset w ∩ R₁).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B : V → Finset V := fun v => G.neighborFinset v ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, hwCard, hwNotFull, hlabels, hpair⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hsize : ∀ y ∈ B w, (owner y).card = 1 ∨ (owner y).card = 2 := by
    intro y hy
    simpa [B, owner, F] using hlabels y (by simpa [B] using hy)
  have hpairSet : ((B w : Finset V) : Set V).PairwiseDisjoint owner := by
    intro y hy z hz hyz
    exact hpair y (by simpa [B] using hy) z (by simpa [B] using hz) hyz
  have hUnionCard : ((B w).biUnion owner).card =
      ∑ y ∈ B w, (owner y).card := Finset.card_biUnion hpairSet
  let P := (B w).filter fun y => (owner y).card = 1
  have hmass : ((B w).biUnion owner).card + P.card = q := by
    have h := sum_card_add_singletonBlock_card_eq_two_mul_card
      (B w) owner hsize
    rw [← hUnionCard] at h
    have hBcard : (B w).card = m := by simpa [B] using hwCard
    change ((B w).biUnion owner).card + P.card = q
    rw [hBcard, ← hqm] at h
    exact h
  have hUnionSub : (B w).biUnion owner ⊆ F := by
    intro i hi
    obtain ⟨y, _hy, hiy⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_inter.mp hiy).2
  have hUnusedCard : (F \ (B w).biUnion owner).card = P.card := by
    rw [Finset.card_sdiff_of_subset hUnionSub]
    have hFcard : F.card = q := by simpa [F] using hCcard
    omega
  have hDefectEq := c4Free_fullCenter_defectNeighbors_eq_unusedOwners
    G hfree S hreg hwNotFull
  have hDefectCard :
      ((secondOrderDefectGraph G).neighborFinset w ∩ F).card = P.card := by
    rw [hDefectEq]
    have hfilterEq :
        F.filter (fun i => ∀ y ∈ G.neighborFinset w ∩ S,
          i ∉ G.neighborFinset y) = F \ (B w).biUnion owner := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion,
        not_exists, not_and]
      constructor
      · rintro ⟨hiF, hiUnused⟩
        refine ⟨hiF, ?_⟩
        intro y hyB
        intro hiOwner
        exact hiUnused y (by simpa [B] using hyB)
          (Finset.mem_inter.mp hiOwner).1
      · rintro ⟨hiF, hiUnused⟩
        refine ⟨hiF, ?_⟩
        intro y hyB hiy
        exact hiUnused y (by simpa [B] using hyB)
          (Finset.mem_inter.mpr ⟨hiy, hiF⟩)
    rw [hfilterEq, hUnusedCard]
  have hP_eq : P = G.neighborFinset w ∩ R₁ := by
    ext y
    simp [P, B, R₁, owner, and_assoc]
  have hxP : x ∈ P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxS⟩, ?_⟩
    simpa [owner, F] using hxOne
  have hx'P : x' ∈ P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset w x').mpr hx'w.symm, hx'S⟩, ?_⟩
    simpa [owner, F] using hx'One
  have htwo : 2 ≤ P.card := by
    have hsub : ({x, x'} : Finset V) ⊆ P := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hxP
      · exact hx'P
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hxx'] at hc
    exact hc
  refine ⟨w, hwCard, ?_, ?_⟩
  · rw [hDefectCard, hP_eq]
  · rwa [← hP_eq]

end

end Erdos85

#print axioms Erdos85.sum_card_add_singletonBlock_card_eq_two_mul_card
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_privateDefect_duality
