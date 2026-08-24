import Proofs.Erdos85PureEndpointHalfOccupancyPrivateDefectDuality

/-!
# Universal private/defect conservation at half occupancy

The local counting law does not depend on how the half-occupancy vertex was
found.  It holds for every non-full half-occupancy vertex, making the identity
available for global summation.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Every non-full half-occupancy vertex satisfies exact conservation between
private graph neighbors and full-center defect neighbors.  Its owner blocks
also form a pairwise-disjoint partition of the complementary centers. -/
theorem c4Free_binarySquare_pureEndpoint_halfOccupancy_privateDefect_conservation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (w : V) (hwNotFull : w ∉ fullLineCenters G S q)
    (hwHalf : (G.neighborFinset w ∩ S).card = m) :
    let F := fullLineCenters G S q
    let B := G.neighborFinset w ∩ S
    let owner := fun y => G.neighborFinset y ∩ F
    let R₁ := S.filter fun y => (owner y).card = 1
    let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
    K.card = (G.neighborFinset w ∩ R₁).card ∧
    (((B : Finset V) : Set V).PairwiseDisjoint owner) ∧
    B.biUnion owner = F \ K := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B := G.neighborFinset w ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
  have hprofile :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  have hsize : ∀ y ∈ B, (owner y).card = 1 ∨ (owner y).card = 2 := by
    intro y hy
    exact (hprofile y).mp (mem_inter.mp hy).2
  have hpair : (((B : Finset V) : Set V).PairwiseDisjoint owner) := by
    intro y hy z hz hyz
    exact c4Free_neighbor_ownerSets_disjoint_of_not_mem
      G hfree F hwNotFull hyz
      ((G.mem_neighborFinset w y).mp (mem_inter.mp hy).1).symm
      ((G.mem_neighborFinset w z).mp (mem_inter.mp hz).1).symm
  have hUnionCard : (B.biUnion owner).card =
      ∑ y ∈ B, (owner y).card := card_biUnion hpair
  let P := B.filter fun y => (owner y).card = 1
  have hmass : (B.biUnion owner).card + P.card = q := by
    have h := sum_card_add_singletonBlock_card_eq_two_mul_card B owner hsize
    rw [← hUnionCard] at h
    change (B.biUnion owner).card + P.card = q
    rw [hwHalf, ← hqm] at h
    exact h
  have hUnionSub : B.biUnion owner ⊆ F := by
    intro i hi
    obtain ⟨y, _hy, hiy⟩ := mem_biUnion.mp hi
    exact (mem_inter.mp hiy).2
  have hKfilter := c4Free_fullCenter_defectNeighbors_eq_unusedOwners
    G hfree S hreg hwNotFull
  have hKset : K = F \ B.biUnion owner := by
    rw [show K = (secondOrderDefectGraph G).neighborFinset w ∩ F by rfl,
      hKfilter]
    ext i
    simp only [mem_filter, mem_sdiff, mem_biUnion, not_exists, not_and]
    constructor
    · rintro ⟨hiF, hi⟩
      refine ⟨hiF, ?_⟩
      intro y hyB hiy
      exact hi y hyB (mem_inter.mp hiy).1
    · rintro ⟨hiF, hi⟩
      refine ⟨hiF, ?_⟩
      intro y hyB hiy
      exact hi y hyB (mem_inter.mpr ⟨hiy, hiF⟩)
  have hKcard : K.card = P.card := by
    rw [hKset, card_sdiff_of_subset hUnionSub]
    have hFcard : F.card = q := by simpa [F] using hCcard
    omega
  have hProw : P = G.neighborFinset w ∩ R₁ := by
    ext y
    simp [P, B, R₁, owner, and_assoc]
  have hNear : B.biUnion owner = F \ K := by
    rw [hKset]
    exact (sdiff_sdiff_eq_self hUnionSub).symm
  exact ⟨by rw [hKcard, hProw], hpair, hNear⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_halfOccupancy_privateDefect_conservation
