import Proofs.Erdos85FinalDyadicExceptionalEmptyBoundaryLeakage
import Proofs.Erdos85C4FreeSubsetForbiddenCherryBound

/-!
# Positive high centers pack into full-center pairs

The positive high adjacency level is `2`.  The final-layer exceptional
neighbor cap forces this to consist of exactly two full neighbors and no
empty neighbor.  C4-freeness then packs the positive high class into the
unordered pairs of full centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A positive high-cut center has exactly two full-center neighbors and no
empty-center neighbor. -/
theorem finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    ∀ v ∈ finalDyadicPositiveHighCutCenters G S q r,
      (G.neighborFinset v ∩ fullLineCenters G S q).card = 2 ∧
        (G.neighborFinset v ∩ emptyLineCenters G S).card = 0 := by
  let m := 2 ^ j
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hregm : ∀ v, G.degree v = 2 * m := by
    intro v
    rw [hreg, hqa]
  have hcardm : Fintype.card V = 4 * m * m := by
    rw [hcard, hqa]
    dsimp only [m]
    ring
  have hcardZ : (Fintype.card V : ℤ) = (q : ℤ) ^ 2 := by
    rw [hcard]
    push_cast
    ring
  have hshoreZ : 2 * (S.card : ℤ) = (q : ℤ) ^ 2 + 2 * r := by
    rw [hcardZ] at hdisp
    nlinarith
  have hshoreMZ : 2 * (S.card : ℤ) = 4 * (m : ℤ) * m + 2 * r := by
    rw [hqa] at hshoreZ
    change 2 * (S.card : ℤ) = (2 * (m : ℤ)) ^ 2 + 2 * r at hshoreZ
    nlinarith
  have hshore : 2 * S.card = 4 * m * m + 2 * r := by
    exact_mod_cast hshoreMZ
  have hS : S.card = 2 * m * m + r := by nlinarith
  have hlower : 2 * m * m - 2 * m + 1 ≤ S.card := by
    rw [hS]
    omega
  have hupper : S.card ≤ 2 * m * m + 2 * m - 1 := by
    change r < m at hrhalf
    rw [hS]
    omega
  have htri : ∀ x,
      (G.neighborFinset x ∩ S).card = 0 ∨
      (G.neighborFinset x ∩ S).card = m ∨
      (G.neighborFinset x ∩ S).card = 2 * m := by
    intro x
    rcases finalDyadic_occupancy_trichotomy G hqa hreg S hdiv x with
      hzero | hhalf | hfull
    · exact Or.inl hzero
    · right; left
      change q = 2 * m at hqa
      omega
    · right; right
      change q = 2 * m at hqa
      omega
  intro v hvP
  have hvS : v ∈ S := (Finset.mem_filter.mp hvP).1
  have hbalance := finalDyadic_positiveShore_exceptionalAdjacencyBalance
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf v hvS
  change finalDyadicExceptionalAdjacencyBalance G S q v =
    if v ∈ finalDyadicPositiveHighCutCenters G S q r then 2 else 1 at hbalance
  rw [if_pos hvP] at hbalance
  have hz (w : V) : exceptionalOccupancySign G S q w =
      (if w ∈ F then (1 : ℤ) else 0) -
        (if w ∈ E then (1 : ℤ) else 0) := by
    have hdisj := fullLineCenters_disjoint_emptyLineCenters G S (by omega : 0 < q)
    by_cases hwF : w ∈ F
    · have hwE : w ∉ E := Finset.disjoint_left.mp hdisj hwF
      simp [exceptionalOccupancySign, F, E, hwF, hwE,
        (mem_fullLineCenters G S q w).mp hwF]
    · by_cases hwE : w ∈ E
      · have hoccE := (mem_emptyLineCenters G S w).mp hwE
        have hzeroNotQ : ¬ 0 = q := by omega
        simp [exceptionalOccupancySign, F, E, hwF, hwE, hoccE,
          hzeroNotQ]
      · have hnotFull : ¬(G.neighborFinset w ∩ S).card = q := fun h =>
          hwF ((mem_fullLineCenters G S q w).mpr h)
        have hnotEmpty : ¬(G.neighborFinset w ∩ S).card = 0 := fun h =>
          hwE ((mem_emptyLineCenters G S w).mpr h)
        simp [exceptionalOccupancySign, F, E, hwF, hwE, hnotFull, hnotEmpty]
  have hbalanceCounts :
      ((G.neighborFinset v ∩ F).card : ℤ) -
          (G.neighborFinset v ∩ E).card = 2 := by
    change (∑ w ∈ G.neighborFinset v, exceptionalOccupancySign G S q w) = 2
      at hbalance
    simp_rw [hz, Finset.sum_sub_distrib] at hbalance
    simpa [Finset.sum_ite_mem] using hbalance
  have hcap := binarySquare_finalLayer_exceptionalNeighbors_card_le_three
    G hfree (by dsimp [m]; omega) hregm hcardm S hlower hupper htri v
  have hfilter :
      (G.neighborFinset v).filter (fun w =>
        (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        G.neighborFinset v ∩ (F ∪ E) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union]
    rw [mem_fullLineCenters, mem_emptyLineCenters]
    simp only [m]
    rw [← hqa]
    tauto
  rw [hfilter] at hcap
  have hdisjInter : Disjoint (G.neighborFinset v ∩ F)
      (G.neighborFinset v ∩ E) := by
    exact Finset.disjoint_left.mpr fun w hwF hwE =>
      Finset.disjoint_left.mp
        (fullLineCenters_disjoint_emptyLineCenters G S (by omega))
        (Finset.mem_inter.mp hwF).2 (Finset.mem_inter.mp hwE).2
  have hsplit : G.neighborFinset v ∩ (F ∪ E) =
      (G.neighborFinset v ∩ F) ∪ (G.neighborFinset v ∩ E) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hsplit, Finset.card_union_of_disjoint hdisjInter] at hcap
  change (G.neighborFinset v ∩ F).card = 2 ∧
    (G.neighborFinset v ∩ E).card = 0
  constructor <;> omega

/-- Positive high centers pack into the unordered pairs of full centers. -/
theorem finalDyadic_positiveHighCutCenters_card_le_full_choose_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    (finalDyadicPositiveHighCutCenters G S q r).card ≤
      (fullLineCenters G S q).card.choose 2 := by
  let P := finalDyadicPositiveHighCutCenters G S q r
  let F := fullLineCenters G S q
  have hprofile := finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hsumP :
      P.card = ∑ v ∈ P, ((G.neighborFinset v ∩ F).card).choose 2 := by
    calc
      P.card = ∑ _v ∈ P, 1 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvTwo := (hprofile v hv).1
        change (G.neighborFinset v ∩ F).card = 2 at hvTwo
        rw [hvTwo]
        decide
  have hsubset : P ⊆ (Finset.univ : Finset V) := Finset.subset_univ P
  have hsumLe :
      (∑ v ∈ P, ((G.neighborFinset v ∩ F).card).choose 2) ≤
        ∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2 :=
    Finset.sum_le_sum_of_subset hsubset
  have hcherry :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree F
  change (∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2) ≤
    F.card.choose 2 at hcherry
  change P.card ≤ F.card.choose 2
  omega

/-- Full-center defect pairs are forbidden cherries, sharpening the packing
bound to `|P| + e_D(F) ≤ choose(|F|,2)`. -/
theorem finalDyadic_positiveHigh_add_fullDefectPairs_le_full_choose_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    (finalDyadicPositiveHighCutCenters G S q r).card +
        (secondOrderDefectPairs G (fullLineCenters G S q)).card ≤
      (fullLineCenters G S q).card.choose 2 := by
  let P := finalDyadicPositiveHighCutCenters G S q r
  let F := fullLineCenters G S q
  let Z := secondOrderDefectPairs G F
  have hprofile := finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hsumP :
      P.card = ∑ v ∈ P, ((G.neighborFinset v ∩ F).card).choose 2 := by
    calc
      P.card = ∑ _v ∈ P, 1 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvTwo := (hprofile v hv).1
        change (G.neighborFinset v ∩ F).card = 2 at hvTwo
        rw [hvTwo]
        decide
  have hsumLe :
      (∑ v ∈ P, ((G.neighborFinset v ∩ F).card).choose 2) ≤
        ∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ P)
  have hpen := sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
    G hfree F Z
      (secondOrderDefectPairs_subset_powersetCard G F)
      (secondOrderDefectPairs_forbidden_commonNeighbor G hfree F)
  change (∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2) ≤
    F.card.choose 2 - Z.card at hpen
  have hZle : Z.card ≤ F.card.choose 2 := by
    calc
      Z.card ≤ (F.powersetCard 2).card :=
        Finset.card_le_card (secondOrderDefectPairs_subset_powersetCard G F)
      _ = F.card.choose 2 := Finset.card_powersetCard 2 F
  change P.card + Z.card ≤ F.card.choose 2
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
#print axioms
  Erdos85.finalDyadic_positiveHighCutCenters_card_le_full_choose_two
#print axioms
  Erdos85.finalDyadic_positiveHigh_add_fullDefectPairs_le_full_choose_two
