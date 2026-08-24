import Proofs.Erdos85FinalDyadicOversizedExceptionalPure
import Proofs.Erdos85C4FreeSubsetCherryBound
import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos85FinalDyadicExceptionalProfile

/-!
# Graph-facing terminal for the large pure exceptional branch

The existing arithmetic terminal only needs the two replication classes.
Here they are constructed canonically from the full-line family.  Final-layer
packing supplies replication at most three; the sole remaining structural
socket is replication at least two on the shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- Four-class strengthening of the pure-large arithmetic terminal.  Unlike
the earlier form, this permits shore points of exceptional replication zero
or one. -/
theorem binarySquare_pureLargeExceptional_fourClass_impossible
    {q c s n₀ n₁ n₂ n₃ : ℕ} (hq : 8 ≤ q) (hqEven : Even q)
    (hqc : q < c)
    (hc : c ≤ 2 * q - 2)
    (hshore : 2 * s = q * q + c)
    (hclasses : n₀ + n₁ + n₂ + n₃ = s)
    (hincidence : n₁ + 2 * n₂ + 3 * n₃ = q * c)
    (hpairs : 2 * n₂ + 6 * n₃ ≤ c * (c - 1)) : False := by
  have hcpos : 1 ≤ c := by omega
  have hcprod : c * (c - 1) + c = c * c := by
    calc
      c * (c - 1) + c = c * ((c - 1) + 1) := by ring
      _ = c * c := by rw [Nat.sub_add_cancel hcpos]
  have hweighted : 4 * (q * c) ≤
      6 * s + (2 * n₂ + 6 * n₃) := by omega
  have hpoly : 4 * q * c ≤ 3 * q * q + c * c + 2 * c := by
    nlinarith
  obtain ⟨qhalf, hqhalf⟩ := hqEven
  let r := c - q
  have hcr : c = q + r := by
    dsimp [r]
    omega
  have hrupper : r ≤ q - 2 := by omega
  have hr : 2 ≤ r := by
    have hcEven : Even c := by
      have hqSq : q * q = 2 * (qhalf * q) := by
        rw [hqhalf]
        ring
      refine ⟨s - qhalf * q, ?_⟩
      omega
    obtain ⟨chalf, hchalf⟩ := hcEven
    dsimp [r]
    omega
  rw [hcr] at hpoly
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ r - 2 by omega)
    (show (0 : ℤ) ≤ q - r - 2 by omega)]

/-- A pure full exceptional family of size strictly between `q` and
`2q-2` is impossible once every shore point has replication at least two. -/
theorem c4Free_binarySquare_pureLarge_fullLineCenters_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hqc : q < (fullLineCenters G S q).card)
    (hc : (fullLineCenters G S q).card ≤ 2 * q - 2)
    (hshore : 2 * S.card = q * q + (fullLineCenters G S q).card)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) : False := by
  let C := fullLineCenters G S q
  let rep : V → ℕ := fun p => (G.neighborFinset p ∩ C).card
  let N₀ := S.filter fun p => rep p = 0
  let N₁ := S.filter fun p => rep p = 1
  let N₂ := S.filter fun p => rep p = 2
  let N₃ := S.filter fun p => rep p = 3
  have hm : 2 ≤ m := by omega
  have hregm : ∀ v, G.degree v = 2 * m := by simpa [hqm] using hreg
  have hcardm : Fintype.card V = 4 * m * m := by
    rw [hcard, hqm]
    ring
  have hlower : 2 * m * m - 2 * m + 1 ≤ S.card := by
    have hshore' : 2 * S.card =
        (2 * m) * (2 * m) + (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hshore
    have hqc' : 2 * m < (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hqc
    have hc' : (fullLineCenters G S (2 * m)).card ≤ 2 * (2 * m) - 2 := by
      simpa [hqm] using hc
    have hprod : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have hupper : S.card ≤ 2 * m * m + 2 * m - 1 := by
    have hshore' : 2 * S.card =
        (2 * m) * (2 * m) + (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hshore
    have hqc' : 2 * m < (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hqc
    have hc' : (fullLineCenters G S (2 * m)).card ≤ 2 * (2 * m) - 2 := by
      simpa [hqm] using hc
    have hprod : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have htri' : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = 2 * m := by
    intro v
    simpa [hqm] using htri v
  have hrepUpper : ∀ p ∈ S, rep p ≤ 3 := by
    intro p hp
    have hbound := binarySquare_finalLayer_exceptionalNeighbors_card_le_three
      G hfree hm hregm hcardm S hlower hupper htri' p
    have hfilter :
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        G.neighborFinset p ∩ C := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_inter,
        mem_fullLineCenters, C]
      constructor
      · rintro ⟨hwp, hzero | hfull⟩
        · have hwEmpty : w ∈ emptyLineCenters G S :=
            (mem_emptyLineCenters G S w).mpr hzero
          rw [hempty] at hwEmpty
          simp at hwEmpty
        · exact ⟨hwp, by simpa [hqm] using hfull⟩
      · rintro ⟨hwp, hfull⟩
        exact ⟨hwp, Or.inr (by simpa [hqm] using hfull)⟩
    rw [hfilter] at hbound
    exact hbound
  have hcases : ∀ p ∈ S,
      rep p = 0 ∨ rep p = 1 ∨ rep p = 2 ∨ rep p = 3 := by
    intro p hp
    have hup := hrepUpper p hp
    interval_cases rep p <;> simp_all
  have hpairDisj : ∀ {i k : ℕ}, i ≠ k →
      Disjoint (S.filter fun p => rep p = i)
        (S.filter fun p => rep p = k) := by
    intro i k hik
    rw [Finset.disjoint_left]
    intro p hpi hpk
    exact hik ((Finset.mem_filter.mp hpi).2.symm.trans
      (Finset.mem_filter.mp hpk).2)
  have hd01 : Disjoint N₀ N₁ := hpairDisj (by omega)
  have hd012 : Disjoint (N₀ ∪ N₁) N₂ := by
    rw [Finset.disjoint_left]
    intro p hp hp₂
    rcases Finset.mem_union.mp hp with hp₀ | hp₁
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₀ hp₂
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₁ hp₂
  have hd0123 : Disjoint (N₀ ∪ N₁ ∪ N₂) N₃ := by
    rw [Finset.disjoint_left]
    intro p hp hp₃
    rcases Finset.mem_union.mp hp with hp01 | hp₂
    · rcases Finset.mem_union.mp hp01 with hp₀ | hp₁
      · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₀ hp₃
      · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₁ hp₃
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₂ hp₃
  have hunion : N₀ ∪ N₁ ∪ N₂ ∪ N₃ = S := by
    apply Finset.Subset.antisymm
    · apply Finset.union_subset
      · apply Finset.union_subset
        · apply Finset.union_subset
          · intro p hp; exact (Finset.mem_filter.mp hp).1
          · intro p hp; exact (Finset.mem_filter.mp hp).1
        · intro p hp; exact (Finset.mem_filter.mp hp).1
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
    · intro p hp
      rcases hcases p hp with h₀ | h₁ | h₂ | h₃
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h₀⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h₁⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hp, h₂⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h₃⟩)
  have hclasses : N₀.card + N₁.card + N₂.card + N₃.card = S.card := by
    rw [← Finset.card_union_of_disjoint hd01,
      ← Finset.card_union_of_disjoint hd012,
      ← Finset.card_union_of_disjoint hd0123, hunion]
  have hout : ∀ p ∉ S, rep p = 0 := by
    intro p hp
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨w, hw⟩
    have hwp := (Finset.mem_inter.mp hw).1
    have hwFull := (mem_fullLineCenters G S q w).mp
      (Finset.mem_inter.mp hw).2
    have hpNw : p ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hwp
    have heq : G.neighborFinset w ∩ S = G.neighborFinset w := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hwFull, G.card_neighborFinset_eq_degree, hreg]
    have hpInter : p ∈ G.neighborFinset w ∩ S := by
      rw [heq]
      exact hpNw
    exact hp (Finset.mem_inter.mp hpInter).2
  have hsumRestrict : (∑ p ∈ S, rep p) = ∑ p : V, rep p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    exact hout p hp
  have hsumAll : (∑ p : V, rep p) = q * C.card := by
    have hinc := sum_card_neighbor_inter_eq_sum_degree G C
    change (∑ p : V, rep p) = _
    rw [hinc]
    simp [hreg, Nat.mul_comm]
  have hsumClasses : (∑ p ∈ S, rep p) =
      N₁.card + 2 * N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hd0123,
      Finset.sum_union hd012, Finset.sum_union hd01]
    have hsum₀ : (∑ p ∈ N₀, rep p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hsum₁ : (∑ p ∈ N₁, rep p) = N₁.card := by
      calc
        (∑ p ∈ N₁, rep p) = ∑ _p ∈ N₁, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = N₁.card := by simp
    have hsum₂ : (∑ p ∈ N₂, rep p) = 2 * N₂.card := by
      calc
        (∑ p ∈ N₂, rep p) = ∑ _p ∈ N₂, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 2 * N₂.card := by simp [Nat.mul_comm]
    have hsum₃ : (∑ p ∈ N₃, rep p) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, rep p) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₀, hsum₁, hsum₂, hsum₃]
    omega
  have hincidence : N₁.card + 2 * N₂.card + 3 * N₃.card =
      q * C.card := by
    rw [← hsumClasses, hsumRestrict, hsumAll]
  have hcherry :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree C
  have hcherryRestrict :
      (∑ p ∈ S, (rep p).choose 2) ≤ C.card.choose 2 := by
    calc
      (∑ p ∈ S, (rep p).choose 2) ≤
          ∑ p : V, (rep p).choose 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun _ _ _ => Nat.zero_le _)
      _ ≤ C.card.choose 2 := hcherry
  have hcherryClasses :
      (∑ p ∈ S, (rep p).choose 2) = N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hd0123,
      Finset.sum_union hd012, Finset.sum_union hd01]
    have hsum₀ : (∑ p ∈ N₀, (rep p).choose 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      decide
    have hsum₁ : (∑ p ∈ N₁, (rep p).choose 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      decide
    have hsum₂ : (∑ p ∈ N₂, (rep p).choose 2) = N₂.card := by
      calc
        (∑ p ∈ N₂, (rep p).choose 2) = ∑ _p ∈ N₂, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = N₂.card := by simp
    have hsum₃ : (∑ p ∈ N₃, (rep p).choose 2) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, (rep p).choose 2) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₀, hsum₁, hsum₂, hsum₃]
    omega
  have hpairs : 2 * N₂.card + 6 * N₃.card ≤ C.card * (C.card - 1) := by
    have hle : N₂.card + 3 * N₃.card ≤ C.card.choose 2 := by
      rw [← hcherryClasses]
      exact hcherryRestrict
    nlinarith [two_mul_choose_two C.card]
  exact binarySquare_pureLargeExceptional_fourClass_impossible
    hq ⟨m, by omega⟩ hqc hc hshore hclasses hincidence hpairs

/-- **The oversized final exceptional horn is empty.**  Empty-pole capacity
first turns an oversized complement into a pure full-line family.  Shore
balance bounds that family by `2q-2`, and the four-class terminal rules out
the resulting interval. -/
theorem c4Free_binarySquare_compl_finalDyadicSupport_card_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ((dyadicOccupancySupport G S j)ᶜ : Finset V).card ≤ q := by
  by_contra hnot
  have hqc : q < ((dyadicOccupancySupport G S j)ᶜ : Finset V).card := by
    omega
  have hempty :=
    c4Free_binarySquare_emptyLineCenters_eq_empty_of_q_lt_compl_finalDyadicSupport
      G hfree (by omega) hqa hreg hcard S hdiv hemptyClique hqc
  have hpure :=
    c4Free_binarySquare_compl_finalDyadicSupport_eq_fullLineCenters_of_q_lt
      G hfree (by omega) hqa hreg hcard S hdiv hemptyClique hqc
  have hbalance := c4Free_binarySquare_finalDivisible_shore_balance
    G hfree (by positivity) hqa hreg hcard S hS hSc hdiv
  have hmass := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hempty, Finset.card_empty, Int.ofNat_zero, sub_zero, hcard] at hmass
  have hshore : 2 * S.card =
      q * q + (fullLineCenters G S q).card := by
    exact_mod_cast (show (2 : ℤ) * S.card =
      q * q + (fullLineCenters G S q).card by omega)
  have hfullCard : (fullLineCenters G S q).card =
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).card := by
    rw [hpure]
  have hcUpper : (fullLineCenters G S q).card ≤ 2 * q - 2 := by
    have haPos : 0 < 2 ^ j := by positivity
    have ha : 1 ≤ 2 ^ j := haPos
    have haq : 2 ^ j ≤ q := by rw [hqa]; omega
    have hqpos : 1 ≤ q := by omega
    have hsub : q * (2 ^ j - 1) = q * 2 ^ j - q := by
      simpa using Nat.mul_sub_left_distrib q (2 ^ j) 1
    have htermLe : q * (2 ^ j - 1) + 1 ≤ q * q := by
      calc
        q * (2 ^ j - 1) + 1 ≤ q * (2 ^ j - 1) + q := by omega
        _ = q * 2 ^ j := by
          rw [hsub]
          have hqle : q ≤ q * 2 ^ j := Nat.le_mul_of_pos_right q haPos
          omega
        _ ≤ q * q := Nat.mul_le_mul_left q haq
    have hbalanceAdd : S.card + (q * (2 ^ j - 1) + 1) ≤ q * q :=
      (Nat.le_sub_iff_add_le htermLe).mp hbalance.2
    have hqleqa : q ≤ q * 2 ^ j := Nat.le_mul_of_pos_right q haPos
    have hqsq : q * q = 2 * (q * 2 ^ j) := by
      rw [hqa]
      ring
    rw [hsub] at hbalanceAdd
    rw [hqsq] at hbalanceAdd hshore
    omega
  have htriFinal := finalDyadic_occupancy_trichotomy G hqa hreg S hdiv
  have htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = 2 ^ j ∨
      (G.neighborFinset v ∩ S).card = q := by
    intro v
    rcases htriFinal v with hzero | hhalf | hfull
    · exact Or.inl hzero
    · exact Or.inr (Or.inl (by rw [hqa] at hhalf; omega))
    · exact Or.inr (Or.inr hfull)
  exact c4Free_binarySquare_pureLarge_fullLineCenters_impossible
    G hfree hq hqa hreg hcard S hempty
      (by rw [hfullCard]; exact hqc) hcUpper hshore htri

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureLarge_fullLineCenters_impossible
#print axioms Erdos85.binarySquare_pureLargeExceptional_fourClass_impossible
#print axioms
  Erdos85.c4Free_binarySquare_compl_finalDyadicSupport_card_le_degree
