import Proofs.Erdos85PlateauLocalRigidity
import Proofs.Erdos85ConflictRegular

/-!
# Greedy localization through the conflict graph

A maximum independent set is maximal, so its closed neighborhoods cover a
finite graph.  Applied to the common-neighbor conflict graph and the sharp
degree window of a plateau core, this gives a uniform cubic localization
with leading constant four.
-/

open SimpleGraph Finset

namespace Erdos85

/-- The standard greedy independence bound, in multiplication-free form. -/
theorem card_le_indepNum_mul_maxDegree_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Fintype.card V ≤ H.indepNum * (H.maxDegree + 1) := by
  classical
  obtain ⟨S, hSind, hScard⟩ := H.exists_isNIndepSet_indepNum
  let U := S.biUnion fun x => H.neighborFinset x
  have hcover : Finset.univ ⊆ S ∪ U := by
    intro x _
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ hxS
    have hxU : x ∈ U := by
      by_contra hxnot
      have hno : ∀ y ∈ S, ¬ H.Adj x y := by
        intro y hy hxy
        apply hxnot
        change x ∈ S.biUnion (fun z => H.neighborFinset z)
        rw [Finset.mem_biUnion]
        exact ⟨y, hy, (H.mem_neighborFinset y x).mpr hxy.symm⟩
      have hSind' := hSind
      rw [SimpleGraph.isIndepSet_iff] at hSind'
      have hinsert : H.IsIndepSet (↑(insert x S) : Set V) := by
        rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hab hadj
        have ha' : a = x ∨ a ∈ S := by simpa using ha
        have hb' : b = x ∨ b ∈ S := by simpa using hb
        rcases ha' with rfl | haS
        · rcases hb' with hbx | hbS
          · exact hab hbx.symm
          · exact hno b hbS hadj
        · rcases hb' with hbx | hbS
          · subst b
            exact hno a haS hadj.symm
          · exact hSind' haS hbS hab hadj
      have hle := SimpleGraph.IsIndepSet.card_le_indepNum
        (t := insert x S) hinsert
      rw [Finset.card_insert_of_notMem hxS, hScard] at hle
      omega
    exact Finset.mem_union_right _ hxU
  have hUcard : U.card ≤ ∑ x ∈ S, (H.neighborFinset x).card := by
    exact Finset.card_biUnion_le
  have hsum : (∑ x ∈ S, (H.neighborFinset x).card) ≤
      S.card * H.maxDegree := by
    calc
      (∑ x ∈ S, (H.neighborFinset x).card) ≤
          ∑ _x ∈ S, H.maxDegree := by
        apply Finset.sum_le_sum
        intro x _
        rw [H.card_neighborFinset_eq_degree]
        exact H.degree_le_maxDegree x
      _ = S.card * H.maxDegree := by simp
  have hcardUnion := Finset.card_union_le S U
  have huniv : Fintype.card V ≤ (S ∪ U).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hcover
  calc
    Fintype.card V ≤ (S ∪ U).card := huniv
    _ ≤ S.card + U.card := hcardUnion
    _ ≤ S.card + S.card * H.maxDegree := Nat.add_le_add_left (hUcard.trans hsum) _
    _ = S.card * (H.maxDegree + 1) := by ring
    _ = H.indepNum * (H.maxDegree + 1) := by rw [hScard]

/-- In any `C₄`-free graph whose degrees lie below `2d-2`, the conflict
degree is at most `(2d-2)(2d-3)`. -/
theorem degree_commonNeighborConflict_le_of_degree_le_two_mul_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hupper : ∀ v, G.degree v ≤ 2 * d - 2) (x : V) :
    (commonNeighborConflict G).degree x ≤
      (2 * d - 2) * (2 * d - 3) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_commonNeighborConflict_eq_biUnion_conflictBranch,
    Finset.card_biUnion (conflictBranch_pairwiseDisjoint G hfree x)]
  have hterm : ∀ y : {z : V // z ∈ G.neighborSet x},
      (conflictBranch G x y).card ≤ 2 * d - 3 := by
    intro y
    rw [conflictBranch, Finset.card_erase_of_mem]
    · rw [G.card_neighborFinset_eq_degree]
      have hy := hupper y.1
      omega
    · exact (G.mem_neighborFinset y.1 x).mpr y.2.symm
  calc
    (∑ y : {z : V // z ∈ G.neighborSet x},
        (conflictBranch G x y).card) ≤
        ∑ _y : {z : V // z ∈ G.neighborSet x}, (2 * d - 3) :=
      Finset.sum_le_sum fun y _ => hterm y
    _ = G.degree x * (2 * d - 3) := by
      rw [Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_neighborSet_eq_degree]
      simp
    _ ≤ (2 * d - 2) * (2 * d - 3) :=
      Nat.mul_le_mul_right _ (hupper x)

/-- **Sharp cubic localization of plateau cores.**  The conflict graph
greedy bound and the universal plateau degree window improve the coarse
prime-band constant `400` to a leading constant `4`. -/
theorem C4PlateauCore.order_le_conflict_cubic
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    m ≤ (d - 1) * ((2 * d - 2) * (2 * d - 3) + 1) := by
  have hd : 2 ≤ d := hcore.two_le_degree hm
  rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  have hno : ¬ C4FreeMinDegreeWitness (m + 1) d := by
    rintro ⟨H, hHdec, hHmin, hHfree⟩
    exact hHfree (hnext H hHdec hHmin)
  have hupper : ∀ x, G.degree x ≤ 2 * d - 2 :=
    degree_le_two_mul_sub_two_of_not_witness_succ
      G (N := m) (by simp) hmin.ge hfree (by omega) hno
  let C := commonNeighborConflict G
  have hCdeg : ∀ x, C.degree x ≤ (2 * d - 2) * (2 * d - 3) := by
    intro x
    exact degree_commonNeighborConflict_le_of_degree_le_two_mul_sub_two
      G hfree hd hupper x
  have hCmax : C.maxDegree ≤ (2 * d - 2) * (2 * d - 3) :=
    C.maxDegree_le_of_forall_degree_le _ hCdeg
  have hind : C.indepNum < d := by
    by_contra hnot
    have hind' : d ≤ C.indepNum := by omega
    obtain ⟨H, hHdec, hHmin, hHfree⟩ :=
      c4FreeMinDegreeWitness_succ_of_conflict_indepNum
        G hmin.ge hfree hind'
    exact hHfree (hnext H hHdec hHmin)
  have hgreedy := card_le_indepNum_mul_maxDegree_add_one C
  have halpha : C.indepNum ≤ d - 1 := by omega
  have hproduct : C.indepNum * (C.maxDegree + 1) ≤
      (d - 1) * ((2 * d - 2) * (2 * d - 3) + 1) :=
    Nat.mul_le_mul halpha (Nat.add_le_add_right hCmax 1)
  simpa using hgreedy.trans hproduct

end Erdos85
