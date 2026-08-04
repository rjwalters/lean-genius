import Proofs.Erdos85PolarityTwoPointCore

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

theorem twoPointCore_degree_eq_card_add_one_of_clean {a b : P K}
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hvnon : ¬ Projectivization.orthogonal v.1 v.1)
    (hva : ¬ (graph K).Adj v.1 a) (hvb : ¬ (graph K).Adj v.1 b) :
    (twoPointCore K).degree v = Nat.card K + 1 := by
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b} : Finset (P K)) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  have hzero : ((graph K).neighborFinset v.1 ∩
      ({a,b} : Finset (P K))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz.2 with rfl | rfl
    · exact hva (by simpa using hz.1)
    · exact hvb (by simpa using hz.1)
  change (twoPointCore K).degree v + _ = Nat.card K + 1 at hs
  rw [hzero, Nat.add_zero] at hs
  exact hs

theorem twoPointCore_card_sub_one_le_degree {a b : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))}) :
    Nat.card K - 1 ≤ (twoPointCore K).degree v := by
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b} : Finset (P K)) v
  by_cases hvabs : Projectivization.orthogonal v.1 v.1
  · have hzero := card_neighborFinset_inter_eq_zero_of_absolute_set K
      ({a,b} : Finset (P K)) (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hb) v hvabs
    rw [degree_eq_card_of_selfOrthogonal hvabs] at hs
    change (twoPointCore K).degree v + _ = Nat.card K at hs
    rw [hzero] at hs
    omega
  · rw [degree_eq_card_add_one_of_not_selfOrthogonal hvabs] at hs
    have hinc : ((graph K).neighborFinset v.1 ∩
        ({a,b} : Finset (P K))).card ≤ 2 := by
      calc
        _ ≤ ({a,b} : Finset (P K)).card :=
          Finset.card_le_card Finset.inter_subset_right
        _ ≤ 2 := by
          exact (Finset.card_insert_le a {b}).trans_eq (by simp)
    change (twoPointCore K).degree v + _ = Nat.card K + 1 at hs
    omega

theorem neighbor_defect_clean {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hvx : (twoPointCore K).Adj v (twoPointDefect K ha hb hab)) :
    ¬ Projectivization.orthogonal v.1 v.1 ∧
      ¬ (graph K).Adj v.1 a ∧ ¬ (graph K).Adj v.1 b := by
  have hvnot : v.1 ≠ a ∧ v.1 ≠ b := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using v.2
  have hvxfull := SimpleGraph.induce_adj.mp hvx
  have hs := absolutePairCommonNeighbor_spec K ha hb hab
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro hvabs
    exact not_adj_absolutePairCommonNeighbor_of_third_absolute K h2 ha hb hab
      hvabs hvnot.1 hvnot.2 (by simpa [twoPointDefect] using hvxfull.symm)
  refine ⟨hvnon, ?_, ?_⟩
  · intro hva
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := (absolutePairCommonNeighbor K ha hb hab)) (w := a)
      hs.1.symm ha
    have hm : v.1 ∈ (graph K).neighborFinset
        (absolutePairCommonNeighbor K ha hb hab) ∩ (graph K).neighborFinset a := by
      rw [Finset.mem_inter]
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [twoPointDefect] using hvxfull.symm, hva.symm⟩
    rw [hempty] at hm
    simp at hm
  · intro hvb
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := (absolutePairCommonNeighbor K ha hb hab)) (w := b)
      hs.2.1.symm hb
    have hm : v.1 ∈ (graph K).neighborFinset
        (absolutePairCommonNeighbor K ha hb hab) ∩ (graph K).neighborFinset b := by
      rw [Finset.mem_inter]
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [twoPointDefect] using hvxfull.symm, hvb.symm⟩
    rw [hempty] at hm
    simp at hm

theorem degree_neighbor_defect_eq_card_add_one {a b : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hvx : (twoPointCore K).Adj v (twoPointDefect K ha hb hab)) :
    (twoPointCore K).degree v = Nat.card K + 1 := by
  obtain ⟨hvnon, hva, hvb⟩ := neighbor_defect_clean K h2 ha hb hab v hvx
  exact twoPointCore_degree_eq_card_add_one_of_clean K v hvnon hva hvb

theorem cross_opposite_clean {a b w : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (hw : Projectivization.orthogonal w w) (hwa : w ≠ a) (hwb : w ≠ b)
    (v u : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hvw : (twoPointCore K).Adj v (thirdAbsoluteVertex K hwa hwb))
    (hux : (twoPointCore K).Adj u (twoPointDefect K ha hb hab))
    (hvu : (twoPointCore K).Adj v u) :
    ¬ Projectivization.orthogonal v.1 v.1 ∧
      ¬ (graph K).Adj v.1 a ∧ ¬ (graph K).Adj v.1 b := by
  have hvwfull := SimpleGraph.induce_adj.mp hvw
  have huxfull := SimpleGraph.induce_adj.mp hux
  have hvufull := SimpleGraph.induce_adj.mp hvu
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 :=
    not_selfOrthogonal_of_adj_selfOrthogonal
      (by simpa [thirdAbsoluteVertex] using hvwfull.symm) hw
  have hxv : absolutePairCommonNeighbor K ha hb hab ≠ v.1 := by
    intro heq
    apply twoPointCore_not_adj_defect_thirdAbsolute K h2 ha hb hab hw hwa hwb
    simpa [twoPointDefect, thirdAbsoluteVertex, heq] using hvw
  refine ⟨hvnon, ?_, ?_⟩
  · intro hva
    have hle := Finset.card_le_one.mp
      (commonNeighbors_le_one (absolutePairCommonNeighbor K ha hb hab) v.1 hxv)
    have hau : a = u.1 := hle a
      (by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨(absolutePairCommonNeighbor_spec K ha hb hab).1.symm, hva⟩)
      u.1 (by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨by simpa [twoPointDefect] using huxfull.symm, hvufull⟩)
    exact u.2 (by simp [← hau])
  · intro hvb
    have hle := Finset.card_le_one.mp
      (commonNeighbors_le_one (absolutePairCommonNeighbor K ha hb hab) v.1 hxv)
    have hbu : b = u.1 := hle b
      (by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨(absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm, hvb⟩)
      u.1 (by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨by simpa [twoPointDefect] using huxfull.symm, hvufull⟩)
    exact u.2 (by simp [← hbu])

theorem degree_eq_card_add_one_of_positive_tangent_crossLoss {a b w : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (hw : Projectivization.orthogonal w w) (hwa : w ≠ a) (hwb : w ≠ b)
    (v : {v : P K // v ∉ ({a,b} : Finset (P K))})
    (hloss : 1 ≤ crossEdgeLoss (twoPointCore K)
      ((twoPointCore K).neighborFinset (twoPointDefect K ha hb hab))
      ((twoPointCore K).neighborFinset (thirdAbsoluteVertex K hwa hwb)) v) :
    (twoPointCore K).degree v = Nat.card K + 1 := by
  classical
  rw [crossEdgeLoss, Finset.one_le_card] at hloss
  obtain ⟨u, hu⟩ := hloss
  rw [Finset.mem_filter] at hu
  have hvu : (twoPointCore K).Adj v u := by simpa using hu.1
  rw [pair_mem_crossEdgeSet_iff] at hu
  rcases hu.2 with ⟨hvx, huw⟩ | ⟨hvw, hux⟩
  · exact degree_neighbor_defect_eq_card_add_one K h2 ha hb hab v
      ((by simpa using hvx : (twoPointCore K).Adj
        (twoPointDefect K ha hb hab) v).symm)
  · obtain ⟨hvnon, hva, hvb⟩ := cross_opposite_clean K h2 ha hb hab
      hw hwa hwb v u
      ((by simpa using hvw : (twoPointCore K).Adj
        (thirdAbsoluteVertex K hwa hwb) v).symm)
      ((by simpa using hux : (twoPointCore K).Adj
        (twoPointDefect K ha hb hab) u).symm) hvu
    exact twoPointCore_degree_eq_card_add_one_of_clean K v hvnon hva hvb

theorem c4FreeMinDegreeWitness_twoPoint_tangent_switch {a b w : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b)
    (hw : Projectivization.orthogonal w w) (hwa : w ≠ a) (hwb : w ≠ b) :
    C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - 2) (Nat.card K) := by
  let H := twoPointCore K (a := a) (b := b)
  let x := twoPointDefect K ha hb hab
  let y := thirdAbsoluteVertex K hwa hwb
  letI : DecidableRel (crossEdgeSwitch H x y).Adj := Classical.decRel _
  letI : DecidableRel
      (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)).Adj :=
    Classical.decRel _
  have hcard : Fintype.card {v : P K // v ∉ ({a,b} : Finset (P K))} =
      (Nat.card K + 1) * Nat.card K + 1 - 2 := by
    rw [Fintype.card_subtype_compl]
    rw [Fintype.card_eq_nat_card, card_points_tight K]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [Fintype.card_subtype_eq_or_eq_of_ne hab]
  have hfree : ¬ containsC4 _ H := by
    intro hc
    apply graph_not_containsC4 (K := K)
    rcases hc with ⟨f, hf, hadj⟩
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => SimpleGraph.induce_adj.mp (hadj i j hij)⟩
  have hxy : ¬ H.Adj x y :=
    twoPointCore_not_adj_defect_thirdAbsolute K h2 ha hb hab hw hwa hwb
  have hne : x ≠ y := by
    intro h
    have hp : x.1 = y.1 := congrArg Subtype.val h
    apply (absolutePairCommonNeighbor_spec K ha hb hab).2.2
    have hp' : absolutePairCommonNeighbor K ha hb hab = w := by
      simpa [x, y, twoPointDefect, thirdAbsoluteVertex] using hp
    rw [hp']
    exact hw
  have htangent : ∀ z, H.Adj z y →
      H.neighborFinset z ∩ H.neighborFinset y = ∅ := by
    intro z hz
    exact twoPointCore_tangent_thirdAbsolute K hwa hwb hw z hz
  apply c4FreeMinDegreeWitness_crossEdgeSwitch_of_unique_defect
    H x y hcard hfree hxy hne
  · have hxS : x ∉ H.neighborFinset x := by simp
    have hxT : x ∉ H.neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset]
      exact fun h => hxy h.symm
    have hloss := crossEdgeLoss_eq_zero_of_not_mem H
      (H.neighborFinset x) (H.neighborFinset y) x hxS hxT
    have hsplit := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) x
    have hxdeg := twoPointDefect_degree K ha hb hab
    change H.degree x = Nat.card K - 1 at hxdeg
    omega
  · intro v hvx
    have hlossle := crossEdgeLoss_neighborFinsets_le_one_of_tangent_right
      H x y v hfree hxy htangent
    have hsplit := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    by_cases hloss0 : crossEdgeLoss H (H.neighborFinset x)
        (H.neighborFinset y) v = 0
    · have hbase := twoPointCore_card_sub_one_le_degree K ha hb v
      change Nat.card K - 1 ≤ H.degree v at hbase
      have hneq : H.degree v ≠ Nat.card K - 1 := by
        intro heq
        have := eq_twoPointDefect_of_degree_eq_sub_one K ha hb hab v
          (by simpa [H] using heq)
        exact hvx (by simpa [x] using this)
      omega
    · have hpos : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
          (H.neighborFinset y) v := Nat.one_le_iff_ne_zero.mpr hloss0
      have hhigh := degree_eq_card_add_one_of_positive_tangent_crossLoss
        K h2 ha hb hab hw hwa hwb v (by simpa [H, x, y] using hpos)
      change H.degree v = Nat.card K + 1 at hhigh
      omega

theorem c4FreeMinDegreeWitness_odd_tangent_switch
    (h2 : (2 : K) ≠ 0) :
    C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - 2) (Nat.card K) := by
  classical
  have hq3 := three_le_card_of_two_ne_zero K h2
  have hcabs := card_absolutePoints_eq_card_add_one K
  obtain ⟨a, ha, _⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (∅ : Finset (P K))) (t := absolutePoints K) (by rw [hcabs]; simp)
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a} : Finset (P K))) (t := absolutePoints K) (by rw [hcabs]; simp)
  have ha' := (mem_absolutePoints K a).mp ha
  have hb' := (mem_absolutePoints K b).mp hb
  have hab : a ≠ b := (by simpa using hba : b ≠ a).symm
  obtain ⟨w, hw, hwa, hwb⟩ := exists_third_absolute K h2 ha' hb' hab
  exact c4FreeMinDegreeWitness_twoPoint_tangent_switch K h2 ha' hb' hab
    hw hwa hwb

theorem minDegreeForC4_odd_twoPoint_order
    (h2 : (2 : K) ≠ 0) :
    minDegreeForC4 ((Nat.card K + 1) * Nat.card K + 1 - 2) =
      Nat.card K + 1 := by
  have hq3 := three_le_card_of_two_ne_zero K h2
  have horder : 4 ≤ (Nat.card K + 1) * Nat.card K + 1 - 2 := by
    apply Nat.le_sub_of_add_le
    nlinarith
  apply le_antisymm
  · exact (minDegreeForC4_odd_absolute_band_bounds K h2
      (k := 2) (by omega)).2
  · have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 horder).1
      (c4FreeMinDegreeWitness_odd_tangent_switch K h2)
    omega

end Erdos85.Polarity
