import Proofs.Erdos85PolarityThreePointCore
import Proofs.Erdos85CrossEdgeSwitch
import Proofs.Erdos85CrossEdgeSwitchCascade

/-! The first dynamic switch between two of the three pair-pole defects. -/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

/-- Pair poles sharing the absolute point `a` are nonadjacent in the
three-point core. -/
theorem centerPairDefect_not_adj_outerAC
    {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) :
    ¬ (threePointCore K).Adj
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac) := by
  intro hxy
  have hbase := SimpleGraph.induce_adj.mp hxy
  have hxa := (absolutePairCommonNeighbor_spec K ha hb hab).1
  have hya := (absolutePairCommonNeighbor_spec K ha hc hac).1
  have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
    (K := K) (z := absolutePairCommonNeighbor K ha hb hab) (w := a)
    hxa.symm ha
  have hm : absolutePairCommonNeighbor K ha hc hac ∈
      (graph K).neighborFinset (absolutePairCommonNeighbor K ha hb hab) ∩
      (graph K).neighborFinset a := by
    rw [Finset.mem_inter]
    simp only [SimpleGraph.mem_neighborFinset]
    exact ⟨by simpa [threePointPairDefect, threePointOuterPairDefectAC] using hbase,
      hya⟩
  rw [hempty] at hm
  simp at hm

/-- Their only full-graph common neighbor is the deleted shared absolute
point, so their core neighborhoods are disjoint. -/
theorem centerPairDefect_neighborFinset_inter_outerAC_eq_empty
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).neighborFinset
        (threePointPairDefect K ha hb hc hab) ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have rb : r.1 ∈ (graph K).neighborFinset
      (absolutePairCommonNeighbor K ha hb hab) ∩
      (graph K).neighborFinset
        (absolutePairCommonNeighbor K ha hc hac) := by
    rw [Finset.mem_inter]
    exact ⟨by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp
        ((threePointCore K).mem_neighborFinset _ r |>.mp
          (Finset.mem_inter.mp hr).1), by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp
        ((threePointCore K).mem_neighborFinset _ r |>.mp
          (Finset.mem_inter.mp hr).2)⟩
  rw [pairPole_neighborFinset_inter_eq_singleton_shared K
    h2 ha hb hc hab hac hbc] at rb
  have hra : r.1 = a := Finset.mem_singleton.mp rb
  exact r.2 (by simp [hra])

/-- The only degree-`q-1` vertices after three absolute deletions are the
three pair poles. -/
theorem eq_one_of_threePairDefects_of_degree_eq_sub_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hvdeg : (threePointCore K).degree v = Nat.card K - 1) :
    v = threePointPairDefect K ha hb hc hab ∨
      v = threePointOuterPairDefectAC K ha hb hc hac ∨
      v = threePointOuterPairDefectBC K ha hb hc hbc := by
  classical
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) v
  have hq := three_le_card_of_two_ne_zero K h2
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro hvabs
    rw [degree_eq_card_of_selfOrthogonal hvabs] at hs
    change (threePointCore K).degree v + _ = Nat.card K at hs
    have hzero := card_neighborFinset_inter_eq_zero_of_absolute_set K
      ({a,b,c} : Finset (P K)) (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption) v hvabs
    rw [hvdeg, hzero] at hs
    omega
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  change (threePointCore K).degree v + _ = Nat.card K + 1 at hs
  rw [hvdeg] at hs
  have hinc : ((graph K).neighborFinset v.1 ∩
      ({a,b,c} : Finset (P K))).card = 2 := by omega
  let I := (graph K).neighborFinset v.1 ∩ ({a,b,c} : Finset (P K))
  have force_mem (t : P K) (ht : t ∈ ({a,b,c} : Finset (P K)))
      (hsub : I ⊆ {t}) : False := by
    have hcI := Finset.card_le_card hsub
    have : I.card = 2 := hinc
    simp at hcI
    omega
  by_cases hva : (graph K).Adj a v.1
  · by_cases hvb : (graph K).Adj b v.1
    · left
      apply Subtype.ext
      exact (Classical.choose_spec
        (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hb hab)).2
          v.1 ⟨hva, hvb, hvnon⟩
    · right; left
      have hvc : (graph K).Adj c v.1 := by
        by_contra hvc
        exfalso
        apply force_mem a (by simp) ?_
        intro z hz
        rcases Finset.mem_inter.mp hz with ⟨hvz, hzD⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
        rcases hzD with rfl | rfl | rfl
        · simp
        · exact (hvb (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
        · exact (hvc (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
      apply Subtype.ext
      change v.1 = absolutePairCommonNeighbor K ha hc hac
      exact (Classical.choose_spec
          (existsUnique_nonabsolute_commonNeighbor_of_absolute K ha hc hac)).2
            v.1 ⟨hva, hvc, hvnon⟩
  · by_cases hvb : (graph K).Adj b v.1
    · right; right
      have hvc : (graph K).Adj c v.1 := by
        by_contra hvc
        exfalso
        apply force_mem b (by simp) ?_
        intro z hz
        rcases Finset.mem_inter.mp hz with ⟨hvz, hzD⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
        rcases hzD with rfl | rfl | rfl
        · exact (hva (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
        · simp
        · exact (hvc (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
      apply Subtype.ext
      change v.1 = absolutePairCommonNeighbor K hb hc hbc
      exact (Classical.choose_spec
          (existsUnique_nonabsolute_commonNeighbor_of_absolute K hb hc hbc)).2
            v.1 ⟨hvb, hvc, hvnon⟩
    · exfalso
      apply force_mem c (by simp) ?_
      intro z hz
      rcases Finset.mem_inter.mp hz with ⟨hvz, hzD⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
      rcases hzD with rfl | rfl | rfl
      · exact (hva (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
      · exact (hvb (((graph K).mem_neighborFinset v.1 _).mp hvz).symm).elim
      · simp

/-- Every vertex of the three-point core has degree at least `q-1`. -/
theorem threePointCore_card_sub_one_le_degree
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))}) :
    Nat.card K - 1 ≤ (threePointCore K).degree v := by
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) v
  by_cases hvabs : Projectivization.orthogonal v.1 v.1
  · rw [degree_eq_card_of_selfOrthogonal hvabs] at hs
    have hzero := card_neighborFinset_inter_eq_zero_of_absolute_set K
      ({a,b,c} : Finset (P K)) (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption) v hvabs
    change (threePointCore K).degree v + _ = Nat.card K at hs
    rw [hzero] at hs
    omega
  · rw [degree_eq_card_add_one_of_not_selfOrthogonal hvabs] at hs
    have hinc : ((graph K).neighborFinset v.1 ∩
        ({a,b,c} : Finset (P K))).card ≤ 2 :=
      card_neighborFinset_inter_le_two_of_subset_absolute K
        (absoluteTwoSecant_of_two_ne_zero K h2) ({a,b,c} : Finset (P K))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption) v hvabs
    change (threePointCore K).degree v + _ = Nat.card K + 1 at hs
    omega

/-- A nonabsolute vertex adjacent to none of the deleted absolutes retains
full degree `q+1`. -/
theorem threePointCore_degree_eq_card_add_one_of_clean
    {a b c : P K}
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hvnon : ¬ Projectivization.orthogonal v.1 v.1)
    (hva : ¬ (graph K).Adj a v.1) (hvb : ¬ (graph K).Adj b v.1)
    (hvc : ¬ (graph K).Adj c v.1) :
    (threePointCore K).degree v = Nat.card K + 1 := by
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvnon] at hs
  have hzero : ((graph K).neighborFinset v.1 ∩
      ({a,b,c} : Finset (P K))).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hvz, hzD⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzD
    rcases hzD with rfl | rfl | rfl
    · exact hva (((graph K).mem_neighborFinset v.1 _).mp hvz).symm
    · exact hvb (((graph K).mem_neighborFinset v.1 _).mp hvz).symm
    · exact hvc (((graph K).mem_neighborFinset v.1 _).mp hvz).symm
  change (threePointCore K).degree v + _ = Nat.card K + 1 at hs
  rw [hzero] at hs
  exact hs

/-- Every vertex hit by the first defect-pair cross deletion has full one-unit
slack: its old core degree is `q+1`. -/
theorem degree_eq_card_add_one_of_positive_firstPair_crossLoss
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hloss : 1 ≤ crossEdgeLoss (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac)) v) :
    (threePointCore K).degree v = Nat.card K + 1 := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointPairDefect K ha hb hc hab
  let y : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointOuterPairDefectAC K ha hb hc hac
  change 1 ≤ crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) v at hloss
  rw [crossEdgeLoss, Finset.one_le_card] at hloss
  obtain ⟨u, hu⟩ := hloss
  rw [Finset.mem_filter] at hu
  obtain ⟨huAdj, huCross⟩ := hu
  rw [pair_mem_crossEdgeSet_iff] at huCross
  have hvu : H.Adj v u := by simpa only [SimpleGraph.mem_neighborFinset] using huAdj
  have hbasevu : (graph K).Adj v.1 u.1 := SimpleGraph.induce_adj.mp hvu
  rcases huCross with hcase | hcase
  · have hvx : H.Adj x v := by simpa only [SimpleGraph.mem_neighborFinset] using hcase.1
    have huy : H.Adj y u := by simpa only [SimpleGraph.mem_neighborFinset] using hcase.2
    have hbasexv := SimpleGraph.induce_adj.mp hvx
    have hbaseyu := SimpleGraph.induce_adj.mp huy
    have hva : ¬ (graph K).Adj a v.1 := by
      intro hav
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := x.1) (w := a)
        (by simpa [x, threePointPairDefect] using
          (absolutePairCommonNeighbor_spec K ha hb hab).1.symm) ha
      have hm : v.1 ∈ (graph K).neighborFinset x.1 ∩
          (graph K).neighborFinset a := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hbasexv, hav⟩
      rw [hempty] at hm; simp at hm
    have hvb : ¬ (graph K).Adj b v.1 := by
      intro hbv
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := x.1) (w := b)
        (by simpa [x, threePointPairDefect] using
          (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm) hb
      have hm : v.1 ∈ (graph K).neighborFinset x.1 ∩
          (graph K).neighborFinset b := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hbasexv, hbv⟩
      rw [hempty] at hm; simp at hm
    have hvc : ¬ (graph K).Adj c v.1 := by
      intro hcv
      have hcu : c ≠ u.1 := by
        intro h; exact u.2 (by simp [← h])
      have hle := commonNeighbors_le_one c u.1 hcu
      rw [Finset.card_le_one_iff] at hle
      have hvm : v.1 ∈ (graph K).neighborFinset c ∩
          (graph K).neighborFinset u.1 := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hcv, hbasevu.symm⟩
      have hym : y.1 ∈ (graph K).neighborFinset c ∩
          (graph K).neighborFinset u.1 := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨by simpa [y, threePointOuterPairDefectAC] using
            (absolutePairCommonNeighbor_spec K ha hc hac).2.1,
          hbaseyu.symm⟩
      have heq := hle hvm hym
      have heq' : v = y := Subtype.ext heq
      have hvxy : H.Adj x y := by simpa [heq'] using hvx
      exact (centerPairDefect_not_adj_outerAC K ha hb hc hab hac) hvxy
    have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
      intro hvabs
      have hva' : v.1 ≠ a := by intro h; exact v.2 (by simp [h])
      have hvb' : v.1 ≠ b := by intro h; exact v.2 (by simp [h])
      exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
        ha hb hab hvabs hva' hvb')
          (by simpa [x, threePointPairDefect] using hbasexv)
    exact threePointCore_degree_eq_card_add_one_of_clean K v hvnon hva hvb hvc
  · have hvy : H.Adj y v := by simpa only [SimpleGraph.mem_neighborFinset] using hcase.1
    have hux : H.Adj x u := by simpa only [SimpleGraph.mem_neighborFinset] using hcase.2
    have hbaseyv := SimpleGraph.induce_adj.mp hvy
    have hbasexu := SimpleGraph.induce_adj.mp hux
    have hva : ¬ (graph K).Adj a v.1 := by
      intro hav
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := y.1) (w := a)
        (by simpa [y, threePointOuterPairDefectAC] using
          (absolutePairCommonNeighbor_spec K ha hc hac).1.symm) ha
      have hm : v.1 ∈ (graph K).neighborFinset y.1 ∩
          (graph K).neighborFinset a := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hbaseyv, hav⟩
      rw [hempty] at hm; simp at hm
    have hvc : ¬ (graph K).Adj c v.1 := by
      intro hcv
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := y.1) (w := c)
        (by simpa [y, threePointOuterPairDefectAC] using
          (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm) hc
      have hm : v.1 ∈ (graph K).neighborFinset y.1 ∩
          (graph K).neighborFinset c := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hbaseyv, hcv⟩
      rw [hempty] at hm; simp at hm
    have hvb : ¬ (graph K).Adj b v.1 := by
      intro hbv
      have hbu : b ≠ u.1 := by intro h; exact u.2 (by simp [← h])
      have hle := commonNeighbors_le_one b u.1 hbu
      rw [Finset.card_le_one_iff] at hle
      have hvm : v.1 ∈ (graph K).neighborFinset b ∩
          (graph K).neighborFinset u.1 := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨hbv, hbasevu.symm⟩
      have hxm : x.1 ∈ (graph K).neighborFinset b ∩
          (graph K).neighborFinset u.1 := by
        rw [Finset.mem_inter]
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨by simpa [x, threePointPairDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).2.1,
          hbasexu.symm⟩
      have heq := hle hvm hxm
      have heq' : v = x := Subtype.ext heq
      have hyx : H.Adj y x := by simpa [heq'] using hvy
      exact (centerPairDefect_not_adj_outerAC K ha hb hc hab hac) hyx.symm
    have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
      intro hvabs
      have hva' : v.1 ≠ a := by intro h; exact v.2 (by simp [h])
      have hvc' : v.1 ≠ c := by intro h; exact v.2 (by simp [h])
      exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
        ha hc hac hvabs hva' hvc')
          (by simpa [y, threePointOuterPairDefectAC] using hbaseyv)
    exact threePointCore_degree_eq_card_add_one_of_clean K v hvnon hva hvb hvc

theorem threePointOuterPairDefectAC_degree {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).degree (threePointOuterPairDefectAC K ha hb hc hac) =
      Nat.card K - 1 := by
  let x := threePointOuterPairDefectAC K ha hb hc hac
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) x
  have hxnon : ¬ Projectivization.orthogonal x.1 x.1 := by
    simpa [x, threePointOuterPairDefectAC] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.2
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hxnon] at hs
  have hxb := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hc hac hb (Ne.symm hab) hbc
  have hinc : ((graph K).neighborFinset x.1 ∩
      ({a,b,c} : Finset (P K))).card = 2 := by
    have heq : (graph K).neighborFinset x.1 ∩ ({a,b,c} : Finset (P K)) = {a,c} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (hxb (by simpa [x, threePointOuterPairDefectAC] using hz)).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨by simpa [x, threePointOuterPairDefectAC] using
            (absolutePairCommonNeighbor_spec K ha hc hac).1.symm, Or.inl rfl⟩
        · exact ⟨by simpa [x, threePointOuterPairDefectAC] using
            (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm,
              Or.inr (Or.inr rfl)⟩
    rw [heq]
    simp [hac]
  change (threePointCore K).degree x + _ = Nat.card K + 1 at hs
  change (threePointCore K).degree x = Nat.card K - 1
  rw [hinc] at hs
  have hq := three_le_card_of_two_ne_zero K h2
  omega

/-- Switching the `{a,b}` and `{a,c}` pair poles leaves the `{b,c}` pole as
the unique sub-`q` vertex. -/
theorem firstPairPoleSwitch_unique_defect
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    let J := crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)
    J.degree (threePointOuterPairDefectBC K ha hb hc hbc) = Nat.card K - 1 ∧
      ∀ v ≠ threePointOuterPairDefectBC K ha hb hc hbc,
        Nat.card K ≤ J.degree v := by
  classical
  dsimp only
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointPairDefect K ha hb hc hab
  let y : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointOuterPairDefectAC K ha hb hc hac
  let z : {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointOuterPairDefectBC K ha hb hc hbc
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  let J := crossEdgeSwitch H x y
  have hxy : ¬ H.Adj x y := centerPairDefect_not_adj_outerAC K ha hb hc hab hac
  have hdisj : Disjoint (H.neighborFinset x) (H.neighborFinset y) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact centerPairDefect_neighborFinset_inter_outerAC_eq_empty K
      h2 ha hb hc hab hac hbc
  have hne : x ≠ y := by
    intro h
    exact (absolutePairCommonNeighbor_ne_shared K h2 ha hb hc hab hac hbc)
      (by simpa [x, y, threePointPairDefect,
        threePointOuterPairDefectAC] using congrArg Subtype.val h)
  have hxdeg : H.degree x = Nat.card K - 1 := by
    simpa [H, x] using threePointPairDefect_degree K h2 ha hb hc hab
      (Ne.symm hac) (Ne.symm hbc)
  have hydeg : H.degree y = Nat.card K - 1 := by
    simpa [H, y] using threePointOuterPairDefectAC_degree K h2
      ha hb hc hab hac hbc
  have hxloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) x = 0 := by
    apply crossEdgeLoss_eq_zero_of_not_mem
    · simpa only [SimpleGraph.mem_neighborFinset] using H.loopless.irrefl x
    · simpa only [SimpleGraph.mem_neighborFinset] using
        (fun h => hxy h.symm)
  have hyloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) y = 0 := by
    apply crossEdgeLoss_eq_zero_of_not_mem
    · simpa only [SimpleGraph.mem_neighborFinset] using hxy
    · simpa only [SimpleGraph.mem_neighborFinset] using H.loopless.irrefl y
  have hDx : D.degree x = Nat.card K - 1 := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) x
    change H.degree x = D.degree x + _ at hs
    rw [hxdeg, hxloss] at hs
    omega
  have hDy : D.degree y = Nat.card K - 1 := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) y
    change H.degree y = D.degree y + _ at hs
    rw [hydeg, hyloss] at hs
    omega
  have hJx : J.degree x = Nat.card K := by
    have hs := crossEdgeSwitch_degree_left H x y hxy hne
    change J.degree x = D.degree x + 1 at hs
    rw [hDx] at hs
    have hq := three_le_card_of_two_ne_zero K h2
    omega
  have hJy : J.degree y = Nat.card K := by
    have hs := crossEdgeSwitch_degree_right H x y hxy hne
    change J.degree y = D.degree y + 1 at hs
    rw [hDy] at hs
    have hq := three_le_card_of_two_ne_zero K h2
    omega
  -- The third pole belongs to neither switched neighborhood.
  have hxz : ¬ H.Adj x z := by
    intro hxz
    have hbase := SimpleGraph.induce_adj.mp hxz
    have hxb := (absolutePairCommonNeighbor_spec K ha hb hab).2.1
    have hzb := (absolutePairCommonNeighbor_spec K hb hc hbc).1
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := x.1) (w := b)
      (by simpa [x, threePointPairDefect] using hxb.symm) hb
    have hm : z.1 ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset b := by
      rw [Finset.mem_inter]
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, by simpa [z, threePointOuterPairDefectBC] using hzb⟩
    rw [hempty] at hm; simp at hm
  have hyz : ¬ H.Adj y z := by
    intro hyz
    have hbase := SimpleGraph.induce_adj.mp hyz
    have hnot := centerPairDefect_not_adj_outerAC K hb ha hc hab.symm hbc
    -- The swapped core has the same underlying deleted set; use tangency at `c` directly.
    have hyc := (absolutePairCommonNeighbor_spec K ha hc hac).2.1
    have hzc := (absolutePairCommonNeighbor_spec K hb hc hbc).2.1
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := y.1) (w := c)
      (by simpa [y, threePointOuterPairDefectAC] using hyc.symm) hc
    have hm : z.1 ∈ (graph K).neighborFinset y.1 ∩
        (graph K).neighborFinset c := by
      rw [Finset.mem_inter]
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨hbase, by simpa [z, threePointOuterPairDefectBC] using hzc⟩
    rw [hempty] at hm; simp at hm
  have hzloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) z = 0 := by
    apply crossEdgeLoss_eq_zero_of_not_mem <;>
      simpa only [SimpleGraph.mem_neighborFinset]
  have hzdeg : H.degree z = Nat.card K - 1 := by
    -- Symmetric direct degree computation follows from the classified defect.
    have hbase := threePointCore_card_sub_one_le_degree K h2 ha hb hc z
    have hclass : z = x ∨ z = y ∨ z = z := Or.inr (Or.inr rfl)
    -- Its defining pole is adjacent to `b,c` and not to `a`.
    let za := absolutePairCommonNeighbor K hb hc hbc
    have hs := degree_deleteVertexSetGraph_add (graph K)
      ({a,b,c} : Finset (P K)) z
    have hznon : ¬ Projectivization.orthogonal z.1 z.1 := by
      simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
    rw [degree_eq_card_add_one_of_not_selfOrthogonal hznon] at hs
    have hinc : ((graph K).neighborFinset z.1 ∩
        ({a,b,c} : Finset (P K))).card = 2 := by
      have heq : (graph K).neighborFinset z.1 ∩ ({a,b,c} : Finset (P K)) = {b,c} := by
        ext t
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨ht, rfl | rfl | rfl⟩
          · exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
              hb hc hbc ha hab hac (by simpa [z, threePointOuterPairDefectBC] using ht)).elim
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨by simpa [z, threePointOuterPairDefectBC] using
              (absolutePairCommonNeighbor_spec K hb hc hbc).1.symm,
              Or.inr (Or.inl rfl)⟩
          · exact ⟨by simpa [z, threePointOuterPairDefectBC] using
              (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm,
              Or.inr (Or.inr rfl)⟩
      rw [heq]
      simp [hbc]
    change H.degree z + _ = Nat.card K + 1 at hs
    change H.degree z = Nat.card K - 1
    rw [hinc] at hs
    have hq := three_le_card_of_two_ne_zero K h2
    omega
  have hDz : D.degree z = Nat.card K - 1 := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) z
    change H.degree z = D.degree z + _ at hs
    rw [hzdeg, hzloss] at hs
    omega
  have hzx : z ≠ x := by
    intro heq
    have hnot := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    have hxa := (absolutePairCommonNeighbor_spec K ha hb hab).1
    have heqv : z.1 = x.1 := congrArg Subtype.val heq
    have hzadj : (graph K).Adj z.1 a := by rw [heqv]; simpa [x,
      threePointPairDefect] using hxa.symm
    exact hnot (by simpa [z, threePointOuterPairDefectBC] using hzadj)
  have hzy : z ≠ y := by
    intro heq
    have hnot := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    have hya := (absolutePairCommonNeighbor_spec K ha hc hac).1
    have heqv : z.1 = y.1 := congrArg Subtype.val heq
    have hzadj : (graph K).Adj z.1 a := by rw [heqv]; simpa [y,
      threePointOuterPairDefectAC] using hya.symm
    exact hnot (by simpa [z, threePointOuterPairDefectBC] using hzadj)
  have hJz : J.degree z = Nat.card K - 1 := by
    rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints H x y z]
    · exact hDz
    · exact hzx
    · exact hzy
  refine ⟨by simpa [J, z] using hJz, ?_⟩
  intro v hvz
  change Nat.card K ≤ J.degree v
  by_cases hvx : v = x
  · rw [hvx, hJx]
  by_cases hvy : v = y
  · rw [hvy, hJy]
  have hbase : Nat.card K ≤ H.degree v := by
    have hlo := threePointCore_card_sub_one_le_degree K h2 ha hb hc v
    change Nat.card K - 1 ≤ H.degree v at hlo
    have hq := three_le_card_of_two_ne_zero K h2
    by_contra hnot
    have heq : H.degree v = Nat.card K - 1 := by omega
    have hclass := eq_one_of_threePairDefects_of_degree_eq_sub_one K
      h2 ha hb hc hab hac hbc v (by simpa [H] using heq)
    rcases hclass with he | he | he
    · exact hvx (by simpa [x] using he)
    · exact hvy (by simpa [y] using he)
    · exact hvz (by simpa [z] using he)
  by_cases hloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) v = 0
  · have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    have hDJ := degree_deleteCrossEdges_le_crossEdgeSwitch H x y v
    change H.degree v = D.degree v + _ at hs
    change D.degree v ≤ J.degree v at hDJ
    omega
  · have hp : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
        (H.neighborFinset y) v := Nat.one_le_iff_ne_zero.mpr hloss
    have hhigh := degree_eq_card_add_one_of_positive_firstPair_crossLoss K
      h2 ha hb hc hab hac hbc v (by simpa [H, x, y] using hp)
    have hHfree : ¬ containsC4 _ H := by
      rintro ⟨f, hinj, hadj⟩
      apply graph_not_containsC4 (K := K)
      refine ⟨fun i => (f i).1, ?_, ?_⟩
      · intro i j hij
        apply hinj
        exact Subtype.ext hij
      · intro i j hij
        exact SimpleGraph.induce_adj.mp (hadj i j hij)
    have hlossle := crossEdgeLoss_neighborFinsets_le_one H x y v
      hHfree hxy hdisj
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    have hDJ := degree_deleteCrossEdges_le_crossEdgeSwitch H x y v
    change H.degree v = D.degree v + _ at hs
    change D.degree v ≤ J.degree v at hDJ
    change H.degree v = Nat.card K + 1 at hhigh
    omega

/-- Every surviving absolute point stays target-tight of degree `q` through
the first dynamic defect-pair switch. -/
theorem firstPairPoleSwitch_degree_surviving_absolute
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hvabs : Projectivization.orthogonal v.1 v.1)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj] :
    (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).degree v = Nat.card K := by
  classical
  let H : SimpleGraph {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    threePointCore K
  let x := threePointPairDefect K ha hb hc hab
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  let J := crossEdgeSwitch H x y
  have hva : v.1 ≠ a := by intro h; exact v.2 (by simp [h])
  have hvb : v.1 ≠ b := by intro h; exact v.2 (by simp [h])
  have hvc : v.1 ≠ c := by intro h; exact v.2 (by simp [h])
  have hxv : ¬ H.Adj x v := by
    intro h
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab hvabs hva hvb)
        (by simpa [H, x, threePointPairDefect] using SimpleGraph.induce_adj.mp h)
  have hyv : ¬ H.Adj y v := by
    intro h
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hc hac hvabs hva hvc)
        (by simpa [H, y, threePointOuterPairDefectAC] using SimpleGraph.induce_adj.mp h)
  have hloss : crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset y) v = 0 := by
    apply crossEdgeLoss_eq_zero_of_not_mem <;>
      simpa only [SimpleGraph.mem_neighborFinset]
  have hbase : H.degree v = Nat.card K := by
    simpa [H] using threePointCore_degree_surviving_absolute K ha hb hc v hvabs
  have hD : D.degree v = Nat.card K := by
    have hs := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset y) v
    change H.degree v = D.degree v + _ at hs
    rw [hbase, hloss] at hs
    omega
  have hvx : v ≠ x := by
    intro h
    exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2
      (by simpa [x, threePointPairDefect, h] using hvabs)
  have hvy : v ≠ y := by
    intro h
    exact (absolutePairCommonNeighbor_spec K ha hc hac).2.2
      (by simpa [y, threePointOuterPairDefectAC, h] using hvabs)
  change J.degree v = Nat.card K
  rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints H x y v hvx hvy]
  exact hD

/-- Any successful second switch must avoid cross-loss at every surviving
absolute point other than its freely chosen second endpoint. -/
theorem secondPairPoleSwitch_avoids_surviving_absolute
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (w v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hvabs : Projectivization.orthogonal v.1 v.1) (hvw : v ≠ w)
    [DecidableRel (crossEdgeSwitch (threePointCore K)
      (threePointPairDefect K ha hb hc hab)
      (threePointOuterPairDefectAC K ha hb hc hac)).Adj]
    [DecidableRel (deleteCrossEdges (threePointCore K)
      ((threePointCore K).neighborFinset (threePointPairDefect K ha hb hc hab))
      ((threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac))).Adj]
    [DecidableRel (crossEdgeSwitch
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      (threePointOuterPairDefectBC K ha hb hc hbc) w).Adj]
    [DecidableRel (deleteCrossEdges
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w)).Adj]
    (hfinal : ∀ u, Nat.card K ≤
      (crossEdgeSwitch
        (crossEdgeSwitch (threePointCore K)
          (threePointPairDefect K ha hb hc hab)
          (threePointOuterPairDefectAC K ha hb hc hac))
        (threePointOuterPairDefectBC K ha hb hc hbc) w).degree u) :
    crossEdgeLoss
      (crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc))
      ((crossEdgeSwitch (threePointCore K)
        (threePointPairDefect K ha hb hc hab)
        (threePointOuterPairDefectAC K ha hb hc hac)).neighborFinset w) v = 0 := by
  let J := crossEdgeSwitch (threePointCore K)
    (threePointPairDefect K ha hb hc hab)
    (threePointOuterPairDefectAC K ha hb hc hac)
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hvz : v ≠ z := by
    intro h
    exact (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
      (by simpa [z, threePointOuterPairDefectBC, h] using hvabs)
  apply crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
    J z w v hfinal
  · exact firstPairPoleSwitch_degree_surviving_absolute K h2 ha hb hc
      hab hac hbc v hvabs
  · exact hvz
  · exact hvw

end Erdos85.Polarity
