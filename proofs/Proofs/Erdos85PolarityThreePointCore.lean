import Proofs.Erdos85PolarityTwoPointCore

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

noncomputable abbrev threePointCore {a b c : P K} :=
  deleteVertexSetGraph (graph K) {a,b,c}

noncomputable def threePointPairDefect {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c) (hab : a ≠ b) :
    {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
  ⟨absolutePairCommonNeighbor K ha hb hab, by
    intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using ha)
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using hb)
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using hc)⟩

theorem threePointPairDefect_degree {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (threePointCore K).degree (threePointPairDefect K (c := c) ha hb hc hab) =
      Nat.card K - 1 := by
  let x := threePointPairDefect K (c := c) ha hb hc hab
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) x
  have hxnon : ¬ Projectivization.orthogonal x.1 x.1 := by
    simpa [x, threePointPairDefect] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.2
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hxnon] at hs
  have hxc := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hb hab hc hca hcb
  have hinc : ((graph K).neighborFinset x.1 ∩
      ({a,b,c} : Finset (P K))).card = 2 := by
    have heq : (graph K).neighborFinset x.1 ∩ ({a,b,c} : Finset (P K)) = {a,b} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hxc (by simpa [x, threePointPairDefect] using hz)).elim
      · rintro (rfl | rfl)
        · exact ⟨by simpa [x, threePointPairDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).1.symm, Or.inl rfl⟩
        · exact ⟨by simpa [x, threePointPairDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm,
              Or.inr (Or.inl rfl)⟩
    rw [heq]
    simp [hab]
  change (threePointCore K).degree x + _ = Nat.card K + 1 at hs
  change (threePointCore K).degree x = Nat.card K - 1
  rw [hinc] at hs
  have hq := three_le_card_of_two_ne_zero K h2
  omega

/-- Every surviving absolute point in a three-absolute deletion core remains
target-tight, of degree exactly `q`. -/
theorem threePointCore_degree_surviving_absolute {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : Projectivization.orthogonal v.1 v.1) :
    (threePointCore K).degree v = Nat.card K := by
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) v
  rw [degree_eq_card_of_selfOrthogonal hv] at hs
  have hinc : ((graph K).neighborFinset v.1 ∩
      ({a,b,c} : Finset (P K))).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hvz, hz⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (not_selfOrthogonal_of_adj_selfOrthogonal
        (by simpa using hvz) hv) ha
    · exact (not_selfOrthogonal_of_adj_selfOrthogonal
        (by simpa using hvz) hv) hb
    · exact (not_selfOrthogonal_of_adj_selfOrthogonal
        (by simpa using hvz) hv) hc
  change (threePointCore K).degree v + _ = Nat.card K at hs
  rw [hinc, Nat.add_zero] at hs
  exact hs

/-- Exactly `q-2` absolute points survive deletion of three distinct absolute
points. -/
theorem card_absolutePoints_sdiff_three {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (absolutePoints K \ ({a,b,c} : Finset (P K))).card = Nat.card K - 2 := by
  have hsub : ({a,b,c} : Finset (P K)) ⊆ absolutePoints K := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (mem_absolutePoints K _).mpr ha
    · exact (mem_absolutePoints K _).mpr hb
    · exact (mem_absolutePoints K _).mpr hc
  rw [Finset.card_sdiff_of_subset hsub, card_absolutePoints_eq_card_add_one K]
  have hthree : ({a,b,c} : Finset (P K)).card = 3 := by
    simp [hab, hac, hbc]
  rw [hthree]
  omega

noncomputable def remainingAbsoluteEmbedding {a b c : P K} :
    {v // v ∈ absolutePoints K \ ({a,b,c} : Finset (P K))} ↪
      {v // v ∉ ({a,b,c} : Finset (P K))} where
  toFun v := ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {v : P K //
      v ∉ ({a,b,c} : Finset (P K))} => z.val) h

/-- The three-point core contains a canonical set of `q-2` target-tight
vertices, namely its surviving absolute points. -/
theorem exists_tight_absolute_set_threePointCore {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ T : Finset {v : P K // v ∉ ({a,b,c} : Finset (P K))},
      T.card = Nat.card K - 2 ∧
      ∀ v ∈ T, (threePointCore K).degree v = Nat.card K := by
  classical
  let e := remainingAbsoluteEmbedding K (a := a) (b := b) (c := c)
  let T : Finset {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
    Finset.univ.map e
  refine ⟨T, ?_, ?_⟩
  · dsimp only [T]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe]
    exact card_absolutePoints_sdiff_three K ha hb hc hab hac hbc
  · intro v hvT
    dsimp only [T] at hvT
    rw [Finset.mem_map] at hvT
    obtain ⟨r, _, rfl⟩ := hvT
    apply threePointCore_degree_surviving_absolute K ha hb hc
    exact (mem_absolutePoints K r.1).mp (Finset.mem_sdiff.mp r.2).1

/-- A nonabsolute point and an absolute point which are not orthogonal have
exactly one graph-theoretic common neighbor. -/
theorem card_commonNeighbors_eq_one_of_nonabsolute_absolute_notOrthogonal
    {x c : P K} (hx : ¬ Projectivization.orthogonal x x)
    (hc : Projectivization.orthogonal c c)
    (hxc : ¬ Projectivization.orthogonal x c) :
    ((graph K).neighborFinset x ∩ (graph K).neighborFinset c).card = 1 := by
  classical
  have hne : x ≠ c := by
    intro h
    exact hx (by simpa [h] using hc)
  obtain ⟨p, hp, _⟩ := Configuration.HasPoints.existsUnique_point
    (P K) (P K) x c hne
  have hpx : Projectivization.orthogonal x p :=
    Projectivization.orthogonal_comm.mpr
      ((Configuration.ofField.mem_iff p x).mp hp.1)
  have hpc : Projectivization.orthogonal c p :=
    Projectivization.orthogonal_comm.mpr
      ((Configuration.ofField.mem_iff p c).mp hp.2)
  have hpnx : p ≠ x := by
    intro h
    exact hx (by simpa [h] using hpx)
  have hpnc : p ≠ c := by
    intro h
    exact hxc (by simpa [h] using hpx)
  apply le_antisymm (commonNeighbors_le_one x c hne)
  rw [Finset.one_le_card]
  refine ⟨p, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simpa only [SimpleGraph.mem_neighborFinset] using
      ((graph_adj_iff x p).mpr ⟨hpnx.symm, hpx⟩)
  · simpa only [SimpleGraph.mem_neighborFinset] using
      ((graph_adj_iff c p).mpr ⟨hpnc.symm, hpc⟩)

/-- Two distinct nonabsolute points have exactly one graph-theoretic common
neighbor. -/
theorem card_commonNeighbors_eq_one_of_nonabsolute
    {x y : P K} (hne : x ≠ y)
    (hx : ¬ Projectivization.orthogonal x x)
    (hy : ¬ Projectivization.orthogonal y y) :
    ((graph K).neighborFinset x ∩ (graph K).neighborFinset y).card = 1 := by
  classical
  obtain ⟨p, hp, _⟩ := Configuration.HasPoints.existsUnique_point
    (P K) (P K) x y hne
  have hpx : Projectivization.orthogonal x p :=
    Projectivization.orthogonal_comm.mpr
      ((Configuration.ofField.mem_iff p x).mp hp.1)
  have hpy : Projectivization.orthogonal y p :=
    Projectivization.orthogonal_comm.mpr
      ((Configuration.ofField.mem_iff p y).mp hp.2)
  have hpnx : p ≠ x := by intro h; exact hx (by simpa [h] using hpx)
  have hpny : p ≠ y := by intro h; exact hy (by simpa [h] using hpy)
  apply le_antisymm (commonNeighbors_le_one x y hne)
  rw [Finset.one_le_card]
  exact ⟨p, Finset.mem_inter.mpr
    ⟨by simpa only [SimpleGraph.mem_neighborFinset] using
      ((graph_adj_iff x p).mpr ⟨hpnx.symm, hpx⟩),
     by simpa only [SimpleGraph.mem_neighborFinset] using
      ((graph_adj_iff y p).mpr ⟨hpny.symm, hpy⟩)⟩⟩

/-- A pair pole and a third distinct absolute point have exactly one common
neighbor, despite being nonadjacent themselves. -/
theorem card_pairPole_commonNeighbors_third_absolute_eq_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ((graph K).neighborFinset (absolutePairCommonNeighbor K ha hb hab) ∩
      (graph K).neighborFinset c).card = 1 := by
  apply card_commonNeighbors_eq_one_of_nonabsolute_absolute_notOrthogonal K
    (absolutePairCommonNeighbor_spec K ha hb hab).2.2 hc
  intro hortho
  have hne : absolutePairCommonNeighbor K ha hb hab ≠ c := by
    intro h
    exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2
      (by simpa [h] using hc)
  exact not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hb hab hc hca hcb
      ((graph_adj_iff _ _).mpr ⟨hne, hortho⟩)

/-- Pair poles of two secants sharing exactly one absolute endpoint are
distinct. -/
theorem absolutePairCommonNeighbor_ne_shared
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    absolutePairCommonNeighbor K ha hb hab ≠
      absolutePairCommonNeighbor K ha hc hac := by
  intro heq
  have hadj := (absolutePairCommonNeighbor_spec K ha hb hab).2.1
  have hnot := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hc hac hb (Ne.symm hab) hbc
  exact hnot (by simpa [heq] using hadj.symm)

/-- The only graph common neighbor of two pair poles sharing the absolute
endpoint `a` is `a` itself. -/
theorem pairPole_neighborFinset_inter_eq_singleton_shared
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (graph K).neighborFinset (absolutePairCommonNeighbor K ha hb hab) ∩
      (graph K).neighborFinset (absolutePairCommonNeighbor K ha hc hac) = {a} := by
  let x := absolutePairCommonNeighbor K ha hb hab
  let y := absolutePairCommonNeighbor K ha hc hac
  have hxy := absolutePairCommonNeighbor_ne_shared K h2 ha hb hc hab hac hbc
  have hone := card_commonNeighbors_eq_one_of_nonabsolute K hxy
    (absolutePairCommonNeighbor_spec K ha hb hab).2.2
    (absolutePairCommonNeighbor_spec K ha hc hac).2.2
  rw [Finset.card_eq_one] at hone
  obtain ⟨z, hz⟩ := hone
  have hamem : a ∈ (graph K).neighborFinset x ∩ (graph K).neighborFinset y := by
    rw [Finset.mem_inter]
    simp only [SimpleGraph.mem_neighborFinset]
    exact ⟨by simpa [x] using (absolutePairCommonNeighbor_spec K ha hb hab).1.symm,
      by simpa [y] using (absolutePairCommonNeighbor_spec K ha hc hac).1.symm⟩
  have hazmem : a ∈ ({z} : Finset (P K)) := by rw [← hz]; exact hamem
  have haz : a = z := by simpa using hazmem
  simpa [x, y, haz] using hz

noncomputable def pairPoleCleanCenterNeighbors {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) : Finset (P K) :=
  ((graph K).neighborFinset (absolutePairCommonNeighbor K ha hb hab) \ {a,b,c}) \
    (graph K).neighborFinset c

/-- The center pair pole has exactly `q-2` surviving neighbors which are not
adjacent to the third deleted absolute point. -/
theorem pairPoleCleanCenterNeighbors_card {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (pairPoleCleanCenterNeighbors K ha hb hab (c := c)).card = Nat.card K - 2 := by
  classical
  let x := absolutePairCommonNeighbor K ha hb hab
  let A := (graph K).neighborFinset x \ ({a,b,c} : Finset (P K))
  have hxnon := (absolutePairCommonNeighbor_spec K ha hb hab).2.2
  have hxdeg : ((graph K).neighborFinset x).card = Nat.card K + 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      degree_eq_card_add_one_of_not_selfOrthogonal hxnon]
  have hxc := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hb hab hc hca hcb
  have hdel : (graph K).neighborFinset x ∩ ({a,b,c} : Finset (P K)) = {a,b} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hxc (by simpa [x] using hz)).elim
    · rintro (rfl | rfl)
      · exact ⟨by simpa [x] using
          (absolutePairCommonNeighbor_spec K ha hb hab).1.symm, Or.inl rfl⟩
      · exact ⟨by simpa [x] using
          (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm,
            Or.inr (Or.inl rfl)⟩
  have hAcard : A.card = Nat.card K - 1 := by
    dsimp only [A]
    rw [Finset.card_sdiff, Finset.inter_comm, hdel, hxdeg]
    simp [hab]
  have hinter : (A ∩ (graph K).neighborFinset c).card = 1 := by
    have heq : A ∩ (graph K).neighborFinset c =
        (graph K).neighborFinset x ∩ (graph K).neighborFinset c := by
      ext z
      simp only [A, Finset.mem_inter, Finset.mem_sdiff,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨⟨hzx, _⟩, hzc⟩
        exact ⟨hzx, hzc⟩
      · rintro ⟨hzx, hzc⟩
        refine ⟨⟨hzx, ?_⟩, hzc⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl | rfl)
        · exact (not_selfOrthogonal_of_adj_selfOrthogonal
            (by simpa using hzc) hc) ha
        · exact (not_selfOrthogonal_of_adj_selfOrthogonal
            (by simpa using hzc) hc) hb
        · exact (hxc (by simpa [x] using hzx)).elim
    rw [heq]
    exact card_pairPole_commonNeighbors_third_absolute_eq_one K
      h2 ha hb hc hab hca hcb
  rw [pairPoleCleanCenterNeighbors, Finset.card_sdiff]
  change A.card - ((graph K).neighborFinset c ∩ A).card = _
  rw [Finset.inter_comm, hinter, hAcard]
  have hq := three_le_card_of_two_ne_zero K h2
  omega

/-- Every member of the clean center-neighbor family has full degree `q+1`
in the three-point core. -/
theorem threePointCore_degree_of_mem_pairPoleCleanCenterNeighbors
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c)) :
    (threePointCore K).degree v = Nat.card K + 1 := by
  classical
  let x := absolutePairCommonNeighbor K ha hb hab
  have hvm := Finset.mem_sdiff.mp hv
  have hvfirst := Finset.mem_sdiff.mp hvm.1
  have hvx : (graph K).Adj x v.1 := by simpa [x] using hvfirst.1
  have hvD : v.1 ∉ ({a,b,c} : Finset (P K)) := hvfirst.2
  have hvc : ¬ (graph K).Adj c v.1 := by
    simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
  have hvabs : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro habs
    have hva : v.1 ≠ a := by
      intro h; exact hvD (by simp [h])
    have hvb : v.1 ≠ b := by
      intro h; exact hvD (by simp [h])
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab habs hva hvb) hvx
  have hva : ¬ (graph K).Adj a v.1 := by
    intro hav
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := x) (w := a)
      (by simpa [x] using (absolutePairCommonNeighbor_spec K ha hb hab).1.symm) ha
    have hm : v.1 ∈ (graph K).neighborFinset x ∩ (graph K).neighborFinset a := by
      rw [Finset.mem_inter]
      simpa only [SimpleGraph.mem_neighborFinset] using ⟨hvx, hav⟩
    rw [hempty] at hm
    simp at hm
  have hvb : ¬ (graph K).Adj b v.1 := by
    intro hbv
    have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
      (K := K) (z := x) (w := b)
      (by simpa [x] using (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm) hb
    have hm : v.1 ∈ (graph K).neighborFinset x ∩ (graph K).neighborFinset b := by
      rw [Finset.mem_inter]
      simpa only [SimpleGraph.mem_neighborFinset] using ⟨hvx, hbv⟩
    rw [hempty] at hm
    simp at hm
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) v
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hvabs] at hs
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
  rw [hzero, Nat.add_zero] at hs
  exact hs


noncomputable def threePointOuterPairDefectAC {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c) (hac : a ≠ c) :
    {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
  ⟨absolutePairCommonNeighbor K ha hc hac, by
    intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (absolutePairCommonNeighbor_spec K ha hc hac).2.2 (by simpa [hm] using ha)
    · exact (absolutePairCommonNeighbor_spec K ha hc hac).2.2 (by simpa [hm] using hb)
    · exact (absolutePairCommonNeighbor_spec K ha hc hac).2.2 (by simpa [hm] using hc)⟩

/-- Every clean center neighbor has exactly one common neighbor in the
three-point core with the outer `{a,c}` pair pole. -/
theorem cleanCenter_commonNeighbors_outerAC_card_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c)) :
    ((threePointCore K).neighborFinset v ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac)).card = 1 := by
  classical
  let y := threePointOuterPairDefectAC K ha hb hc hac
  have hvy : v.1 ≠ y.1 := by
    intro heq
    have hvm := Finset.mem_sdiff.mp hv
    have hvnc : ¬ (graph K).Adj c v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    exact hvnc (by simpa [y, threePointOuterPairDefectAC, heq] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.1)
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro hvabs
    have hvm := Finset.mem_sdiff.mp hv
    have hvfirst := Finset.mem_sdiff.mp hvm.1
    have hvx : (graph K).Adj
        (absolutePairCommonNeighbor K ha hb hab) v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvfirst.1
    have hva : v.1 ≠ a := by intro h; exact hvfirst.2 (by simp [h])
    have hvb : v.1 ≠ b := by intro h; exact hvfirst.2 (by simp [h])
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab hvabs hva hvb) hvx
  have hynon : ¬ Projectivization.orthogonal y.1 y.1 := by
    simpa [y, threePointOuterPairDefectAC] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.2
  have hbase := card_commonNeighbors_eq_one_of_nonabsolute K hvy hvnon hynon
  rw [Finset.card_eq_one] at hbase
  obtain ⟨p, hp⟩ := hbase
  have hpBoth : p ∈ (graph K).neighborFinset v.1 ∩
      (graph K).neighborFinset y.1 := by rw [hp]; simp
  have hpv : (graph K).Adj v.1 p := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hpBoth).1
  have hpy : (graph K).Adj y.1 p := by
    have hm : p ∈ (graph K).neighborFinset y.1 := by
      exact Finset.mem_inter.mp hpBoth |>.2
    simpa only [SimpleGraph.mem_neighborFinset] using hm
  have hpout : p ∉ ({a,b,c} : Finset (P K)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · have hvm := Finset.mem_sdiff.mp hv
      have hvx := (Finset.mem_sdiff.mp hvm.1).1
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := absolutePairCommonNeighbor K ha hb hab) (w := _)
        (absolutePairCommonNeighbor_spec K ha hb hab).1.symm ha
      have hm : v.1 ∈ (graph K).neighborFinset
          (absolutePairCommonNeighbor K ha hb hab) ∩
          (graph K).neighborFinset p := by
        rw [Finset.mem_inter]
        exact ⟨hvx, by simpa only [SimpleGraph.mem_neighborFinset] using hpv.symm⟩
      rw [hempty] at hm
      simp at hm
    · exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
        ha hc hac hb (Ne.symm hab) hbc)
          (by simpa [y, threePointOuterPairDefectAC] using hpy)
    · have hvm := Finset.mem_sdiff.mp hv
      exact hvm.2 (by simpa using hpv.symm)
  let ps : {z : P K // z ∉ ({a,b,c} : Finset (P K))} := ⟨p, hpout⟩
  apply le_antisymm
  · rw [Finset.card_le_one_iff]
    intro r s hr hs
    apply Subtype.ext
    have rb : r.1 ∈ (graph K).neighborFinset v.1 ∩
        (graph K).neighborFinset y.1 := by
      rw [Finset.mem_inter]
      constructor
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset v r |>.mp
            (Finset.mem_inter.mp hr).1)
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset y r |>.mp
            (Finset.mem_inter.mp hr).2)
    have sb : s.1 ∈ (graph K).neighborFinset v.1 ∩
        (graph K).neighborFinset y.1 := by
      rw [Finset.mem_inter]
      constructor
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset v s |>.mp
            (Finset.mem_inter.mp hs).1)
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset y s |>.mp
            (Finset.mem_inter.mp hs).2)
    rw [hp] at rb sb
    simpa using (Finset.mem_singleton.mp rb).trans
      (Finset.mem_singleton.mp sb).symm
  · rw [Finset.one_le_card]
    refine ⟨ps, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mpr hpv
    · rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mpr hpy


noncomputable def threePointOuterPairDefectBC {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c) (hbc : b ≠ c) :
    {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
  ⟨absolutePairCommonNeighbor K hb hc hbc, by
    intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (absolutePairCommonNeighbor_spec K hb hc hbc).2.2 (by simpa [hm] using ha)
    · exact (absolutePairCommonNeighbor_spec K hb hc hbc).2.2 (by simpa [hm] using hb)
    · exact (absolutePairCommonNeighbor_spec K hb hc hbc).2.2 (by simpa [hm] using hc)⟩

theorem cleanCenter_commonNeighbors_outerBC_card_one
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c)) :
    ((threePointCore K).neighborFinset v ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectBC K ha hb hc hbc)).card = 1 := by
  classical
  let y := threePointOuterPairDefectBC K ha hb hc hbc
  have hvy : v.1 ≠ y.1 := by
    intro heq
    have hvm := Finset.mem_sdiff.mp hv
    have hvnc : ¬ (graph K).Adj c v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvm.2
    exact hvnc (by simpa [y, threePointOuterPairDefectBC, heq] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.1)
  have hvnon : ¬ Projectivization.orthogonal v.1 v.1 := by
    intro hvabs
    have hvm := Finset.mem_sdiff.mp hv
    have hvfirst := Finset.mem_sdiff.mp hvm.1
    have hvx : (graph K).Adj
        (absolutePairCommonNeighbor K ha hb hab) v.1 := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvfirst.1
    have hva : v.1 ≠ a := by intro h; exact hvfirst.2 (by simp [h])
    have hvb : v.1 ≠ b := by intro h; exact hvfirst.2 (by simp [h])
    exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      ha hb hab hvabs hva hvb) hvx
  have hynon : ¬ Projectivization.orthogonal y.1 y.1 := by
    simpa [y, threePointOuterPairDefectBC] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
  have hbase := card_commonNeighbors_eq_one_of_nonabsolute K hvy hvnon hynon
  rw [Finset.card_eq_one] at hbase
  obtain ⟨p, hp⟩ := hbase
  have hpBoth : p ∈ (graph K).neighborFinset v.1 ∩
      (graph K).neighborFinset y.1 := by rw [hp]; simp
  have hpv : (graph K).Adj v.1 p := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hpBoth).1
  have hpy : (graph K).Adj y.1 p := by
    have hm : p ∈ (graph K).neighborFinset y.1 := by
      exact Finset.mem_inter.mp hpBoth |>.2
    simpa only [SimpleGraph.mem_neighborFinset] using hm
  have hpout : p ∉ ({a,b,c} : Finset (P K)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact (not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
        hb hc hbc ha hab hac)
          (by simpa [y, threePointOuterPairDefectBC] using hpy)
    · have hvm := Finset.mem_sdiff.mp hv
      have hvx := (Finset.mem_sdiff.mp hvm.1).1
      have hempty := neighborFinset_inter_eq_empty_of_adj_absolute
        (K := K) (z := absolutePairCommonNeighbor K ha hb hab) (w := _)
        (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm hb
      have hm : v.1 ∈ (graph K).neighborFinset
          (absolutePairCommonNeighbor K ha hb hab) ∩
          (graph K).neighborFinset p := by
        rw [Finset.mem_inter]
        exact ⟨hvx, by simpa only [SimpleGraph.mem_neighborFinset] using hpv.symm⟩
      rw [hempty] at hm
      simp at hm
    · have hvm := Finset.mem_sdiff.mp hv
      exact hvm.2 (by simpa using hpv.symm)
  let ps : {z : P K // z ∉ ({a,b,c} : Finset (P K))} := ⟨p, hpout⟩
  apply le_antisymm
  · rw [Finset.card_le_one_iff]
    intro r s hr hs
    apply Subtype.ext
    have rb : r.1 ∈ (graph K).neighborFinset v.1 ∩
        (graph K).neighborFinset y.1 := by
      rw [Finset.mem_inter]
      constructor
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset v r |>.mp
            (Finset.mem_inter.mp hr).1)
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset y r |>.mp
            (Finset.mem_inter.mp hr).2)
    have sb : s.1 ∈ (graph K).neighborFinset v.1 ∩
        (graph K).neighborFinset y.1 := by
      rw [Finset.mem_inter]
      constructor
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset v s |>.mp
            (Finset.mem_inter.mp hs).1)
      · rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.induce_adj.mp
          ((threePointCore K).mem_neighborFinset y s |>.mp
            (Finset.mem_inter.mp hs).2)
    rw [hp] at rb sb
    simpa using (Finset.mem_singleton.mp rb).trans
      (Finset.mem_singleton.mp sb).symm
  · rw [Finset.one_le_card]
    refine ⟨ps, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mpr hpv
    · rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mpr hpy

/-- The two outer pole neighborhoods are disjoint after their shared absolute
common neighbor `c` is deleted. -/
theorem outerPairDefects_neighborFinset_inter_eq_empty
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac) ∩
      (threePointCore K).neighborFinset
        (threePointOuterPairDefectBC K ha hb hc hbc) = ∅ := by
  classical
  let y := threePointOuterPairDefectAC K ha hb hc hac
  let z := threePointOuterPairDefectBC K ha hb hc hbc
  have hyz : y.1 ≠ z.1 := by
    intro heq
    have hya := (absolutePairCommonNeighbor_spec K ha hc hac).1
    have hnot := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
      hb hc hbc ha hab hac
    have hyadj : (graph K).Adj y.1 a := by
      simpa [y, threePointOuterPairDefectAC] using hya.symm
    have hzadj : (graph K).Adj z.1 a := by simpa [heq] using hyadj
    exact hnot (by simpa [z, threePointOuterPairDefectBC] using hzadj)
  have hynon : ¬ Projectivization.orthogonal y.1 y.1 := by
    simpa [y, threePointOuterPairDefectAC] using
      (absolutePairCommonNeighbor_spec K ha hc hac).2.2
  have hznon : ¬ Projectivization.orthogonal z.1 z.1 := by
    simpa [z, threePointOuterPairDefectBC] using
      (absolutePairCommonNeighbor_spec K hb hc hbc).2.2
  have hone := card_commonNeighbors_eq_one_of_nonabsolute K hyz hynon hznon
  rw [Finset.card_eq_one] at hone
  obtain ⟨p, hp⟩ := hone
  have hcmem : c ∈ (graph K).neighborFinset y.1 ∩
      (graph K).neighborFinset z.1 := by
    rw [Finset.mem_inter]
    simp only [SimpleGraph.mem_neighborFinset]
    exact ⟨by simpa [y, threePointOuterPairDefectAC] using
        (absolutePairCommonNeighbor_spec K ha hc hac).2.1.symm,
      by simpa [z, threePointOuterPairDefectBC] using
        (absolutePairCommonNeighbor_spec K hb hc hbc).2.1.symm⟩
  have hcp : c = p := by
    have : c ∈ ({p} : Finset (P K)) := by rw [← hp]; exact hcmem
    simpa using this
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have rb : r.1 ∈ (graph K).neighborFinset y.1 ∩
      (graph K).neighborFinset z.1 := by
    rw [Finset.mem_inter]
    exact ⟨by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp
        ((threePointCore K).mem_neighborFinset y r |>.mp
          (Finset.mem_inter.mp hr).1), by
      rw [SimpleGraph.mem_neighborFinset]
      exact SimpleGraph.induce_adj.mp
        ((threePointCore K).mem_neighborFinset z r |>.mp
          (Finset.mem_inter.mp hr).2)⟩
  rw [hp] at rb
  have hrc : r.1 = c := (Finset.mem_singleton.mp rb).trans hcp.symm
  exact r.2 (by simp [hrc])

/-- Every clean center neighbor supports two distinct incident cross edges,
one toward each outer pole neighborhood. -/
theorem exists_two_distinct_outer_cross_edges_of_cleanCenter
    {a b c : P K} (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : {v : P K // v ∉ ({a,b,c} : Finset (P K))})
    (hv : v.1 ∈ pairPoleCleanCenterNeighbors K ha hb hab (c := c)) :
    ∃ r s,
      r ≠ s ∧
      (threePointCore K).Adj v r ∧
      r ∈ (threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac) ∧
      (threePointCore K).Adj v s ∧
      s ∈ (threePointCore K).neighborFinset
        (threePointOuterPairDefectBC K ha hb hc hbc) := by
  classical
  have hAC := cleanCenter_commonNeighbors_outerAC_card_one K
    h2 ha hb hc hab hac hbc v hv
  have hBC := cleanCenter_commonNeighbors_outerBC_card_one K
    h2 ha hb hc hab hac hbc v hv
  rw [Finset.card_eq_one] at hAC hBC
  obtain ⟨r, hr⟩ := hAC
  obtain ⟨s, hs⟩ := hBC
  refine ⟨r, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro hrs
    subst s
    have hm : r ∈ (threePointCore K).neighborFinset
        (threePointOuterPairDefectAC K ha hb hc hac) ∩
        (threePointCore K).neighborFinset
          (threePointOuterPairDefectBC K ha hb hc hbc) := by
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_inter.mp (by rw [hr]; simp)).2,
        (Finset.mem_inter.mp (by rw [hs]; simp)).2⟩
    rw [outerPairDefects_neighborFinset_inter_eq_empty K
      h2 ha hb hc hab hac hbc] at hm
    simp at hm
  · exact ((threePointCore K).mem_neighborFinset v r).mp
      (Finset.mem_inter.mp (by rw [hr]; simp)).1
  · exact (Finset.mem_inter.mp (by rw [hr]; simp)).2
  · exact ((threePointCore K).mem_neighborFinset v s).mp
      (Finset.mem_inter.mp (by rw [hs]; simp)).1
  · exact (Finset.mem_inter.mp (by rw [hs]; simp)).2

end Erdos85.Polarity
