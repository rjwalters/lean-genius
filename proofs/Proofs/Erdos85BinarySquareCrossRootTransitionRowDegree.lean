import Proofs.Erdos85BinarySquareCenterGridComplement

/-! # Literal row and column degrees of cross-root transition factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Degree of a left coordinate in a finite pair relation. -/
def pairFinsetFstDegree
    {A : Type*} [DecidableEq A] (S : Finset (A × A)) (u : A) : ℕ :=
  (S.filter fun p => p.1 = u).card

/-- Degree of a right coordinate in a finite pair relation. -/
def pairFinsetSndDegree
    {A : Type*} [DecidableEq A] (S : Finset (A × A)) (v : A) : ℕ :=
  (S.filter fun p => p.2 = v).card

theorem pairFinsetFstDegree_union_of_disjoint
    {A : Type*} [DecidableEq A] {S T : Finset (A × A)}
    (hST : Disjoint S T) (u : A) :
    pairFinsetFstDegree (S ∪ T) u =
      pairFinsetFstDegree S u + pairFinsetFstDegree T u := by
  rw [pairFinsetFstDegree, Finset.filter_union,
    Finset.card_union_of_disjoint
      (hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rfl

theorem pairFinsetSndDegree_union_of_disjoint
    {A : Type*} [DecidableEq A] {S T : Finset (A × A)}
    (hST : Disjoint S T) (v : A) :
    pairFinsetSndDegree (S ∪ T) v =
      pairFinsetSndDegree S v + pairFinsetSndDegree T v := by
  rw [pairFinsetSndDegree, Finset.filter_union,
    Finset.card_union_of_disjoint
      (hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rfl

/-- A normalized remote-target transition factor has literal left degree two
at every ambient center adjacent to the first root. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fstDegree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : V) (hxu : G.Adj x.1 u) :
    pairFinsetFstDegree
      (crossRootCenterPairFinset G hfree hde x y) u = 2 := by
  classical
  let c := (secondOrderDefectGraph G).connectedComponentMk u
  let us : c.supp := ⟨u, ConnectedComponent.connectedComponentMk_mem⟩
  have hinj := crossRootCenterPair_injective_of_secondOrderDefect_adj
    G hfree hde x y hxyD
  rw [pairFinsetFstDegree, crossRootCenterPairFinset, Finset.filter_image]
  rw [Finset.card_image_of_injective _ hinj]
  exact binarySquare_regular_sizeTwo_crossRootCenterPair_fst_fiber_card_eq_two
    G hfree hq hreg hcard hde he x y us hxu

/-- A normalized remote-target transition factor has literal right degree two
at every ambient center adjacent to the second root. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPairFinset_sndDegree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (v : V) (hyv : G.Adj y.1 v) :
    pairFinsetSndDegree
      (crossRootCenterPairFinset G hfree hde x y) v = 2 := by
  classical
  let c := (secondOrderDefectGraph G).connectedComponentMk v
  let vs : c.supp := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
  have hinj := crossRootCenterPair_injective_of_secondOrderDefect_adj
    G hfree hde x y hxyD
  rw [pairFinsetSndDegree, crossRootCenterPairFinset, Finset.filter_image]
  rw [Finset.card_image_of_injective _ hinj]
  exact binarySquare_regular_sizeTwo_crossRootCenterPair_snd_fiber_card_eq_two
    G hfree hq hreg hcard hde he x y vs hyv

/-- The full center grid has one left-row entry for each neighbor of the
second root. -/
theorem crossRootCenterGrid_fstDegree_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y u : V} (hxu : G.Adj x u) :
    pairFinsetFstDegree (crossRootCenterGrid G x y) u = G.degree y := by
  classical
  rw [pairFinsetFstDegree, crossRootCenterGrid]
  have hrow :
      (((G.neighborFinset x ×ˢ G.neighborFinset y).filter fun p =>
        p.1 = u)) = (G.neighborFinset y).image fun v => (u, v) := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product,
      G.mem_neighborFinset, Finset.mem_image]
    constructor
    · rintro ⟨⟨hxa, hyb⟩, rfl⟩
      exact ⟨b, hyb, rfl⟩
    · rintro ⟨v, hyv, huv⟩
      cases huv
      exact ⟨⟨hxu, hyv⟩, rfl⟩
  rw [hrow, Finset.card_image_of_injective]
  · exact G.card_neighborFinset_eq_degree y
  · intro a b h
    exact congrArg Prod.snd h

/-- At order sixty-four, the complement of the three remote target factors
has left degree exactly two at every center adjacent to the first root. -/
theorem orderSixtyFour_three_remoteTargets_complement_fstDegree_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : Fin 64) (hxu : G.Adj x.1 u) :
    pairFinsetFstDegree
      (crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y)) u = 2 := by
  classical
  let Se := crossRootCenterPairFinset G hfree hde x y
  let Sf := crossRootCenterPairFinset G hfree hdf x y
  let Sg := crossRootCenterPairFinset G hfree hdg x y
  let U := (Se ∪ Sf) ∪ Sg
  have hEF : Disjoint Se Sf :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdf hef x y hxyD
  have hEG : Disjoint Se Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdg heg x y hxyD
  have hFG : Disjoint Sf Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hdf hdg hfg x y hxyD
  have hUG : Disjoint (Se ∪ Sf) Sg :=
    Finset.disjoint_union_left.mpr ⟨hEG, hFG⟩
  have hSe : pairFinsetFstDegree Se u = 2 :=
    binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fstDegree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        hde (by simpa using he) x y hxyD u hxu
  have hSf : pairFinsetFstDegree Sf u = 2 :=
    binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fstDegree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        hdf (by simpa using hf) x y hxyD u hxu
  have hSg : pairFinsetFstDegree Sg u = 2 :=
    binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fstDegree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        hdg (by simpa using hg) x y hxyD u hxu
  have hUdegree : pairFinsetFstDegree U u = 6 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl,
      pairFinsetFstDegree_union_of_disjoint hUG,
      pairFinsetFstDegree_union_of_disjoint hEF, hSe, hSf, hSg]
  have hUsub : U ⊆ crossRootCenterGrid G x.1 y.1 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl,
      Finset.union_subset_iff, Finset.union_subset_iff]
    exact ⟨⟨crossRootCenterPairFinset_subset_centerGrid G hfree hde x y,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdf x y⟩,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdg x y⟩
  have hfilter :
      ((crossRootCenterGrid G x.1 y.1 \ U).filter fun p => p.1 = u) =
        (crossRootCenterGrid G x.1 y.1).filter (fun p => p.1 = u) \
          U.filter (fun p => p.1 = u) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpgrid, hpU⟩, hpu⟩
      exact ⟨⟨hpgrid, hpu⟩, fun hp => hpU hp.1⟩
    · rintro ⟨⟨hpgrid, hpu⟩, hpU⟩
      exact ⟨⟨hpgrid, fun hp => hpU ⟨hp, hpu⟩⟩, hpu⟩
  have hfilterSub :
      U.filter (fun p => p.1 = u) ⊆
        (crossRootCenterGrid G x.1 y.1).filter (fun p => p.1 = u) := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨hUsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  change pairFinsetFstDegree
    (crossRootCenterGrid G x.1 y.1 \ U) u = 2
  rw [pairFinsetFstDegree, hfilter,
    Finset.card_sdiff_of_subset
      hfilterSub,
    ← pairFinsetFstDegree, ← pairFinsetFstDegree,
    crossRootCenterGrid_fstDegree_eq_degree G hxu,
    hreg y.1, hUdegree]

/-- Each graph-native piece of the fourth factor has left degree at most two.
This is the first pointwise restriction on the internal split, strengthening
the previously known total-cardinality ledger. -/
theorem orderSixtyFour_sourceCommon_and_defect_fstDegree_le_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (hexhaust : ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
      k = d ∨ k = e ∨ k = f ∨ k = g)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : Fin 64) (hxu : G.Adj x.1 u) :
    pairFinsetFstDegree
        (crossRootSourceCommonCenterPairs G d x.1 y.1) u ≤ 2 ∧
      pairFinsetFstDegree
        (crossRootDefectCenterPairs G x.1 y.1) u ≤ 2 := by
  let K := crossRootCenterGrid G x.1 y.1 \ ((
      crossRootCenterPairFinset G hfree hde x y ∪
        crossRootCenterPairFinset G hfree hdf x y) ∪
      crossRootCenterPairFinset G hfree hdg x y)
  have hKdegree : pairFinsetFstDegree K u = 2 :=
    orderSixtyFour_three_remoteTargets_complement_fstDegree_two
      G hfree hreg hde hdf hdg hef heg hfg he hf hg x y hxyD u hxu
  have hKeq : K =
      crossRootSourceCommonCenterPairs G d x.1 y.1 ∪
        crossRootDefectCenterPairs G x.1 y.1 :=
    crossRootCenterGrid_complement_eq_sourceCommon_union_defect
      G hfree hde hdf hdg hexhaust x y hxyD
  have hSourceSub : crossRootSourceCommonCenterPairs G d x.1 y.1 ⊆ K := by
    rw [hKeq]
    exact Finset.subset_union_left
  have hDefectSub : crossRootDefectCenterPairs G x.1 y.1 ⊆ K := by
    rw [hKeq]
    exact Finset.subset_union_right
  constructor
  · rw [← hKdegree]
    apply Finset.card_mono
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨hSourceSub (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2⟩
  · rw [← hKdegree]
    apply Finset.card_mono
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨hDefectSub (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2⟩

end

end Erdos85
