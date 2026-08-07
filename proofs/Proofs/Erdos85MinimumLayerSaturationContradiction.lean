import Proofs.Erdos85MinimumLayerExtension

/-!
# Latin resolution in the saturated minimum-layer branch

In the saturated branch the exterior rows form matching blocks over the
reflexive complement of the child graph.  For a child pair having one common
neighbor, the common-nonneighbor rows and any one exterior row have the same
cardinality.  Composing matching blocks through those rows gives a bijection:
`C₄`-freeness supplies injectivity and the exact-boundary count supplies
surjectivity.  This is the first genuine Latin-square resolution law.
-/

open scoped BigOperators

namespace Erdos85

section

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Vertices nonadjacent (allowing equality) to both endpoints. -/
def commonNonneighborFinset (H : SimpleGraph W) [DecidableRel H.Adj]
    (a b : W) : Finset W :=
  Finset.univ \ (H.neighborFinset a ∪ H.neighborFinset b)

@[simp] theorem mem_commonNonneighborFinset_iff
    (H : SimpleGraph W) [DecidableRel H.Adj] (a b c : W) :
    c ∈ commonNonneighborFinset H a b ↔ ¬H.Adj a c ∧ ¬H.Adj b c := by
  simp [commonNonneighborFinset, H.mem_neighborFinset]

theorem card_commonNonneighborFinset
    (H : SimpleGraph W) [DecidableRel H.Adj]
    {s q : ℕ} (hreg : ∀ x, H.degree x = s)
    (a b : W)
    (hcommon : (H.neighborFinset a ∩ H.neighborFinset b).card = q) :
    (commonNonneighborFinset H a b).card = Fintype.card W - (2 * s - q) := by
  have hunion :
      (H.neighborFinset a ∪ H.neighborFinset b).card = 2 * s - q := by
    have h := Finset.card_union_add_card_inter
      (H.neighborFinset a) (H.neighborFinset b)
    rw [H.card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree,
      hreg a, hreg b, hcommon] at h
    omega
  rw [commonNonneighborFinset,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    hunion]

/-- An injection between finite types whose codomain has one extra point has
a unique omitted value. -/
theorem existsUnique_not_mem_range_of_card_add_one
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (hcard : Fintype.card α + 1 = Fintype.card β) :
    ∃! y : β, ∀ x : α, f x ≠ y := by
  classical
  let R : Finset β := Finset.univ.image f
  have hcardR : R.card = Fintype.card α := by
    simpa [R] using Finset.card_image_of_injective Finset.univ hf
  have hcardComp : (Finset.univ \ R).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ,
      hcardR]
    omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcardComp
  have hyComp : y ∈ Finset.univ \ R := by
    rw [hy]
    exact Finset.mem_singleton_self y
  refine ⟨y, ?_, ?_⟩
  · intro x hxy
    have hyR : y ∈ R := by
      subst y
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp hyComp).2 hyR
  · intro y' hy'
    have hy'notR : y' ∉ R := by
      intro hy'R
      obtain ⟨x, _hx, hxy'⟩ := Finset.mem_image.mp hy'R
      exact hy' x hxy'
    have hy'Comp : y' ∈ Finset.univ \ R :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy'notR⟩
    rw [hy] at hy'Comp
    exact Finset.mem_singleton.mp hy'Comp

end

section

/-- For arbitrary distinct child owners, matching composition through their
common-nonneighbor rows is injective into the target exterior row.  The
one-common and zero-common cases differ only in whether this injection is
surjective or misses one point. -/
theorem minimumLayer_saturated_twoStep_injection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b) :
    let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    let C := commonNonneighborFinset H a b
    ∀ z ∈ E a, ∃ f : ↥C → ↥(E b),
      Function.Injective f ∧
        ∀ c : ↥C, ∃ x : V,
          x ∈ E c.1 ∧ G.Adj z x ∧ G.Adj x (f c).1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let C := commonNonneighborFinset H a b
  intro z hza
  have hfirst : ∀ c : ↥C, ∃! r : V, r ∈ E c.1 ∧ G.Adj z r := by
    intro c
    apply minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        c.1 a hza
    intro hca
    exact ((mem_commonNonneighborFinset_iff H a b c.1).mp c.2).1 hca.symm
  let p : ↥C → V := fun c => Classical.choose (hfirst c)
  have hp : ∀ c : ↥C, p c ∈ E c.1 ∧ G.Adj z (p c) := fun c =>
    Classical.choose_spec (hfirst c) |>.1
  have hsecond : ∀ c : ↥C, ∃! r : V, r ∈ E b ∧ G.Adj (p c) r := by
    intro c
    apply minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        b c.1 (hp c).1
    exact (mem_commonNonneighborFinset_iff H a b c.1).mp c.2 |>.2
  let f : ↥C → V := fun c => Classical.choose (hsecond c)
  have hf : ∀ c : ↥C, f c ∈ E b ∧ G.Adj (p c) (f c) := fun c =>
    Classical.choose_spec (hsecond c) |>.1
  let fE : ↥C → ↥(E b) := fun c => ⟨f c, (hf c).1⟩
  have hfEinj : Function.Injective fE := by
    intro c c' hcc'
    by_contra hnecc'
    have hfc : f c = f c' :=
      congrArg (fun x : ↥(E b) => x.1) hcc'
    exact minimumLayer_externalBlock_no_closed_fourStep
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        a c.1 b c'.1 habne (by
          intro h
          apply hnecc'
          exact Subtype.ext h)
        hza (hp c).1 (hf c).1 (hp c').1
        (hp c).2 (hf c).2 (by simpa [hfc] using (hf c').2.symm)
        (hp c').2.symm
  refine ⟨fE, hfEinj, ?_⟩
  intro c
  exact ⟨p c, (hp c).1, (hp c).2, (hf c).2⟩

/-- **Latin resolution law.**  Fix `z` in the exterior row over `a`.  If
`a,b` are nonadjacent child vertices with one common child neighbor, then
two-step matching paths from `z`, through rows nonadjacent to both `a,b`,
resolve the row over `b` bijectively. -/
theorem minimumLayer_saturated_twoStep_bijection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b)
    (hcommon :
      ((minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset a ∩
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset b).card = 1) :
    let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    let C := commonNonneighborFinset H a b
    ∀ z ∈ E a, ∃ f : ↥C → ↥(E b),
      Function.Bijective f ∧
        ∀ c : ↥C, ∃ x : V,
          x ∈ E c.1 ∧ G.Adj z x ∧ G.Adj x (f c).1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let C := commonNonneighborFinset H a b
  have hsatOrder : s * (s - 1) + 3 = d + s - 1 := by
    rw [hsat]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 1 := ⟨s - 1, by omega⟩
    norm_num
    ring
  have hcardC : C.card = d - s := by
    rw [card_commonNonneighborFinset H hregChild a b hcommon, hcardChild,
      hsatOrder]
    omega
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
    intro x
    exact card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild x
  intro z hza
  have hfirst : ∀ c : ↥C, ∃! r : V, r ∈ E c.1 ∧ G.Adj z r := by
    intro c
    apply minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        c.1 a hza
    intro hca
    exact ((mem_commonNonneighborFinset_iff H a b c.1).mp c.2).1 hca.symm
  let p : ↥C → V := fun c => Classical.choose (hfirst c)
  have hp : ∀ c : ↥C, p c ∈ E c.1 ∧ G.Adj z (p c) := fun c =>
    Classical.choose_spec (hfirst c) |>.1
  have hsecond : ∀ c : ↥C, ∃! r : V, r ∈ E b ∧ G.Adj (p c) r := by
    intro c
    apply minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        b c.1 (hp c).1
    exact (mem_commonNonneighborFinset_iff H a b c.1).mp c.2 |>.2
  let f : ↥C → V := fun c => Classical.choose (hsecond c)
  have hf : ∀ c : ↥C, f c ∈ E b ∧ G.Adj (p c) (f c) := fun c =>
    Classical.choose_spec (hsecond c) |>.1
  let fE : ↥C → ↥(E b) := fun c => ⟨f c, (hf c).1⟩
  have hfEinj : Function.Injective fE := by
    intro c c' hcc'
    by_contra hnecc'
    have hfc : f c = f c' :=
      congrArg (fun x : ↥(E b) => x.1) hcc'
    exact minimumLayer_externalBlock_no_closed_fourStep
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        a c.1 b c'.1 habne (by
          intro h
          apply hnecc'
          exact Subtype.ext h)
        hza (hp c).1 (hf c).1 (hp c').1
        (hp c).2 (hf c).2 (by simpa [hfc] using (hf c').2.symm)
        (hp c').2.symm
  have hcardTypes : Fintype.card ↥C = Fintype.card ↥(E b) := by
    simpa [hcardC, hcardE b]
  refine ⟨fE, (Fintype.bijective_iff_injective_and_card fE).2
    ⟨hfEinj, hcardTypes⟩, ?_⟩
  intro c
  exact ⟨p c, (hp c).1, (hp c).2, (hf c).2⟩

/-- Graph-facing form of the Latin resolution law: for every pair of
exterior points over `a,b`, there is a unique common-nonneighbor owner row
containing the middle point of a two-edge exterior path between them. -/
theorem minimumLayer_saturated_existsUnique_twoStep_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b)
    (hcommon :
      ((minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset a ∩
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset b).card = 1)
    {z y : V}
    (hza : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ a)
    (hyb : y ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ b) :
    let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    ∃! c : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      c ∈ commonNonneighborFinset H a b ∧
        ∃ x : V, x ∈ E c ∧ G.Adj z x ∧ G.Adj x y := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let C := commonNonneighborFinset H a b
  obtain ⟨f, hfbij, hfpath⟩ := minimumLayer_saturated_twoStep_bijection
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
      a b habne hcommon z hza
  obtain ⟨c, hfc⟩ := hfbij.2 ⟨y, hyb⟩
  obtain ⟨x, hxc, hzx, hxf⟩ := hfpath c
  have hfval : (f c).1 = y := congrArg Subtype.val hfc
  have hxy : G.Adj x y := by simpa [hfval] using hxf
  refine ⟨c.1, ⟨c.2, ⟨x, hxc, hzx, hxy⟩⟩, ?_⟩
  intro c' hc'
  by_contra hne
  obtain ⟨x', hxc', hzx', hx'y⟩ := hc'.2
  exact minimumLayer_externalBlock_no_closed_fourStep
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
      a c.1 b c' habne (by
        intro h
        apply hne
        exact h.symm)
      hza hxc hyb hxc' hzx hxy hx'y.symm hzx'.symm

/-- For a zero-common child pair, the two-step matching injection misses
exactly one point of the target exterior row.  This is the combinatorial
precursor of the exterior defect-matching lift. -/
theorem minimumLayer_saturated_zeroCommon_uniqueOmitted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b)
    (hcommon :
      ((minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset a ∩
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset b).card = 0) :
    let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    let C := commonNonneighborFinset H a b
    ∀ z ∈ E a, ∃ f : ↥C → ↥(E b),
      Function.Injective f ∧
      (∀ c : ↥C, ∃ x : V,
        x ∈ E c.1 ∧ G.Adj z x ∧ G.Adj x (f c).1) ∧
      ∃! y : ↥(E b), ∀ c : ↥C, f c ≠ y := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let C := commonNonneighborFinset H a b
  have hsatOrder : s * (s - 1) + 3 = d + s - 1 := by
    rw [hsat]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 1 := ⟨s - 1, by omega⟩
    norm_num
    ring
  have hcardC : C.card + 1 = d - s := by
    rw [card_commonNonneighborFinset H hregChild a b hcommon, hcardChild,
      hsatOrder]
    omega
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardEb : (E b).card = d - s :=
    card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild b
  intro z hza
  obtain ⟨f, hfinj, hfpath⟩ := minimumLayer_saturated_twoStep_injection
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
      a b habne z hza
  have hcardTypes : Fintype.card ↥C + 1 = Fintype.card ↥(E b) := by
    simpa [hcardC, hcardEb]
  exact ⟨f, hfinj, hfpath,
    existsUnique_not_mem_range_of_card_add_one f hfinj hcardTypes⟩

/-- Every common neighbor of exterior points in distinct rows is exterior,
and its owner is a common nonneighbor of the endpoint owners. -/
theorem minimumLayer_saturated_commonNeighbor_has_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b)
    {z y x : V}
    (hza : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ a)
    (hyb : y ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ b)
    (hzx : G.Adj z x) (hxy : G.Adj x y) :
    let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    ∃ c : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      c ∈ commonNonneighborFinset H a b ∧ x ∈ E c := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hza' := Finset.mem_sdiff.mp hza
  have hyb' := Finset.mem_sdiff.mp hyb
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hxOutside : x ∉ U := by
    intro hxU
    obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp hxU
    have hzu : z ∈ E u := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hza'.2⟩
      change u.2.1 = x at hux
      exact (G.mem_neighborFinset u.2.1 z).mpr (by simpa [hux] using hzx.symm)
    have hyu : y ∈ E u := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hyb'.2⟩
      change u.2.1 = x at hux
      exact (G.mem_neighborFinset u.2.1 y).mpr (by simpa [hux] using hxy)
    have hua : u = a := by
      by_contra hua
      have hdisj := hpair (Finset.mem_univ u) (Finset.mem_univ a) hua
      exact (Finset.disjoint_left.mp hdisj hzu hza).elim
    have hub : u = b := by
      by_contra hub
      have hdisj := hpair (Finset.mem_univ u) (Finset.mem_univ b) hub
      exact (Finset.disjoint_left.mp hdisj hyu hyb).elim
    exact habne (hua.symm.trans hub)
  obtain ⟨c, hxc, _hcUnique⟩ :=
    minimumLayer_existsUnique_externalOwner_of_saturated
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat hxOutside
  have hnca : ¬H.Adj c a := by
    intro hca
    have hempty := minimumLayer_saturated_externalBlock_eq_empty_of_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        c a hza hca
    have hxmem : x ∈ G.neighborFinset z ∩ E c :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr hzx, hxc⟩
    rw [hempty] at hxmem
    exact Finset.notMem_empty x hxmem
  have hncb : ¬H.Adj c b := by
    intro hcb
    have hempty := minimumLayer_saturated_externalBlock_eq_empty_of_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        c b hyb hcb
    have hxmem : x ∈ G.neighborFinset y ∩ E c :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y x).mpr hxy.symm, hxc⟩
    rw [hempty] at hxmem
    exact Finset.notMem_empty x hxmem
  refine ⟨c, ?_, hxc⟩
  exact (mem_commonNonneighborFinset_iff H a b c).mpr
    ⟨fun hac => hnca hac.symm, fun hbc => hncb hbc.symm⟩

/-- The unique endpoint omitted by the zero-common two-step resolution is
exactly the unique parent-defect neighbor in the target exterior row. -/
theorem minimumLayer_saturated_existsUnique_defectNeighbor_in_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habne : a ≠ b)
    (hcommon :
      ((minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset a ∩
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).neighborFinset b).card = 0) :
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    ∀ z ∈ E a, ∃! y : ↥(E b), (secondOrderDefectGraph G).Adj z y.1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let C := commonNonneighborFinset H a b
  intro z hza
  obtain ⟨f, hfinj, hfpath, y, hyomit, hyunique⟩ :=
    minimumLayer_saturated_zeroCommon_uniqueOmitted
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        a b habne hcommon z hza
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hzy : z ≠ y.1 := by
    intro hzy
    have hdisj := hpair (Finset.mem_univ a) (Finset.mem_univ b) habne
    exact (Finset.disjoint_left.mp hdisj hza (hzy ▸ y.2)).elim
  have hyCommonZero : (G.neighborFinset z ∩ G.neighborFinset y.1).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxparts := Finset.mem_inter.mp hx
    have hzx : G.Adj z x := (G.mem_neighborFinset z x).mp hxparts.1
    have hxy : G.Adj x y.1 :=
      ((G.mem_neighborFinset y.1 x).mp hxparts.2).symm
    obtain ⟨c, hcC, hxc⟩ := minimumLayer_saturated_commonNeighbor_has_owner
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        a b habne hza y.2 hzx hxy
    let cs : ↥C := ⟨c, hcC⟩
    obtain ⟨x₀, hx₀c, hzx₀, hx₀f⟩ := hfpath cs
    have hcdata := (mem_commonNonneighborFinset_iff H a b c).mp hcC
    obtain ⟨r₁, hr₁, hr₁uniq⟩ :=
      minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
        G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
          c a hza (fun hca => hcdata.1 hca.symm)
    have hxx₀ : x = x₀ :=
      (hr₁uniq x ⟨hxc, hzx⟩).trans (hr₁uniq x₀ ⟨hx₀c, hzx₀⟩).symm
    obtain ⟨r₂, hr₂, hr₂uniq⟩ :=
      minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
        G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
          b c hx₀c (fun hbc => hcdata.2 hbc)
    have hyf : y.1 = (f cs).1 := by
      exact (hr₂uniq y.1 ⟨y.2, by simpa [hxx₀] using hxy⟩).trans
        (hr₂uniq (f cs) ⟨(f cs).2, hx₀f⟩).symm
    exact hyomit cs (Subtype.ext hyf.symm)
  have hyD : D.Adj z y.1 := by
    have hformula := card_common_eq_if_secondOrderDefect G hfree z y.1 hzy
    by_contra hyD
    have hynmem : y.1 ∉ D.neighborFinset z := by
      simpa [D.mem_neighborFinset] using hyD
    rw [if_neg hynmem, hyCommonZero] at hformula
    omega
  refine ⟨y, hyD, ?_⟩
  intro y' hy'D
  have hzy' : z ≠ y'.1 := D.ne_of_adj hy'D
  have hy'CommonZero :
      (G.neighborFinset z ∩ G.neighborFinset y'.1).card = 0 := by
    have hformula := card_common_eq_if_secondOrderDefect G hfree z y'.1 hzy'
    have hy'mem : y'.1 ∈ D.neighborFinset z :=
      (D.mem_neighborFinset z y'.1).mpr hy'D
    rw [if_pos hy'mem] at hformula
    exact hformula
  have hy'omit : ∀ c : ↥C, f c ≠ y' := by
    intro c hfc
    obtain ⟨x, hxc, hzx, hxf⟩ := hfpath c
    have hxmem : x ∈ G.neighborFinset z ∩ G.neighborFinset y'.1 := by
      apply Finset.mem_inter.mpr
      refine ⟨(G.mem_neighborFinset z x).mpr hzx, ?_⟩
      exact (G.mem_neighborFinset y'.1 x).mpr (by
        have : G.Adj x y'.1 := by simpa [hfc] using hxf
        exact this.symm)
    rw [Finset.card_eq_zero.mp hy'CommonZero] at hxmem
    exact Finset.notMem_empty x hxmem
  exact hyunique y' hy'omit

/-- Cover-facing form: every child defect edge lifts to a perfect matching
between the corresponding exterior rows in the parent defect graph. -/
theorem minimumLayer_saturated_childDefect_lifts_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a b : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (habD : (secondOrderDefectGraph
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀)).Adj a b) :
    let E := minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀
    ∀ z ∈ E a, ∃! y : ↥(E b), (secondOrderDefectGraph G).Adj z y.1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  have hfreeH : ¬containsC4 _ H := minimumLayerGraph_c4Free G D c₀ hfree
  have habne : a ≠ b := (secondOrderDefectGraph H).ne_of_adj habD
  have hcommon : (H.neighborFinset a ∩ H.neighborFinset b).card = 0 := by
    have hformula := card_common_eq_if_secondOrderDefect H hfreeH a b habne
    have hbmem : b ∈ (secondOrderDefectGraph H).neighborFinset a :=
      ((secondOrderDefectGraph H).mem_neighborFinset a b).mpr habD
    rw [if_pos hbmem] at hformula
    exact hformula
  exact minimumLayer_saturated_existsUnique_defectNeighbor_in_row
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
      a b habne hcommon

/-- Degree exhaustion: every parent-defect neighbor of an exterior point is
in the exterior row of a child-defect neighbor of its owner.  Hence the
exterior parent-defect graph is genuinely a cover of the child defect graph,
with no additional cross-layer or unrelated-row defect edges. -/
theorem minimumLayer_saturated_defectNeighbor_has_childOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (a : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    {z y : V}
    (hza : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ a)
    (hzyD : (secondOrderDefectGraph G).Adj z y) :
    ∃ b : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (secondOrderDefectGraph
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀)).Adj a b ∧
      y ∈ minimumLayerExternalNeighborFinset
        G (secondOrderDefectGraph G) c₀ b := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let DH := secondOrderDefectGraph H
  let B := DH.neighborFinset a
  have hfreeH : ¬containsC4 _ H := minimumLayerGraph_c4Free G D c₀ hfree
  have hDHdegree : DH.degree a = 2 :=
    secondOrderDefectGraph_degree_eq_two_of_regular_boundary
      H hfreeH hregChild hcardChild a
  have hcardB : B.card = 2 := by
    rw [DH.card_neighborFinset_eq_degree, hDHdegree]
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hDdegree : D.degree z = 2 :=
    secondOrderDefectGraph_degree_eq_two_of_regular_boundary
      G hfree hregParent hcard z
  have hcardDz : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree, hDdegree]
  have hlift : ∀ b : ↥B, ∃! y : ↥(E b.1), D.Adj z y.1 := by
    intro b
    exact minimumLayer_saturated_childDefect_lifts_matching
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        a b.1 ((DH.mem_neighborFinset a b.1).mp b.2) z hza
  let f : ↥B → V := fun b => (Classical.choose (hlift b)).1
  have hfrow : ∀ b : ↥B, f b ∈ E b.1 := fun b => (Classical.choose (hlift b)).2
  have hfD : ∀ b : ↥B, D.Adj z (f b) := fun b =>
    (Classical.choose_spec (hlift b)).1
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hfinj : Function.Injective f := by
    intro b b' hbb'
    apply Subtype.ext
    by_contra hnebb'
    have hdisj := hpair (Finset.mem_univ b.1) (Finset.mem_univ b'.1) hnebb'
    exact Finset.disjoint_left.mp hdisj (hfrow b) (hbb' ▸ hfrow b')
  let fD : ↥B → ↥(D.neighborFinset z) := fun b =>
    ⟨f b, (D.mem_neighborFinset z (f b)).mpr (hfD b)⟩
  have hfDinj : Function.Injective fD := by
    intro b b' h
    apply hfinj
    exact congrArg Subtype.val h
  have hcardTypes : Fintype.card ↥B = Fintype.card ↥(D.neighborFinset z) := by
    rw [Fintype.card_coe B, Fintype.card_coe (D.neighborFinset z),
      hcardB, hcardDz]
  have hfDbij : Function.Bijective fD :=
    (Fintype.bijective_iff_injective_and_card fD).2 ⟨hfDinj, hcardTypes⟩
  have hymem : y ∈ D.neighborFinset z := (D.mem_neighborFinset z y).mpr hzyD
  obtain ⟨b, hby⟩ := hfDbij.2 ⟨y, hymem⟩
  refine ⟨b.1, (DH.mem_neighborFinset a b.1).mp b.2, ?_⟩
  have hfval : f b = y := congrArg Subtype.val hby
  exact hfval ▸ hfrow b

end

end Erdos85
