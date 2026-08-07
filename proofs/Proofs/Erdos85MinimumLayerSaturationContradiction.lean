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

end

section

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

end

end Erdos85
