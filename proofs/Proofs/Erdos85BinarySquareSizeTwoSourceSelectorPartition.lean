import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph

/-! # Source-component partition of a size-two selector graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The edges of a size-two selector graph whose unique ambient selector
vertex belongs to a specified source defect component. -/
def sourceIndexedSizeTwoSelectorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph owner.supp where
  Adj u v := u ≠ v ∧ ∃ x : source.supp,
    componentNeighborFinset G (secondOrderDefectGraph G) owner x.1 =
      {u.1, v.1}
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨x, hx⟩ := h.2
    exact ⟨x, by simpa [Finset.pair_comm] using hx⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance sourceIndexedSizeTwoSelectorGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (sourceIndexedSizeTwoSelectorGraph G source owner).Adj :=
  Classical.decRel _

/-- **Source-edge partition.**  Every edge of a normalized size-two selector
graph belongs to exactly one source defect component: the component of its
unique ambient selector vertex. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_adj_iff_existsUnique_source
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2) (u v : owner.supp) :
    (sizeTwoSelectorGraph G (secondOrderDefectGraph G) owner).Adj u v ↔
      ∃! source : (secondOrderDefectGraph G).ConnectedComponent,
        (sourceIndexedSizeTwoSelectorGraph G source owner).Adj u v := by
  let D := secondOrderDefectGraph G
  constructor
  · rintro ⟨huv, x, hx⟩
    have hnotD :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard owner howner u v huv).mp ⟨x, hx⟩
    have hunique :=
      (binarySquare_regular_sizeTwoPart_existsUnique_pair_iff_not_defectAdj
        G hfree hq hreg hcard owner howner u v huv).mpr hnotD
    let source := D.connectedComponentMk x
    have hxmem : x ∈ source.supp := ConnectedComponent.connectedComponentMk_mem
    refine ⟨source, ⟨huv, ⟨⟨x, hxmem⟩, hx⟩⟩, ?_⟩
    intro source' hs'
    obtain ⟨y, hy⟩ := hs'.2
    have hyx : y.1 = x := hunique.unique hy hx
    have hycomp : D.connectedComponentMk y.1 = source' :=
      (ConnectedComponent.mem_supp_iff source' y.1).mp y.2
    rw [hyx] at hycomp
    exact hycomp.symm
  · rintro ⟨source, hs, _hunique⟩
    exact ⟨hs.1, ⟨hs.2.choose.1, hs.2.choose_spec⟩⟩

/-- Distinct source components contribute edge-disjoint subgraphs of the
size-two selector graph. -/
theorem sourceIndexedSizeTwoSelectorGraph_adj_disjoint_of_source_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) {u v : owner.supp} :
    (sourceIndexedSizeTwoSelectorGraph G source owner).Adj u v →
      ¬ (sourceIndexedSizeTwoSelectorGraph G target owner).Adj u v := by
  intro hs ht
  have hall :=
    (binarySquare_regular_sizeTwoSelectorGraph_adj_iff_existsUnique_source
      G hfree hq hreg hcard owner howner u v).mp
      ⟨hs.1, ⟨hs.2.choose.1, hs.2.choose_spec⟩⟩
  exact hst (hall.unique ht hs).symm

/-- A source component of normalized size `m` contributes an `m`-regular
spanning edge layer to every normalized size-two selector graph. -/
theorem binarySquare_regular_sourceIndexedSizeTwoSelectorGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    {m : ℕ} (hsource : source.supp.ncard = q * m)
    (howner : owner.supp.ncard = q * 2) (u : owner.supp) :
    (sourceIndexedSizeTwoSelectorGraph G source owner).degree u = m := by
  classical
  let D := secondOrderDefectGraph G
  let H := sourceIndexedSizeTwoSelectorGraph G source owner
  let T := (source.supp.toFinite.toFinset).filter fun x =>
    u.1 ∈ componentNeighborFinset G D owner x
  have hTcard : T.card = m := by
    exact binarySquare_regular_selector_incidence_from_component
      G hfree hq hreg hcard owner source hsource u
  let f : (v : owner.supp) → v ∈ H.neighborFinset u → V := fun v hv =>
    (Classical.choose (((H.mem_neighborFinset u v).mp hv).2)).1
  have hfspec (v : owner.supp) (hv : v ∈ H.neighborFinset u) :
      componentNeighborFinset G D owner (f v hv) = {u.1, v.1} :=
    Classical.choose_spec (((H.mem_neighborFinset u v).mp hv).2)
  rw [← H.card_neighborFinset_eq_degree, ← hTcard]
  apply Finset.card_bij f
  · intro v hv
    have hxmem : f v hv ∈ source.supp :=
      (Classical.choose (((H.mem_neighborFinset u v).mp hv).2)).2
    apply Finset.mem_filter.mpr
    refine ⟨by simpa [T] using hxmem, ?_⟩
    rw [hfspec v hv]
    simp
  · intro v₁ hv₁ v₂ hv₂ heq
    have hpairs : ({u.1, v₁.1} : Finset V) = {u.1, v₂.1} := by
      rw [← hfspec v₁ hv₁, ← hfspec v₂ hv₂, heq]
    have hv₁mem : v₁.1 ∈ ({u.1, v₂.1} : Finset V) := by
      rw [← hpairs]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv₁mem
    rcases hv₁mem with hvu | hvv
    · have hne := ((H.mem_neighborFinset u v₁).mp hv₁).ne
      exact False.elim (hne (Subtype.ext hvu.symm))
    · exact Subtype.ext hvv
  · intro x hxT
    have hxData := Finset.mem_filter.mp hxT
    have hxSupp : x ∈ source.supp := by simpa [T] using hxData.1
    have htwo : (componentNeighborFinset G D owner x).card = 2 := by
      have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
        G hfree hq hreg hcard (D.connectedComponentMk x) owner (x := x) (by rfl)
      rw [howner] at hmul
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    obtain ⟨p, r, hpr, hpair⟩ := Finset.card_eq_two.mp htwo
    have huPair : u.1 = p ∨ u.1 = r := by
      have := hxData.2
      rw [hpair] at this
      simpa [eq_comm] using this
    rcases huPair with hup | hur
    · have hrmem : r ∈ componentNeighborFinset G D owner x := by
        rw [hpair]
        simp
      have hrOwner : r ∈ owner.supp :=
        (ConnectedComponent.mem_supp_iff owner r).mpr
          (Finset.mem_filter.mp hrmem).2
      let v : owner.supp := ⟨r, hrOwner⟩
      have huv : u ≠ v := by
        intro huv
        apply hpr
        exact hup.symm.trans (congrArg Subtype.val huv)
      have hadj : H.Adj u v := by
        refine ⟨huv, ⟨⟨x, hxSupp⟩, ?_⟩⟩
        simpa [v, hup] using hpair
      have hv : v ∈ H.neighborFinset u := (H.mem_neighborFinset u v).mpr hadj
      refine ⟨v, hv, ?_⟩
      apply binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
        G hfree hq hreg hcard owner howner
      change componentNeighborFinset G D owner (f v hv) =
        componentNeighborFinset G D owner x
      rw [hfspec v hv]
      simpa [v, hup] using hpair.symm
    · have hpmem : p ∈ componentNeighborFinset G D owner x := by
        rw [hpair]
        simp
      have hpOwner : p ∈ owner.supp :=
        (ConnectedComponent.mem_supp_iff owner p).mpr
          (Finset.mem_filter.mp hpmem).2
      let v : owner.supp := ⟨p, hpOwner⟩
      have huv : u ≠ v := by
        intro huv
        apply hpr
        exact (congrArg Subtype.val huv).symm.trans hur
      have hadj : H.Adj u v := by
        refine ⟨huv, ⟨⟨x, hxSupp⟩, ?_⟩⟩
        simpa [v, hur, Finset.pair_comm] using hpair
      have hv : v ∈ H.neighborFinset u := (H.mem_neighborFinset u v).mpr hadj
      refine ⟨v, hv, ?_⟩
      apply binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
        G hfree hq hreg hcard owner howner
      change componentNeighborFinset G D owner (f v hv) =
        componentNeighborFinset G D owner x
      rw [hfspec v hv]
      simpa [v, hur, Finset.pair_comm] using hpair.symm

/-- Order-64 `[6,2]` specialization: the selector-complement graph on the
size-two component is edge-partitioned into a 6-factor and a 2-factor. -/
theorem orderSixtyFour_sixTwo_sourceIndexedSizeTwoSelectorGraph_degrees
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (large small : (secondOrderDefectGraph G).ConnectedComponent)
    (hlarge : large.supp.ncard = 48)
    (hsmall : small.supp.ncard = 16) (u : small.supp) :
    (sourceIndexedSizeTwoSelectorGraph G large small).degree u = 6 ∧
      (sourceIndexedSizeTwoSelectorGraph G small small).degree u = 2 := by
  constructor
  · exact binarySquare_regular_sourceIndexedSizeTwoSelectorGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
      large small (m := 6) (by norm_num [hlarge]) (by norm_num [hsmall]) u
  · exact binarySquare_regular_sourceIndexedSizeTwoSelectorGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
      small small (m := 2) (by norm_num [hsmall]) (by norm_num [hsmall]) u

end

end Erdos85
