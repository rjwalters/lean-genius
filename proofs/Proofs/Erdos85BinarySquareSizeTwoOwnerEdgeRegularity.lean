import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph
import Proofs.Erdos85BinarySquareSizeTwoStarPerfectMatching
import Proofs.Erdos85RegularTwoFoldOrderOpenWedge

/-!
# Edge regularity obstruction for size-two owner colors

This begins the direct combinatorial route from the selector-line-graph model
to adjacent-codegree irregularity.  The first graph-specific step records an
open wedge in every normalized size-two selector graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem card_two_inter_two_pairs_iff
    {W : Type*} [DecidableEq W] (s : Finset W) {u v w : W}
    (hs : s.card = 2) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (s ∩ {u, v}).Nonempty ∧ (s ∩ {u, w}).Nonempty ↔
      u ∈ s ∨ s = {v, w} := by
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨r, hr⟩⟩
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hp hr
    by_cases hu : u ∈ s
    · exact Or.inl hu
    · right
      have hv : v ∈ s := by
        rcases hp.2 with rfl | rfl
        · exact (hu hp.1).elim
        · exact hp.1
      have hw : w ∈ s := by
        rcases hr.2 with rfl | rfl
        · exact (hu hr.1).elim
        · exact hr.1
      obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hs
      rw [hsab] at hv hw ⊢
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw ⊢
      aesop
  · intro h
    rcases h with h | h
    · exact ⟨⟨u, Finset.mem_inter.mpr ⟨h, by simp⟩⟩,
        ⟨u, Finset.mem_inter.mpr ⟨h, by simp⟩⟩⟩
    · rw [h]
      exact ⟨⟨v, Finset.mem_inter.mpr ⟨by simp, by simp⟩⟩,
        ⟨w, Finset.mem_inter.mpr ⟨by simp, by simp⟩⟩⟩

/-- A selector star is just the ambient neighborhood of its center, hence
has cardinality `q`.  Recording this in the selector language avoids a
second edge-bijection construction in the line-graph codegree count. -/
theorem binarySquare_regular_sizeTwoSelectorStar_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (u : c.supp) :
    ((Finset.univ : Finset V).filter fun x =>
      u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x).card = q := by
  have hstar :
      (Finset.univ : Finset V).filter (fun x =>
          u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x) =
        G.neighborFinset u.1 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      componentNeighborFinset, Finset.mem_filter, G.mem_neighborFinset]
    constructor
    · rintro ⟨hxu, hucomp⟩
      exact hxu.symm
    · intro hux
      exact ⟨hux.symm,
        (SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2⟩
  rw [hstar, G.card_neighborFinset_eq_degree, hreg]

/-- Common neighbors of two owner vertices whose selectors form the wedge
`uv, uw` are exactly the other vertices in the selector star at `u`, plus
the possible closing selector `vw`. -/
theorem binarySquare_regular_sizeTwoOwner_commonNeighbors_mem_iff_wedge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (u v w : c.supp) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (x y z : V)
    (hx : componentNeighborFinset G (secondOrderDefectGraph G) c x =
      {u.1, v.1})
    (hy : componentNeighborFinset G (secondOrderDefectGraph G) c y =
      {u.1, w.1}) :
    z ∈ (componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y ↔
      z ≠ x ∧ z ≠ y ∧
        (u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z ∨
          componentNeighborFinset G (secondOrderDefectGraph G) c z =
            {v.1, w.1}) := by
  have hselCard := binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard c hc z
  rw [SimpleGraph.mem_commonNeighbors]
  simp only [componentOwnerGraph]
  rw [hx, hy]
  simp only [ne_comm, Finset.inter_comm]
  have hp := card_two_inter_two_pairs_iff
    (componentNeighborFinset G (secondOrderDefectGraph G) c z)
    hselCard (Subtype.coe_injective.ne huv) (Subtype.coe_injective.ne huw)
      (Subtype.coe_injective.ne hvw)
  tauto

/-- An open selector wedge gives the smaller owner edge-codegree `q - 2`.
This is the numerical half of the wedge formula needed to contradict owner
edge-regularity in the presence of a closed wedge. -/
theorem binarySquare_regular_sizeTwoOwner_openWedge_codegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (u v w : c.supp) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (x y : V)
    (hx : componentNeighborFinset G (secondOrderDefectGraph G) c x =
      {u.1, v.1})
    (hy : componentNeighborFinset G (secondOrderDefectGraph G) c y =
      {u.1, w.1})
    (hopen : ¬ ∃ z : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c z = {v.1, w.1}) :
    Fintype.card
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y) =
        q - 2 := by
  let star := (Finset.univ : Finset V).filter fun z =>
    u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z
  have hxy : x ≠ y := by
    intro h
    subst y
    have hp : ({u.1, v.1} : Finset V) = {u.1, w.1} := hx.symm.trans hy
    have : v.1 = w.1 := by
      have hv : v.1 ∈ ({u.1, w.1} : Finset V) := by rw [← hp]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      exact hv.resolve_left (Subtype.coe_injective.ne huv).symm
    exact hvw (Subtype.ext this)
  have hxstar : x ∈ star := by simp [star, hx]
  have hystar : y ∈ star := by simp [star, hy]
  have hfin :
      (Finset.univ : Finset V).filter (fun z =>
          z ∈ (componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y) =
        (star.erase x).erase y := by
    ext z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_erase]
    rw [binarySquare_regular_sizeTwoOwner_commonNeighbors_mem_iff_wedge
      G hfree hq hreg hcard c hc u v w huv huw hvw x y z hx hy]
    have hnclose :
        componentNeighborFinset G (secondOrderDefectGraph G) c z ≠ {v.1, w.1} :=
      fun hz => hopen ⟨z, hz⟩
    simp only [hnclose, or_false]
    simp only [star, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [Fintype.card_subtype, hfin]
  rw [Finset.card_erase_of_mem]
  · rw [Finset.card_erase_of_mem hxstar]
    have hstarCard := binarySquare_regular_sizeTwoSelectorStar_card G hreg c u
    change star.card = q at hstarCard
    omega
  · exact Finset.mem_erase.mpr ⟨hxy.symm, hystar⟩

/-- A closed selector wedge gives the larger owner edge-codegree `q - 1`. -/
theorem binarySquare_regular_sizeTwoOwner_closedWedge_codegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (u v w : c.supp) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (x y t : V)
    (hx : componentNeighborFinset G (secondOrderDefectGraph G) c x =
      {u.1, v.1})
    (hy : componentNeighborFinset G (secondOrderDefectGraph G) c y =
      {u.1, w.1})
    (ht : componentNeighborFinset G (secondOrderDefectGraph G) c t =
      {v.1, w.1}) :
    Fintype.card
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y) =
        q - 1 := by
  let star := (Finset.univ : Finset V).filter fun z =>
    u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c z
  have hxy : x ≠ y := by
    intro h
    subst y
    have hp : ({u.1, v.1} : Finset V) = {u.1, w.1} := hx.symm.trans hy
    have hv : v.1 ∈ ({u.1, w.1} : Finset V) := by rw [← hp]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    exact hvw (Subtype.ext (hv.resolve_left (Subtype.coe_injective.ne huv).symm))
  have hxstar : x ∈ star := by simp [star, hx]
  have hystar : y ∈ star := by simp [star, hy]
  have htstar : t ∉ star := by
    simp only [star, Finset.mem_filter, Finset.mem_univ, true_and, ht,
      Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim (Subtype.coe_injective.ne huv) (Subtype.coe_injective.ne huw)
  have htUnique : ∀ z : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c z = {v.1, w.1} →
        z = t := by
    intro z hz
    apply binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
      G hfree hq hreg hcard c hc
    exact hz.trans ht.symm
  have hfin :
      (Finset.univ : Finset V).filter (fun z =>
          z ∈ (componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y) =
        insert t ((star.erase x).erase y) := by
    ext z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    rw [binarySquare_regular_sizeTwoOwner_commonNeighbors_mem_iff_wedge
      G hfree hq hreg hcard c hc u v w huv huw hvw x y z hx hy]
    constructor
    · rintro ⟨hzx, hzy, hzstar | hzclose⟩
      · exact Or.inr ⟨hzy, hzx, by simpa [star] using hzstar⟩
      · exact Or.inl (htUnique z hzclose)
    · rintro (rfl | ⟨hzy, hzx, hzstar⟩)
      · exact ⟨fun h => by subst x; exact htstar hxstar,
          fun h => by subst y; exact htstar hystar, Or.inr ht⟩
      · exact ⟨hzx, hzy, Or.inl (by simpa [star] using hzstar)⟩
  rw [Fintype.card_subtype, hfin, Finset.card_insert_of_notMem]
  · rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem hxstar]
      have hstarCard := binarySquare_regular_sizeTwoSelectorStar_card G hreg c u
      change star.card = q at hstarCard
      omega
    · exact Finset.mem_erase.mpr ⟨hxy.symm, hystar⟩
  · simp only [Finset.mem_erase, not_and_or]
    exact Or.inr (Or.inr htstar)

/-- If adjacent owner pairs had constant codegree, then the size-two selector
graph would be triangle-free.  The open wedge supplies codegree `q-2`; any
closed wedge would supply `q-1`. -/
theorem binarySquare_regular_sizeTwoOwner_edgeCodegree_constant_implies_selector_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconst : ∀ ⦃x y a b : V⦄,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y →
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj a b →
      Fintype.card
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors x y) =
        Fintype.card
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).commonNeighbors a b)) :
    ∀ ⦃u v w : c.supp⦄,
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj u v →
      (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj u w →
      v ≠ w →
      ¬ (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).Adj v w := by
  let S := sizeTwoSelectorGraph G (secondOrderDefectGraph G) c
  have hcardSupp : Fintype.card c.supp = q * 2 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = q * 2 := hc
  obtain ⟨u₀, v₀, w₀, h₀uv, h₀uw, h₀vw, h₀open⟩ :=
    regular_two_mul_order_exists_open_wedge S (by omega) hcardSupp
      (binarySquare_regular_sizeTwoSelectorGraph_degree
        G hfree hq hreg hcard c hc)
  obtain ⟨x₀, hx₀⟩ := h₀uv.2
  obtain ⟨y₀, hy₀⟩ := h₀uw.2
  have h₀noClose : ¬ ∃ t : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c t = {v₀.1, w₀.1} := by
    intro ht
    exact h₀open ⟨h₀vw, ht⟩
  have h₀xy : x₀ ≠ y₀ := by
    intro h
    subst y₀
    have hp : ({u₀.1, v₀.1} : Finset V) = {u₀.1, w₀.1} := hx₀.symm.trans hy₀
    have hv : v₀.1 ∈ ({u₀.1, w₀.1} : Finset V) := by rw [← hp]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    exact h₀vw (Subtype.ext
      (hv.resolve_left (Subtype.coe_injective.ne h₀uv.1).symm))
  have h₀owner :
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x₀ y₀ := by
    rw [binarySquare_regular_sizeTwoPart_ownerAdj_iff_selector_intersects]
    refine ⟨h₀xy, u₀.1, ?_⟩
    rw [hx₀, hy₀]
    simp
  have h₀codeg := binarySquare_regular_sizeTwoOwner_openWedge_codegree
    G hfree hq hreg hcard c hc u₀ v₀ w₀ h₀uv.1 h₀uw.1 h₀vw
      x₀ y₀ hx₀ hy₀ h₀noClose
  intro u v w huv huw hvw hvwAdj
  obtain ⟨x, hx⟩ := huv.2
  obtain ⟨y, hy⟩ := huw.2
  obtain ⟨t, ht⟩ := hvwAdj.2
  have hxy : x ≠ y := by
    intro h
    subst y
    have hp : ({u.1, v.1} : Finset V) = {u.1, w.1} := hx.symm.trans hy
    have hv : v.1 ∈ ({u.1, w.1} : Finset V) := by rw [← hp]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    exact hvw (Subtype.ext
      (hv.resolve_left (Subtype.coe_injective.ne huv.1).symm))
  have howner :
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y := by
    rw [binarySquare_regular_sizeTwoPart_ownerAdj_iff_selector_intersects]
    refine ⟨hxy, u.1, ?_⟩
    rw [hx, hy]
    simp
  have hcodeg := binarySquare_regular_sizeTwoOwner_closedWedge_codegree
    G hfree hq hreg hcard c hc u v w huv.1 huw.1 hvw x y t hx hy ht
  have heq := hconst h₀owner howner
  rw [h₀codeg, hcodeg] at heq
  omega

/-- The selector graph of a normalized size-two defect component contains
two incident selector edges whose other endpoints are not joined. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_exists_open_wedge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    let S := sizeTwoSelectorGraph G (secondOrderDefectGraph G) c
    ∃ u v w, S.Adj u v ∧ S.Adj u w ∧ v ≠ w ∧ ¬ S.Adj v w := by
  let S := sizeTwoSelectorGraph G (secondOrderDefectGraph G) c
  have hcardSupp : Fintype.card c.supp = q * 2 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = q * 2 := hc
  exact regular_two_mul_order_exists_open_wedge S (by omega) hcardSupp
    (binarySquare_regular_sizeTwoSelectorGraph_degree
      G hfree hq hreg hcard c hc)

#print axioms binarySquare_regular_sizeTwoSelectorStar_card
#print axioms binarySquare_regular_sizeTwoOwner_commonNeighbors_mem_iff_wedge
#print axioms binarySquare_regular_sizeTwoOwner_openWedge_codegree
#print axioms binarySquare_regular_sizeTwoOwner_closedWedge_codegree
#print axioms binarySquare_regular_sizeTwoOwner_edgeCodegree_constant_implies_selector_triangleFree
#print axioms binarySquare_regular_sizeTwoSelectorGraph_exists_open_wedge

end

end Erdos85
