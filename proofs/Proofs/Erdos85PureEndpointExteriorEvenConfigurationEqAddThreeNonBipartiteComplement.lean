import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeOddDegreeTwoSector
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # The odd `m+3` complement sector is non-bipartite -/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- A finite two-regular graph has even order whenever it is bipartite. -/
theorem twoRegular_bipartite_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 2) (hbip : G.IsBipartite) :
    Even (Fintype.card V) := by
  classical
  obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
  have hsupport : G.support = Set.univ := by
    ext v
    simp only [Set.mem_univ, iff_true]
    rw [← G.degree_pos_iff_mem_support]
    simpa [hreg.degree_eq v]
  have hcover : s ∪ t = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro v _
    have hv : v ∈ G.support := by simp [hsupport]
    exact isBipartiteWith_support_subset hst hv
  let sf := s.toFinset
  let tf := t.toFinset
  have hstFin : G.IsBipartiteWith (↑sf : Set V) (↑tf : Set V) := by
    simpa [sf, tf] using hst
  have hsum := isBipartiteWith_sum_degrees_eq hstFin
  have hstCard : sf.card = tf.card := by
    have htwo : 2 * sf.card = 2 * tf.card := by
      simpa [hreg.degree_eq, mul_comm] using hsum
    omega
  have hcard : Fintype.card V = sf.card + tf.card := by
    have hunion : sf ∪ tf = Finset.univ := by
      ext v
      simpa [sf, tf] using Set.ext_iff.mp hcover v
    have hdisFin : Disjoint sf tf := by
      rw [Finset.disjoint_left]
      intro v hvs hvt
      exact Set.disjoint_left.mp hst.disjoint
        (by simpa [sf] using hvs) (by simpa [tf] using hvt)
    have hc := card_union_of_disjoint hdisFin
    rw [hunion] at hc
    simpa using hc
  refine ⟨sf.card, ?_⟩
  omega

/-- Therefore a finite two-regular graph of odd order is not bipartite. -/
theorem twoRegular_odd_card_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 2) (hodd : Odd (Fintype.card V)) :
    ¬ G.IsBipartite := by
  intro hbip
  exact Nat.not_even_iff_odd.mpr hodd (twoRegular_bipartite_card_even G hreg hbip)

/-- Degree in the symmetric-relation graph induced on a finite vertex set is
the corresponding filtered-cardinality inside that set. -/
theorem fromRel_subtype_degree_eq_filter
    {α : Type*} [DecidableEq α] (R : Finset α)
    (Rel : α → α → Prop) [DecidableRel Rel]
    (hsym : Symmetric Rel)
    (w : {x // x ∈ R}) :
    (SimpleGraph.fromRel (fun x y : {x // x ∈ R} => Rel x.1 y.1)).degree w =
      ((R.erase w.1).filter fun u => Rel w.1 u).card := by
  classical
  let H := SimpleGraph.fromRel (fun x y : {x // x ∈ R} => Rel x.1 y.1)
  have himage : (H.neighborFinset w).image Subtype.val =
      (R.erase w.1).filter (fun u => Rel w.1 u) := by
    ext u
    simp only [mem_image, mem_neighborFinset, mem_filter, mem_erase]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hadj := (SimpleGraph.fromRel_adj _ _ _).mp hv
      exact ⟨⟨fun h => hadj.1 (Subtype.ext h.symm), v.2⟩,
        hadj.2.elim id (fun h => hsym h)⟩
    · rintro ⟨⟨huw, huR⟩, hrel⟩
      let v : {x // x ∈ R} := ⟨u, huR⟩
      refine ⟨v, ?_, rfl⟩
      exact (SimpleGraph.fromRel_adj _ _ _).mpr
        ⟨fun h => huw (congrArg Subtype.val h).symm, Or.inl hrel⟩
  calc
    H.degree w = (H.neighborFinset w).card := rfl
    _ = ((H.neighborFinset w).image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective]
    _ = ((R.erase w.1).filter fun u => Rel w.1 u).card := by rw [himage]

/-- The nonmeeting graph on the degree-two sector of an endpoint exterior
`m+3` even configuration is non-bipartite. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_nonmeetingGraph_notBipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 3 →
      let R₂ := T.filter fun w =>
        ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 2
      let H := SimpleGraph.fromRel
        (fun w u : {x // x ∈ R₂} => ¬ (row w.1 ∩ row u.1).Nonempty)
      ¬ H.IsBipartite := by
  classical
  dsimp only
  intro T heven hTcard
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let R₂ := T.filter fun w =>
    ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 2
  let Rel : W → W → Prop := fun w u => ¬ (row w ∩ row u).Nonempty
  let H := SimpleGraph.fromRel
    (fun w u : {x // x ∈ R₂} => Rel w.1 u.1)
  have hoddR₂ : Odd R₂.card := by
    change Odd ((T.filter fun w =>
      ((T.erase w).filter fun u =>
        ¬ (row w ∩ row u).Nonempty).card = 2).card)
    exact
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_degreeTwoSectorOdd
        G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
        T heven hTcard
  have hmissing :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard
  have hmissingRow : ∀ w ∈ T,
      ((T.erase w).filter fun u => Rel w u).card = 0 ∨
      ((T.erase w).filter fun u => Rel w u).card = 2 := by
    intro w hw
    have hm := hmissing w hw
    change ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 0 ∨
      ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 2
    simpa only [Rel, row, inter_assoc] using hm
  have hsym : Symmetric Rel := by
    intro w u h
    simpa [Rel, inter_comm] using h
  have hclosed : ∀ w ∈ R₂, ∀ u ∈ T.erase w, Rel w u → u ∈ R₂ := by
    intro w hwR u hu hrel
    have hwT := (mem_filter.mp hwR).1
    have huT := (mem_erase.mp hu).2
    rcases hmissingRow u huT with hzero | htwo
    · have hwmem : w ∈ (T.erase u).filter fun z => Rel u z := by
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨(mem_erase.mp hu).1.symm, hwT⟩, ?_⟩
        exact hsym hrel
      have hpos := card_pos.mpr ⟨w, hwmem⟩
      omega
    · exact mem_filter.mpr ⟨huT, htwo⟩
  have hregH : H.IsRegularOfDegree 2 := by
    intro w
    rw [show H.degree w =
      ((R₂.erase w.1).filter fun u => Rel w.1 u).card by
        exact fromRel_subtype_degree_eq_filter R₂ Rel hsym w]
    have heq : (R₂.erase w.1).filter (fun u => Rel w.1 u) =
        (T.erase w.1).filter (fun u => Rel w.1 u) := by
      ext u
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨huw, huR⟩, hrel⟩
        exact ⟨⟨huw, (mem_filter.mp huR).1⟩, hrel⟩
      · rintro ⟨hu, hrel⟩
        exact ⟨⟨hu.1, hclosed w.1 w.2 u (mem_erase.mpr hu) hrel⟩, hrel⟩
    rw [heq]
    exact (mem_filter.mp w.2).2
  have hoddType : Odd (Fintype.card {x // x ∈ R₂}) := by
    simpa using hoddR₂
  exact twoRegular_odd_card_not_bipartite H hregH hoddType

end

end Erdos85

#print axioms Erdos85.twoRegular_bipartite_card_even
#print axioms Erdos85.twoRegular_odd_card_not_bipartite
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_nonmeetingGraph_notBipartite
