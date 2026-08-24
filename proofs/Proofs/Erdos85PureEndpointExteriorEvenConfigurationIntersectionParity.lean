import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGirth

/-!
# Intersection parity of an even block configuration

In a linear incidence system, the number of selected blocks meeting a fixed
outside block is the sum of the selected point-degrees along that block.
Consequently an even incidence configuration is also even in the block
intersection graph.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- A fixed block meets an even number of blocks from any pointwise-even
configuration, provided every such pair has intersection size at most one. -/
theorem linear_even_configuration_meeting_card_even
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β) (p : α)
    (heven : ∀ l ∈ L, Even ((T.filter fun q => Inc q l).card))
    (hlinear : ∀ q ∈ T,
      (L.filter fun l => Inc p l ∧ Inc q l).card ≤ 1) :
    Even ((T.filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card) := by
  classical
  let d : β → ℕ := fun l => (T.filter fun q => Inc q l).card
  have hindicator : ∀ q ∈ T,
      (if (L.filter fun l => Inc p l ∧ Inc q l).Nonempty then 1 else 0) =
        (L.filter fun l => Inc p l ∧ Inc q l).card := by
    intro q hq
    by_cases hn : (L.filter fun l => Inc p l ∧ Inc q l).Nonempty
    · simp only [hn, if_true]
      exact Nat.le_antisymm (card_pos.mpr hn) (hlinear q hq)
    · simp only [hn, if_false]
      exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)).symm
  have hcount : (T.filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card =
      ∑ l ∈ L.filter (fun l => Inc p l), d l := by
    calc
      (T.filter fun q =>
          (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card =
          ∑ q ∈ T, if (L.filter fun l => Inc p l ∧ Inc q l).Nonempty
            then 1 else 0 := by rw [card_filter]
      _ = ∑ q ∈ T, (L.filter fun l => Inc p l ∧ Inc q l).card := by
            apply sum_congr rfl
            intro q hq
            exact hindicator q hq
      _ = ∑ q ∈ T, ∑ l ∈ L,
          if Inc p l ∧ Inc q l then 1 else 0 := by
            apply sum_congr rfl
            intro q hq
            rw [card_filter]
      _ = ∑ l ∈ L, ∑ q ∈ T,
          if Inc p l ∧ Inc q l then 1 else 0 := by rw [sum_comm]
      _ = ∑ l ∈ L, if Inc p l then d l else 0 := by
            apply sum_congr rfl
            intro l hl
            by_cases hp : Inc p l
            · simp only [hp, true_and, if_true, d, card_filter]
            · simp [hp]
      _ = ∑ l ∈ L.filter (fun l => Inc p l), d l := by
            rw [sum_filter]
  rw [hcount]
  exact Finset.even_sum _ fun l hl => heven l (mem_filter.mp hl).1

/-- Every exterior row outside the extracted endpoint even configuration
meets an even number of selected exterior rows. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_meetingParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
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
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      ∀ w : W, w ∉ T →
        Even ((T.filter fun u => (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  obtain ⟨T, hT, hlarge, heven⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨T, hT, hlarge, heven, ?_⟩
  intro w hwT
  let Inc : W → P → Prop := fun u y => G.Adj u.1 y.1
  have heven' : ∀ y ∈ (univ : Finset P),
      Even ((T.filter fun u => Inc u y).card) := by
    intro y hy
    exact heven y
  have hlinear : ∀ u ∈ T,
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).card ≤ 1 := by
    intro u huT
    have hwu : w.1 ≠ u.1 := by
      intro h
      apply hwT
      have : w = u := Subtype.ext h
      simpa [this] using huT
    have hwF : w.1 ∉ F := mem_compl.mp w.2
    have huF : u.1 ∉ F := mem_compl.mp u.2
    have hrow := hdesign.2.1 w.1 (by simpa [F] using hwF)
      u.1 (by simpa [F] using huF) hwu
    have himage : ((((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).image
        fun y => y.1)) = row w ∩ row u := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := mem_image.mp hy
        have hyInc := (mem_filter.mp hyy).2
        exact mem_inter.mpr ⟨mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr hyInc.1, yy.2⟩,
          mem_inter.mpr ⟨(G.mem_neighborFinset u.1 yy.1).mpr hyInc.2, yy.2⟩⟩
      · intro hy
        have hyData := mem_inter.mp hy
        let yy : P := ⟨y, (mem_inter.mp hyData.1).2⟩
        exact mem_image.mpr ⟨yy, mem_filter.mpr ⟨mem_univ _, ⟨
          (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hyData.1).1,
          (G.mem_neighborFinset u.1 y).mp (mem_inter.mp hyData.2).1⟩⟩, rfl⟩
    calc
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).card =
          ((((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).image
            fun y => y.1).card) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (row w ∩ row u).card := congrArg card himage
      _ ≤ 1 := by simpa [row] using hrow
  have hparity := linear_even_configuration_meeting_card_even
    Inc T (univ : Finset P) w heven' hlinear
  have hfilters : (T.filter fun u =>
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).Nonempty) =
      T.filter fun u => (row w ∩ row u).Nonempty := by
    ext u
    simp only [mem_filter]
    apply and_congr_right
    intro huT
    constructor
    · rintro ⟨y, hy⟩
      have hyInc := (mem_filter.mp hy).2
      exact ⟨y.1, mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hyInc.1, y.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset u.1 y.1).mpr hyInc.2, y.2⟩⟩⟩
    · rintro ⟨y, hy⟩
      have hyData := mem_inter.mp hy
      let yy : P := ⟨y, (mem_inter.mp hyData.1).2⟩
      exact ⟨yy, mem_filter.mpr ⟨mem_univ _, ⟨
        (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hyData.1).1,
        (G.mem_neighborFinset u.1 y).mp (mem_inter.mp hyData.2).1⟩⟩⟩
  rw [← hfilters]
  exact hparity

end

end Erdos85

#print axioms Erdos85.linear_even_configuration_meeting_card_even
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_meetingParity
