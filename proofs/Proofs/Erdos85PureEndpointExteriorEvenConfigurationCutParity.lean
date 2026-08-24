import Proofs.Erdos85PureEndpointExteriorEvenConfigurationIntersectionParity
import Proofs.Erdos85PureEndpointExteriorRowIntersectionDegree

/-!
# Per-row cut parity of an even exterior configuration
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- Inside an even linear configuration, the number of other selected blocks
meeting a selected `m`-uniform block has parity `m`. -/
theorem linear_even_configuration_internal_meeting_add_uniform_even
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β) (p : α) (m : ℕ)
    (hp : p ∈ T)
    (huniform : (L.filter fun l => Inc p l).card = m)
    (heven : ∀ l ∈ L, Even ((T.filter fun q => Inc q l).card))
    (hlinear : ∀ q ∈ T.erase p,
      (L.filter fun l => Inc p l ∧ Inc q l).card ≤ 1) :
    Even (m + ((T.erase p).filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card) := by
  classical
  let block := L.filter fun l => Inc p l
  let d : β → ℕ := fun l => (T.filter fun q => Inc q l).card
  let inter : α → Finset β := fun q =>
    L.filter fun l => Inc p l ∧ Inc q l
  let meet := (T.erase p).filter fun q => (inter q).Nonempty
  have hIeven : Even (∑ l ∈ block, d l) := by
    exact Finset.even_sum _ fun l hl => heven l (mem_filter.mp hl).1
  have hdouble : (∑ l ∈ block, d l) = ∑ q ∈ T, (inter q).card := by
    calc
      (∑ l ∈ block, d l) = ∑ l ∈ L,
          if Inc p l then ∑ q ∈ T, if Inc q l then 1 else 0 else 0 := by
            rw [show block = L.filter fun l => Inc p l by rfl, sum_filter]
            apply sum_congr rfl
            intro l hl
            by_cases hpl : Inc p l
            · simp only [hpl, if_true, d, card_filter]
            · simp [hpl]
      _ = ∑ l ∈ L, ∑ q ∈ T,
          if Inc p l ∧ Inc q l then 1 else 0 := by
            apply sum_congr rfl
            intro l hl
            by_cases hpl : Inc p l
            · simp [hpl]
            · simp [hpl]
      _ = ∑ q ∈ T, ∑ l ∈ L,
          if Inc p l ∧ Inc q l then 1 else 0 := by rw [sum_comm]
      _ = ∑ q ∈ T, (inter q).card := by
            apply sum_congr rfl
            intro q hq
            simp only [inter, card_filter]
  have hself : (inter p).card = m := by
    have heq : inter p = block := by
      ext l
      simp [inter, block]
    rw [heq]
    exact huniform
  have herase : ∑ q ∈ T, (inter q).card =
      (inter p).card + ∑ q ∈ T.erase p, (inter q).card := by
    rw [add_comm, sum_erase_add _ _ hp]
  have hindicator : ∀ q ∈ T.erase p,
      (inter q).card = if (inter q).Nonempty then 1 else 0 := by
    intro q hq
    by_cases hn : (inter q).Nonempty
    · simp only [hn, if_true]
      exact Nat.le_antisymm (hlinear q hq) (card_pos.mpr hn)
    · simp only [hn, if_false]
      exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
  have hother : (∑ q ∈ T.erase p, (inter q).card) = meet.card := by
    calc
      (∑ q ∈ T.erase p, (inter q).card) =
          ∑ q ∈ T.erase p, if (inter q).Nonempty then 1 else 0 := by
            apply sum_congr rfl
            intro q hq
            exact hindicator q hq
      _ = meet.card := by simp [meet]
  have hEq : (∑ l ∈ block, d l) = m + meet.card := by
    rw [hdouble, herase, hself, hother]
  simpa [meet, inter] using hEq ▸ hIeven

/-- Endpoint form of the selected-row parity law: each selected exterior row
meets, inside the configuration, a number of other selected rows congruent to
`m` modulo two. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_internalParity
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
      ∀ w ∈ T, Even (m + ((T.erase w).filter fun u =>
        (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  obtain ⟨T, hT, hlarge, heven, _houtParity⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_meetingParity
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨T, hT, hlarge, heven, ?_⟩
  intro w hwT
  have huniform : ((univ : Finset P).filter fun y => Inc w y).card = m := by
    have himage : (((univ : Finset P).filter fun y => Inc w y).image
        fun y => y.1) = row w := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := mem_image.mp hy
        exact mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr (mem_filter.mp hyy).2, yy.2⟩
      · intro hy
        let yy : P := ⟨y, (mem_inter.mp hy).2⟩
        exact mem_image.mpr ⟨yy, mem_filter.mpr ⟨mem_univ _,
          (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hy).1⟩, rfl⟩
    have hwF : w.1 ∉ F := mem_compl.mp w.2
    calc
      ((univ : Finset P).filter fun y => Inc w y).card =
          ((((univ : Finset P).filter fun y => Inc w y).image
            fun y => y.1).card) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (row w).card := congrArg card himage
      _ = m := hdesign.1 w.1 (by simpa [F, row] using hwF)
  have hlinear : ∀ u ∈ T.erase w,
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).card ≤ 1 := by
    intro u hu
    have hwu : w.1 ≠ u.1 := by
      intro h
      exact (ne_of_mem_erase hu) (Subtype.ext h).symm
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
  have hinter := linear_even_configuration_internal_meeting_add_uniform_even
    Inc T (univ : Finset P) w m hwT huniform
    (by intro y _hy; exact heven y) hlinear
  have hfilters : ((T.erase w).filter fun u =>
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).Nonempty) =
      (T.erase w).filter fun u => (row w ∩ row u).Nonempty := by
    ext u
    simp only [mem_filter]
    apply and_congr_right
    intro hu
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
  exact hinter

/-- Pointwise cut law for the extracted circuit: the number of exterior rows
outside `T` meeting a selected row has the same parity as that row's number
of full-center defect holes. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_cutParity
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
      ∀ w ∈ T,
        Even (((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card +
          (((univ : Finset W) \ T).filter fun u =>
            (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  obtain ⟨T, hT, hlarge, heven, hinternal⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_internalParity
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdegree := c4Free_binarySquare_pureEndpoint_exterior_rowIntersection_degree
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨T, hT, hlarge, heven, ?_⟩
  intro w hwT
  let I := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let C := ((univ : Finset W) \ T).filter fun u =>
    (row w ∩ row u).Nonempty
  let A := ((univ : Finset W).erase w).filter fun u =>
    (row w ∩ row u).Nonempty
  let H := ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card
  have hpart : A = I ∪ C := by
    ext u
    simp only [A, I, C, mem_filter, mem_erase, mem_univ, true_and,
      mem_union, mem_sdiff]
    constructor
    · rintro ⟨huw, hmeet⟩
      by_cases huT : u ∈ T
      · exact Or.inl ⟨⟨huw.1, huT⟩, hmeet⟩
      · exact Or.inr ⟨huT, hmeet⟩
    · rintro (⟨⟨huw, _huT⟩, hmeet⟩ | ⟨_huNotT, hmeet⟩)
      · exact ⟨⟨huw, trivial⟩, hmeet⟩
      · exact ⟨⟨(fun huwEq => _huNotT (huwEq ▸ hwT)), trivial⟩, hmeet⟩
  have hdis : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro u huI huC
    exact (mem_sdiff.mp (mem_filter.mp huC).1).2
      (mem_erase.mp (mem_filter.mp huI).1).2
  have hcardPart : A.card = I.card + C.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have hAcard : A.card = m * (q - 3) + H := by
    have hwR : w.1 ∈ (Fᶜ : Finset V) := by simpa [F] using w.2
    have hdegData := hdegree w.1 hwR
    let R := (Fᶜ : Finset V)
    let B : V → Finset V := fun v => G.neighborFinset v ∩ S
    let meetV := (R.erase w.1).filter fun v =>
      ((B w.1) ∩ (B v)).Nonempty
    have himage : A.image (fun u => u.1) = meetV := by
      ext v
      constructor
      · intro hv
        obtain ⟨u, huA, rfl⟩ := mem_image.mp hv
        have huData := mem_filter.mp huA
        have huwVal : u.1 ≠ w.1 := fun h =>
          (mem_erase.mp huData.1).1 (Subtype.ext h)
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨huwVal, u.2⟩,
          by simpa [row, B] using huData.2⟩
      · intro hv
        have hvData := mem_filter.mp hv
        have hvR := (mem_erase.mp hvData.1).2
        let u : W := ⟨v, hvR⟩
        apply mem_image.mpr
        refine ⟨u, mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_univ _⟩, ?_⟩, rfl⟩
        · intro huv
          exact (mem_erase.mp hvData.1).1 (congrArg Subtype.val huv)
        · simpa [row, B] using hvData.2
    calc
      A.card = (A.image fun u => u.1).card :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = meetV.card := congrArg card himage
      _ = m * (q - 3) + H := by
        rw [hdegData.1, hdegData.2]
  have hInternalEven : Even (m + I.card) := by
    simpa [I, row] using hinternal w hwT
  have hqEven : Even (q - 2) := by
    refine ⟨m - 1, ?_⟩
    omega
  have hbaseEven : Even (m * (q - 3) + m) := by
    have hbaseEq : m * (q - 3) + m = m * (q - 2) := by
      have hsub : (q - 3) + 1 = q - 2 := by omega
      calc
        m * (q - 3) + m = m * ((q - 3) + 1) := by ring
        _ = m * (q - 2) := by rw [hsub]
    rw [hbaseEq]
    exact hqEven.mul_left m
  have hsumEven : Even ((H + C.card) + (m + I.card)) := by
    have heq : (H + C.card) + (m + I.card) =
        (H + H) + (m * (q - 3) + m) := by
      omega
    rw [heq]
    exact (show Even (H + H) from ⟨H, rfl⟩).add hbaseEven
  change Even (H + C.card)
  exact (Nat.even_add.mp hsumEven).mpr hInternalEven

end

end Erdos85

#print axioms Erdos85.linear_even_configuration_internal_meeting_add_uniform_even
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_internalParity
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_cutParity
