import Proofs.Erdos85PureEndpointExteriorMinimalCircuitEulerian

/-!
# Missing-partner degrees in an even-excess circuit

Two generic lemmas isolate the mechanism for the even larger-circuit branch.
Every point of a selected row has another selected row through it; linearity
makes those partners distinct, giving internal degree at least the uniform
row size.  If the total circuit size is `m+2s` and internal degree is even,
the complementary missing-partner degree is odd and at most `2s-1`.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- In a linear pointwise-even configuration, a selected `m`-uniform row
meets at least `m` other selected rows. -/
theorem linear_evenConfiguration_uniform_le_internalMeeting
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β) (p : α) (m : ℕ)
    (hp : p ∈ T)
    (huniform : (L.filter fun l => Inc p l).card = m)
    (heven : ∀ l ∈ L, Even ((T.filter fun q => Inc q l).card))
    (hlinear : ∀ q ∈ T.erase p, ∀ l ∈ L, ∀ l' ∈ L,
      Inc p l → Inc q l → Inc p l' → Inc q l' → l = l') :
    m ≤ ((T.erase p).filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card := by
  classical
  let B := L.filter fun l => Inc p l
  let M := (T.erase p).filter fun q =>
    (L.filter fun l => Inc p l ∧ Inc q l).Nonempty
  have hexists : ∀ l : {l // l ∈ B}, ∃ q,
      q ∈ T.erase p ∧ Inc q l.1 := by
    intro l
    have hlData := Finset.mem_filter.mp l.2
    let fiber := T.filter fun q => Inc q l.1
    have hpFiber : p ∈ fiber :=
      Finset.mem_filter.mpr ⟨hp, hlData.2⟩
    have hfiberEven : Even fiber.card := heven l.1 hlData.1
    have hfiberPos : 0 < fiber.card := Finset.card_pos.mpr ⟨p, hpFiber⟩
    have hfiberTwo : 2 ≤ fiber.card := by
      obtain ⟨k, hk⟩ := hfiberEven
      omega
    have herasePos : 0 < (fiber.erase p).card := by
      rw [Finset.card_erase_of_mem hpFiber]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp herasePos
    have hqData := Finset.mem_erase.mp hq
    exact ⟨q, Finset.mem_erase.mpr
      ⟨hqData.1, (Finset.mem_filter.mp hqData.2).1⟩,
        (Finset.mem_filter.mp hqData.2).2⟩
  let f : {l // l ∈ B} → {q // q ∈ M} := fun l =>
    let q := Classical.choose (hexists l)
    ⟨q, Finset.mem_filter.mpr ⟨
      (Classical.choose_spec (hexists l)).1,
      ⟨l.1, Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp l.2).1,
        ⟨(Finset.mem_filter.mp l.2).2,
          (Classical.choose_spec (hexists l)).2⟩⟩⟩⟩⟩
  have hfval : ∀ l : {l // l ∈ B},
      Inc (f l).1 l.1 := by
    intro l
    exact (Classical.choose_spec (hexists l)).2
  have hfinj : Function.Injective f := by
    intro l l' hll'
    apply Subtype.ext
    have hqmem : (f l).1 ∈ T.erase p :=
      (Finset.mem_filter.mp (f l).2).1
    have hlData := Finset.mem_filter.mp l.2
    have hl'Data := Finset.mem_filter.mp l'.2
    have hfval' : Inc (f l).1 l'.1 := by
      have := hfval l'
      rw [← hll'] at this
      exact this
    exact hlinear (f l).1 hqmem l.1 hlData.1 l'.1 hl'Data.1
      hlData.2 (hfval l) hl'Data.2 hfval'
  have hcardSub := Fintype.card_le_of_injective f hfinj
  simpa only [Fintype.card_coe, B, M, huniform] using hcardSub

/-- Arithmetic form of the even-excess complement law. -/
theorem evenExcess_missingDegree_odd_le
    (m s t internal missing : ℕ)
    (hs : 0 < s)
    (ht : t = m + 2 * s)
    (hpart : internal + missing = t - 1)
    (hm : Even m) (hi : Even internal)
    (hlower : m ≤ internal) :
    Odd missing ∧ missing ≤ 2 * s - 1 := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hi
  have htpos : 0 < t := by omega
  refine ⟨⟨a + s - b - 1, by omega⟩, ?_⟩
  omega

/-- Endpoint form: in a size-`m+2s` pointwise-even exterior configuration,
every row has an odd number of missing partners, bounded by `2s-1`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_evenExcess_missingDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m s : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m) (hs : 0 < s)
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 * s →
      ∀ w ∈ T,
        let missing := (T.erase w).filter fun u =>
          ¬(row w ∩ row u).Nonempty
        Odd missing.card ∧ missing.card ≤ 2 * s - 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  intro T heven hTcard w hwT
  let meet := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let missing := (T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ((Finset.univ : Finset P).filter fun y => Inc w y).card = m := by
    have himage : (((Finset.univ : Finset P).filter fun y => Inc w y).image
        fun y => y.1) = row w := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr (Finset.mem_filter.mp hyy).2,
          yy.2⟩
      · intro hy
        let yy : P := ⟨y, (Finset.mem_inter.mp hy).2⟩
        exact Finset.mem_image.mpr ⟨yy, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
            (G.mem_neighborFinset w.1 y).mp (Finset.mem_inter.mp hy).1⟩, rfl⟩
    calc
      ((Finset.univ : Finset P).filter fun y => Inc w y).card =
          ((((Finset.univ : Finset P).filter fun y => Inc w y).image
            fun y => y.1).card) :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = (row w).card := congrArg Finset.card himage
      _ = m := hdesign.1 w.1 (by
        simpa [F] using (Finset.mem_compl.mp w.2))
  have hlinear : ∀ u ∈ T.erase w,
      ∀ y ∈ (Finset.univ : Finset P), ∀ y' ∈ (Finset.univ : Finset P),
        Inc w y → Inc u y → Inc w y' → Inc u y' → y = y' := by
    intro u hu y _hy y' _hy' hwy huy hwy' huy'
    apply Subtype.ext
    apply Finset.card_le_one.mp
      (hdesign.2.1 w.1 (by simpa [F] using (Finset.mem_compl.mp w.2))
        u.1 (by simpa [F] using (Finset.mem_compl.mp u.2))
        (fun h => (Finset.ne_of_mem_erase hu) (Subtype.ext h.symm)))
    · exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hwy, y.2⟩,
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u.1 y.1).mpr huy, y.2⟩⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y'.1).mpr hwy', y'.2⟩,
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u.1 y'.1).mpr huy', y'.2⟩⟩
  have hlowerRaw := linear_evenConfiguration_uniform_le_internalMeeting
    Inc T (Finset.univ : Finset P) w m hwT huniform
      (by intro y _hy; exact heven y) hlinear
  have hmeetEq : ((T.erase w).filter fun u =>
      ((Finset.univ : Finset P).filter fun y =>
        Inc w y ∧ Inc u y).Nonempty) = meet := by
    change ((T.erase w).filter fun u =>
      ((Finset.univ : Finset P).filter fun y =>
        Inc w y ∧ Inc u y).Nonempty) =
      (T.erase w).filter fun u => (row w ∩ row u).Nonempty
    ext u
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _hu
    constructor
    · rintro ⟨y, hy⟩
      have hd := (Finset.mem_filter.mp hy).2
      exact ⟨y.1, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hd.1, y.2⟩,
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset u.1 y.1).mpr hd.2, y.2⟩⟩⟩
    · rintro ⟨y, hy⟩
      have hd := Finset.mem_inter.mp hy
      let yy : P := ⟨y, (Finset.mem_inter.mp hd.1).2⟩
      exact ⟨yy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨
        (G.mem_neighborFinset w.1 y).mp (Finset.mem_inter.mp hd.1).1,
        (G.mem_neighborFinset u.1 y).mp (Finset.mem_inter.mp hd.2).1⟩⟩⟩
  rw [hmeetEq] at hlowerRaw
  have hmeetEven :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
        T heven w hwT
  change Even meet.card at hmeetEven
  have hpart : meet.card + missing.card = T.card - 1 := by
    calc
      meet.card + missing.card = (T.erase w).card := by
        simpa [meet, missing] using
          (Finset.card_filter_add_card_filter_not
            (s := T.erase w) (fun u => (row w ∩ row u).Nonempty))
      _ = T.card - 1 := Finset.card_erase_of_mem hwT
  exact evenExcess_missingDegree_odd_le m s T.card meet.card missing.card
    hs hTcard hpart hmEven hmeetEven hlowerRaw

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_uniform_le_internalMeeting
#print axioms Erdos85.evenExcess_missingDegree_odd_le
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_evenExcess_missingDegree
