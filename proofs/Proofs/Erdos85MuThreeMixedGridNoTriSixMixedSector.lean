import Proofs.Erdos85MuThreeMixedGridCommonForeignRowsCard

/-!
# No three-by-three triangle block in a mixed sector

This is the pure hole-counting obstruction behind the mixed `C10 + C6`
exclusion.  If a three-column triangle block has its `H`-edges disjoint from
the hole factor `K`, while every column outside the block is an `H ⊆ K`
triangle-free column, then column two-regularity traps the two `K`-holes of
each triangle row inside the block.  Together with its two disjoint `H`
neighbors this would require four columns inside a three-element set.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two shores of a connected component of a bipartite two-factor have
equal cardinality. -/
theorem relationTwoRegular_component_shore_cards_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H : X → Y → Prop) [DecidableRel H] (hreg : RelationTwoRegular H)
    (c : (relationBipartiteGraph H).ConnectedComponent) :
    {x : X | Sum.inl x ∈ c.supp}.ncard =
      {y : Y | Sum.inr y ∈ c.supp}.ncard := by
  classical
  let L : Finset X := Finset.univ.filter fun x => Sum.inl x ∈ c.supp
  let R : Finset Y := Finset.univ.filter fun y => Sum.inr y ∈ c.supp
  have hrow (x : X) (hx : x ∈ L) :
      (R.filter fun y => H x y).card = 2 := by
    have hrestrict : R.filter (fun y => H x y) =
        (Finset.univ : Finset Y).filter fun y => H x y := by
      ext y
      constructor
      · intro hy
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro hy
        have hxC : Sum.inl x ∈ c.supp := (Finset.mem_filter.mp hx).2
        have hyH : H x y := (Finset.mem_filter.mp hy).2
        have hyC : Sum.inr y ∈ c.supp := by
          apply (ConnectedComponent.mem_supp_congr_adj c
            (show (relationBipartiteGraph H).Adj (Sum.inl x) (Sum.inr y)
              from hyH)).mp
          exact hxC
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC⟩, hyH⟩
    rw [hrestrict]
    exact hreg.1 x
  have hcolumn (y : Y) (hy : y ∈ R) :
      (L.filter fun x => H x y).card = 2 := by
    have hrestrict : L.filter (fun x => H x y) =
        (Finset.univ : Finset X).filter fun x => H x y := by
      ext x
      constructor
      · intro hx
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      · intro hx
        have hyC : Sum.inr y ∈ c.supp := (Finset.mem_filter.mp hy).2
        have hxH : H x y := (Finset.mem_filter.mp hx).2
        have hxC : Sum.inl x ∈ c.supp := by
          apply (ConnectedComponent.mem_supp_congr_adj c
            (show (relationBipartiteGraph H).Adj (Sum.inr y) (Sum.inl x)
              from hxH)).mp
          exact hyC
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxC⟩, hxH⟩
    rw [hrestrict]
    exact hreg.2 y
  have hleft : (∑ x ∈ L, (R.filter fun y => H x y).card) = 2 * L.card := by
    calc
      (∑ x ∈ L, (R.filter fun y => H x y).card) = ∑ _x ∈ L, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hrow x hx
      _ = 2 * L.card := by simp [mul_comm]
  have hright : (∑ y ∈ R, (L.filter fun x => H x y).card) = 2 * R.card := by
    calc
      (∑ y ∈ R, (L.filter fun x => H x y).card) = ∑ _y ∈ R, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hcolumn y hy
      _ = 2 * R.card := by simp [mul_comm]
  have hdouble :
      (∑ x ∈ L, (R.filter fun y => H x y).card) =
        ∑ y ∈ R, (L.filter fun x => H x y).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hcards : L.card = R.card := by omega
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card]
  simpa [L, R] using hcards

/-- A six-vertex component of a bipartite two-factor has three vertices on
each shore. -/
theorem relationTwoRegular_sixComponent_shore_cards_eq_three
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H : X → Y → Prop) [DecidableRel H] (hreg : RelationTwoRegular H)
    (c : (relationBipartiteGraph H).ConnectedComponent)
    (hc : c.supp.ncard = 6) :
    {x : X | Sum.inl x ∈ c.supp}.ncard = 3 ∧
      {y : Y | Sum.inr y ∈ c.supp}.ncard = 3 := by
  classical
  let L : Finset X := Finset.univ.filter fun x => Sum.inl x ∈ c.supp
  let R : Finset Y := Finset.univ.filter fun y => Sum.inr y ∈ c.supp
  let e : {z : X ⊕ Y // z ∈ c.supp} ≃
      {x : X // Sum.inl x ∈ c.supp} ⊕
        {y : Y // Sum.inr y ∈ c.supp} :=
    { toFun := fun z => match z with
        | ⟨Sum.inl x, h⟩ => Sum.inl ⟨x, h⟩
        | ⟨Sum.inr y, h⟩ => Sum.inr ⟨y, h⟩
      invFun := fun z => match z with
        | Sum.inl x => ⟨Sum.inl x.1, x.2⟩
        | Sum.inr y => ⟨Sum.inr y.1, y.2⟩
      left_inv := by
        intro z
        rcases z with ⟨x | y, h⟩ <;> rfl
      right_inv := by
        intro z
        rcases z with x | y <;> rfl }
  have hLRset := relationTwoRegular_component_shore_cards_eq H hreg c
  have hLR : L.card = R.card := by
    rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card] at hLRset
    simpa [L, R] using hLRset
  have hLcard : Fintype.card {x : X // Sum.inl x ∈ c.supp} = L.card := by
    rw [Fintype.card_subtype]
  have hRcard : Fintype.card {y : Y // Sum.inr y ∈ c.supp} = R.card := by
    rw [Fintype.card_subtype]
  have htotal : L.card + R.card = 6 := by
    have he := Fintype.card_congr e
    rw [Fintype.card_sum, hLcard, hRcard] at he
    have hc' : Fintype.card {z : X ⊕ Y // z ∈ c.supp} = 6 := by
      calc
        Fintype.card {z : X ⊕ Y // z ∈ c.supp} =
            Nat.card {z : X ⊕ Y // z ∈ c.supp} := by
              simp [Nat.card_eq_fintype_card]
        _ = c.supp.ncard := Nat.card_coe_set_eq _
        _ = 6 := hc
    omega
  have hresult : L.card = 3 ∧ R.card = 3 := by omega
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card]
  simpa [L, R] using hresult

/-- An `H \ K` block whose outside columns all satisfy `H ⊆ K` has at
least four columns.  This is the abstract-code form of “a triangle-sector
cycle has length at least eight in a genuinely mixed sector.” -/
theorem MuThreeMixedGridCode.four_le_card_notK_block_of_outside_all_K
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (S : Finset Y) (x : X)
    (hHinside : ∀ y, H x y → y ∈ S)
    (hHnotK : ∀ y, H x y → ¬ K x y)
    (houtside : ∀ y, y ∉ S → ∀ z, H z y → K z y) : 4 ≤ S.card := by
  classical
  have hKinside : ∀ y, K x y → y ∈ S := by
    intro y hKxy
    by_contra hyS
    let A : Finset X := Finset.univ.filter fun z => H z y
    let B : Finset X := Finset.univ.filter fun z => K z y
    have hAB : A ⊆ B := by
      intro z hz
      have hzH : H z y := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, houtside y hyS z hzH⟩
    have hAcard : A.card = 2 := by
      simpa [A] using code.H_twoRegular.2 y
    have hBcard : B.card = 2 := by
      simpa [B] using code.K_twoRegular.2 y
    have hABeq : A = B :=
      Finset.eq_of_subset_of_card_le hAB (by omega)
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKxy⟩
    have hxA : x ∈ A := hABeq.symm ▸ hxB
    have hxH : H x y := (Finset.mem_filter.mp hxA).2
    exact hHnotK y hxH hKxy
  let RH : Finset Y := Finset.univ.filter fun y => H x y
  let RK : Finset Y := Finset.univ.filter fun y => K x y
  have hRHcard : RH.card = 2 := by
    simpa [RH] using code.H_twoRegular.1 x
  have hRKcard : RK.card = 2 := by
    simpa [RK] using code.K_twoRegular.1 x
  have hRHsub : RH ⊆ S := by
    intro y hy
    exact hHinside y (Finset.mem_filter.mp hy).2
  have hRKsub : RK ⊆ S := by
    intro y hy
    exact hKinside y (Finset.mem_filter.mp hy).2
  have hdisj : Disjoint RH RK := by
    rw [Finset.disjoint_left]
    intro y hyH hyK
    exact hHnotK y (Finset.mem_filter.mp hyH).2
      (Finset.mem_filter.mp hyK).2
  have hunionSub : RH ∪ RK ⊆ S := Finset.union_subset hRHsub hRKsub
  have hunionCard : (RH ∪ RK).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hRHcard, hRKcard]
  have hle := Finset.card_le_card hunionSub
  rwa [hunionCard] at hle

/-- In particular, a three-column `H \ K` block cannot coexist with
`H ⊆ K` on every outside column. -/
theorem MuThreeMixedGridCode.no_threeColumn_notK_block_of_outside_all_K
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (S : Finset Y) (hScard : S.card = 3) (x : X)
    (hHinside : ∀ y, H x y → y ∈ S)
    (hHnotK : ∀ y, H x y → ¬ K x y)
    (houtside : ∀ y, y ∉ S → ∀ z, H z y → K z y) : False := by
  have hle := code.four_le_card_notK_block_of_outside_all_K H K C
    S x hHinside hHnotK houtside
  omega

/-- Component-level mixed-sector wrapper: a six-vertex `H`-component cannot
be the `H \ K` component when every column outside it lies in `H ⊆ K`.
No certificate coordinates are required; shore cardinality follows by
double-counting the bipartite two-factor. -/
theorem MuThreeMixedGridCode.no_sixComponent_notK_of_outside_all_K
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (c : (relationBipartiteGraph H).ConnectedComponent)
    (hc : c.supp.ncard = 6)
    (hcomponentNotK : ∀ x y, H x y → Sum.inl x ∈ c.supp → ¬ K x y)
    (houtsideAllK : ∀ y, Sum.inr y ∉ c.supp → ∀ z, H z y → K z y) : False := by
  classical
  let L : Finset X := Finset.univ.filter fun x => Sum.inl x ∈ c.supp
  let S : Finset Y := Finset.univ.filter fun y => Sum.inr y ∈ c.supp
  have hshores := relationTwoRegular_sixComponent_shore_cards_eq_three
    H code.H_twoRegular c hc
  have hLcard : L.card = 3 := by
    have h := hshores.1
    rw [Set.ncard_eq_toFinset_card] at h
    simpa [L] using h
  have hScard : S.card = 3 := by
    have h := hshores.2
    rw [Set.ncard_eq_toFinset_card] at h
    simpa [S] using h
  obtain ⟨x, hxL⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
  have hxC : Sum.inl x ∈ c.supp := (Finset.mem_filter.mp hxL).2
  apply code.no_threeColumn_notK_block_of_outside_all_K H K C S hScard x
  · intro y hHxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      apply (ConnectedComponent.mem_supp_congr_adj c
        (show (relationBipartiteGraph H).Adj (Sum.inl x) (Sum.inr y)
          from hHxy)).mp
      exact hxC⟩
  · exact fun y hHxy => hcomponentNotK x y hHxy hxC
  · intro y hyS
    apply houtsideAllK y
    intro hyC
    exact hyS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC⟩)

end

end Erdos85

#print axioms
  Erdos85.relationTwoRegular_component_shore_cards_eq
#print axioms
  Erdos85.relationTwoRegular_sixComponent_shore_cards_eq_three
#print axioms
  Erdos85.MuThreeMixedGridCode.four_le_card_notK_block_of_outside_all_K
#print axioms
  Erdos85.MuThreeMixedGridCode.no_threeColumn_notK_block_of_outside_all_K
#print axioms
  Erdos85.MuThreeMixedGridCode.no_sixComponent_notK_of_outside_all_K
