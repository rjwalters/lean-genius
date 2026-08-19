import Proofs.Erdos85SizeTwoMuNegFiveSixTenLongSupport
import Proofs.Erdos85ZModTenMixedSelfIntertwinerExclusion

/-! # Terminal `mu=-5`, `6+10` obstruction -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite relation with at most one target in every source fiber has as
many pairs as sources whose fiber is inhabited. -/
theorem card_filter_product_eq_card_filter_exists_of_rightUnique
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (R : X → Y → Prop) [DecidableRel R]
    (huniq : ∀ x y z, R x y → R x z → y = z) :
    ((Finset.univ : Finset (X × Y)).filter fun p ↦ R p.1 p.2).card =
      ((Finset.univ : Finset X).filter fun x ↦ ∃ y, R x y).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ p.1)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, ⟨p.2, hp.2⟩⟩
  · intro p hp q hq heq
    apply Prod.ext heq
    exact huniq p.1 p.2 q.2
      (Finset.mem_filter.mp hp).2
      (by simpa [heq] using (Finset.mem_filter.mp hq).2)
  · intro x hx
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨(x, y), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩

/-- If an involution sends every point of `A` outside `A`, the points outside
`A` whose mates also remain outside number `|X|-2|A|`. -/
theorem involution_complement_internal_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : Equiv.Perm X) (hinv : ∀ x, f (f x) = x)
    (A : Finset X) (hcross : ∀ x ∈ A, f x ∉ A) :
    ((Finset.univ \ A).filter fun x => f x ∈ Finset.univ \ A).card =
      Fintype.card X - 2 * A.card := by
  classical
  let fA := A.image f
  have hfAcard : fA.card = A.card := by
    exact Finset.card_image_of_injective A f.injective
  have hdisj : Disjoint A fA := by
    rw [Finset.disjoint_left]
    intro x hxA hxfA
    obtain ⟨a, haA, hax⟩ := Finset.mem_image.mp hxfA
    subst x
    exact hcross a haA hxA
  have heq : (Finset.univ \ A).filter (fun x => f x ∈ Finset.univ \ A) =
      Finset.univ \ (A ∪ fA) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_union, not_or, fA]
    constructor
    · rintro ⟨hxA, hfxA⟩
      refine ⟨hxA, ?_⟩
      intro hxfA
      obtain ⟨a, haA, hax⟩ := Finset.mem_image.mp hxfA
      apply hfxA
      have : f x = a := by
        calc
          f x = f (f a) := congrArg f hax.symm
          _ = a := hinv a
      simpa [this] using haA
    · rintro ⟨hxA, hxfA⟩
      refine ⟨hxA, ?_⟩
      intro hfxA
      apply hxfA
      apply Finset.mem_image.mpr
      exact ⟨f x, hfxA, hinv x⟩
  rw [heq, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr (Finset.subset_univ _),
    Finset.card_union_of_disjoint hdisj, hfAcard, Finset.card_univ]
  omega

/-- On each sign shore, exactly two long-cycle vertices have their same-sign
defect mate also on the long cycle. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z => s z.1) 3) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      (∀ x y, D.Adj x.1 y.1 ↔ fp x = y) ∧
      (∀ x y, D.Adj x.1 y.1 ↔ fm x = y) ∧
      (((Finset.univ \ Finset.univ.image (fun i : ZMod 3 =>
          (⟨(coord.pval i).1, (coord.pval i).2,
            (coord.p_mem_sign i).2⟩ : Xp))).filter fun x =>
        fp x ∈ Finset.univ \ Finset.univ.image (fun i : ZMod 3 =>
          (⟨(coord.pval i).1, (coord.pval i).2,
            (coord.p_mem_sign i).2⟩ : Xp))).card = 2) ∧
      (((Finset.univ \ Finset.univ.image (fun j : ZMod 3 =>
          (⟨(coord.nval j).1, (coord.nval j).2,
            (coord.n_mem_sign j).2⟩ : Xm))).filter fun y =>
        fm y ∈ Finset.univ \ Finset.univ.image (fun j : ZMod 3 =>
          (⟨(coord.nval j).1, (coord.nval j).2,
            (coord.n_mem_sign j).2⟩ : Xm))).card = 2) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  obtain ⟨fp, fm, hfp, hfpinv, _hfpne, hfm, hfminv, _hfmne⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcross := orderSixtyFour_sizeTwo_muNegFive_sixTen_short_sameSignDefect_cross
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab ha hb
  obtain ⟨fp', fm', hfp', hfm', hcrossp', hcrossm'⟩ := hcross
  have hfp_eq : fp = fp' := by
    ext x
    have hd : D.Adj x.1 (fp x).1 := (hfp x (fp x)).2 rfl
    exact congrArg Subtype.val ((hfp' x (fp x)).1 hd).symm
  have hfm_eq : fm = fm' := by
    ext y
    have hd : D.Adj y.1 (fm y).1 := (hfm y (fm y)).2 rfl
    exact congrArg Subtype.val ((hfm' y (fm y)).1 hd).symm
  let Ap : Finset Xp := Finset.univ.image fun i : ZMod 3 =>
    ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
  let Am : Finset Xm := Finset.univ.image fun j : ZMod 3 =>
    ⟨(coord.nval j).1, (coord.nval j).2, (coord.n_mem_sign j).2⟩
  have hApcard : Ap.card = 3 := by
    rw [Finset.card_image_of_injective]
    · decide
    · intro i j hij
      apply coord.p_injective
      apply Subtype.ext
      exact congrArg (fun z : Xp => z.1) hij
  have hAmcard : Am.card = 3 := by
    rw [Finset.card_image_of_injective]
    · decide
    · intro i j hij
      apply coord.n_injective
      apply Subtype.ext
      exact congrArg (fun z : Xm => z.1) hij
  have hApcross : ∀ x ∈ Ap, fp x ∉ Ap := by
    intro x hx hfx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hfx
    have hxa : (⟨x.1, x.2.1⟩ : c.supp) ∈ a.supp := by
      rw [← hi]
      exact (coord.p_mem_sign i).1
    have hfb := hcrossp' x hxa
    rw [← hfp_eq] at hfb
    have hfa : (⟨(fp x).1, (fp x).2.1⟩ : c.supp) ∈ a.supp := by
      rw [← hj]
      exact (coord.p_mem_sign j).1
    apply hab
    exact ((ConnectedComponent.mem_supp_iff a _).mp hfa).symm.trans
      ((ConnectedComponent.mem_supp_iff b _).mp hfb)
  have hAmcross : ∀ y ∈ Am, fm y ∉ Am := by
    intro y hy hfy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hfy
    have hya : (⟨y.1, y.2.1⟩ : c.supp) ∈ a.supp := by
      rw [← hi]
      exact (coord.n_mem_sign i).1
    have hfb := hcrossm' y hya
    rw [← hfm_eq] at hfb
    have hfa : (⟨(fm y).1, (fm y).2.1⟩ : c.supp) ∈ a.supp := by
      rw [← hj]
      exact (coord.n_mem_sign j).1
    apply hab
    exact ((ConnectedComponent.mem_supp_iff a _).mp hfa).symm.trans
      ((ConnectedComponent.mem_supp_iff b _).mp hfb)
  have hp := involution_complement_internal_card fp hfpinv Ap hApcross
  have hm := involution_complement_internal_card fm hfminv Am hAmcross
  have hXp : Fintype.card Xp = 8 := by
    rw [Fintype.card_subtype]
    simpa [Xp, ConnectedComponent.mem_supp_iff] using
      (orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
      G hfree hreg hcard c hc s hs_out hs_in hH hD).1
  have hXm : Fintype.card Xm = 8 := by
    rw [Fintype.card_subtype]
    simpa [Xm, ConnectedComponent.mem_supp_iff] using
      (orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
      G hfree hreg hcard c hc s hs_out hs_in hH hD).2.1
  rw [hXp, hApcard] at hp
  rw [hXm, hAmcard] at hm
  refine ⟨fp, fm, hfp, hfm, ?_, ?_⟩
  · simpa [Ap] using hp
  · simpa [Am] using hm

/-- On an all-triangle-free long `C10`, the antipodal residual is a
self-intertwiner of the cycle.  Hence it cannot have exactly four directed
same-parity entries. -/
theorem orderSixtyFour_sizeTwo_sixTen_long_allTf_antipodal_sameParity_ne_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (b : (G.induce c.supp).ConnectedComponent)
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ((Finset.univ : Finset (ZMod 10 × ZMod 10)).filter fun p ↦
      ZModTenEvenOffset (p.2 - p.1) ∧
        (antipodalGraph G).Adj (v p.1).1 (v p.2).1).card ≠ 4 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 10) (ZMod 10) ℤ := fun i j ↦
    (antipodalGraph G).adjMatrix ℤ (v i).1 (v j).1
  have hvb : ∀ i, v i ∈ b.supp := by
    intro i
    rw [← hvrange]
    exact ⟨i, rfl⟩
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have htf_iff_H : ∀ i j,
      (triangleFreeEdgeGraph G).Adj (v i).1 (v j).1 ↔ H.Adj (v i) (v j) := by
    intro i j
    constructor
    · intro htf
      exact ((mem_triangleFreeNeighbors G (v i).1 (v j).1).mp
        ((triangleFreeEdgeGraph_adj G (v i).1 (v j).1).mp htf)).1
    · intro hH
      exact sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree
        (v i) (v j) hH (hbtf (v i) (hvb i))
  have hentry : ∀ i j,
      K.adjMatrix ℤ (v i) (v j) =
        M i j + H.adjMatrix ℤ (v i) (v j) := by
    intro i j
    have hKiff : K.Adj (v i) (v j) ↔
        (antipodalGraph G).Adj (v i).1 (v j).1 ∨ H.Adj (v i) (v j) := by
      change ((antipodalGraph G) ⊔ triangleFreeEdgeGraph G).Adj
        (v i).1 (v j).1 ↔ _
      simpa only [SimpleGraph.sup_adj, htf_iff_H i j]
    have hdisj : (antipodalGraph G).Adj (v i).1 (v j).1 →
        ¬ H.Adj (v i) (v j) := by
      intro hanti hH
      exact ((mem_antipodalNeighbors G (v i).1 (v j).1).mp hanti).2.1 hH
    simp only [SimpleGraph.adjMatrix_apply, M]
    by_cases ha : (antipodalGraph G).Adj (v i).1 (v j).1
    · rw [if_pos ((hKiff).2 (Or.inl ha)), if_pos ha, if_neg (hdisj ha)]
      norm_num
    · by_cases hH : H.Adj (v i) (v j)
      · rw [if_pos ((hKiff).2 (Or.inr hH)), if_neg ha, if_pos hH]
        norm_num
      · rw [if_neg (fun hK ↦ (hKiff.mp hK).elim ha hH), if_neg ha, if_neg hH]
        norm_num
  obtain ⟨_hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcommKH : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hvpair : ∀ z : ZMod 10, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    exact (by decide : (2 : ZMod 10) ≠ 0) (by
      calc
        (2 : ZMod 10) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp)
  have hinterK := entry_cycleIntertwine_of_adjMatrix_comm K H v v
    (1 : ZMod 10) (1 : ZMod 10) hcommKH hv hv hvpair hvpair
  have hinterH := entry_cycleIntertwine_of_adjMatrix_comm H H v v
    (1 : ZMod 10) (1 : ZMod 10) rfl hv hv hvpair hvpair
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    intro i j
    have hK := hinterK i j
    have hH := hinterH i j
    rw [hentry, hentry, hentry, hentry] at hK
    linear_combination hK - hH
  have hdiag : ∀ z, M z z = 0 := by
    intro z
    simp [M, SimpleGraph.adjMatrix_apply]
  have hne := zmodTen_selfIntertwiner_sameParity_directed_card_ne_four
    M hdiag hinter
  simpa [M, SimpleGraph.adjMatrix_apply] using hne

/-- If exactly two positive and two negative long rows carry a same-parity
antipodal entry, uniqueness of the same-parity entry contradicts the C10
self-intertwiner obstruction. -/
theorem orderSixtyFour_sizeTwo_sixTen_long_allTf_false_of_signed_active_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (b : (G.induce c.supp).ConnectedComponent)
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hsign : ∀ i, s (v i).1 = -1 ∨ s (v i).1 = 1)
    (huniq : ∀ i j k,
      (ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1) →
      (ZModTenEvenOffset (k - i) ∧
        (antipodalGraph G).Adj (v i).1 (v k).1) → j = k)
    (hpos : ((Finset.univ : Finset (ZMod 10)).filter fun i ↦
      s (v i).1 = 1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1).card = 2)
    (hneg : ((Finset.univ : Finset (ZMod 10)).filter fun i ↦
      s (v i).1 = -1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1).card = 2) : False := by
  classical
  let R : ZMod 10 → ZMod 10 → Prop := fun i j ↦
    ZModTenEvenOffset (j - i) ∧
      (antipodalGraph G).Adj (v i).1 (v j).1
  let A := (Finset.univ : Finset (ZMod 10)).filter fun i ↦
    s (v i).1 = 1 ∧ ∃ j, R i j
  let B := (Finset.univ : Finset (ZMod 10)).filter fun i ↦
    s (v i).1 = -1 ∧ ∃ j, R i j
  let T := (Finset.univ : Finset (ZMod 10)).filter fun i ↦ ∃ j, R i j
  have hAB : A ∪ B = T := by
    ext i
    simp only [A, B, T, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨_, hi⟩ | ⟨_, hi⟩) <;> exact hi
    · intro hi
      rcases hsign i with hiNeg | hiPos
      · exact Or.inr ⟨hiNeg, hi⟩
      · exact Or.inl ⟨hiPos, hi⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hp := (Finset.mem_filter.mp hiA).2.1
    have hn := (Finset.mem_filter.mp hiB).2.1
    omega
  have hTcard : T.card = 4 := by
    rw [← hAB, Finset.card_union_of_disjoint hdisj]
    have hAcard : A.card = 2 := hpos
    have hBcard : B.card = 2 := hneg
    omega
  have hpairs := card_filter_product_eq_card_filter_exists_of_rightUnique
    R (by simpa [R] using huniq)
  have hfour :
      ((Finset.univ : Finset (ZMod 10 × ZMod 10)).filter fun p ↦
        ZModTenEvenOffset (p.2 - p.1) ∧
          (antipodalGraph G).Adj (v p.1).1 (v p.2).1).card = 4 := by
    simpa [R, T, hTcard] using hpairs.trans hTcard
  exact (orderSixtyFour_sizeTwo_sixTen_long_allTf_antipodal_sameParity_ne_four
    G hfree hreg hcard c hc b hbtf v hvinj hvrange hv) hfour

end

end Erdos85

#print axioms Erdos85.involution_complement_internal_card
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
#print axioms Erdos85.orderSixtyFour_sizeTwo_sixTen_long_allTf_antipodal_sameParity_ne_four
#print axioms Erdos85.card_filter_product_eq_card_filter_exists_of_rightUnique
#print axioms Erdos85.orderSixtyFour_sizeTwo_sixTen_long_allTf_false_of_signed_active_two
