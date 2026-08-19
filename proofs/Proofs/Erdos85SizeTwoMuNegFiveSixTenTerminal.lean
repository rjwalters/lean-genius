import Proofs.Erdos85SizeTwoMuNegFiveSixTenLongSupport
import Proofs.Erdos85ZModTenMixedSelfIntertwinerExclusion
import Proofs.Erdos85SizeTwoMuNegThreeSixTenCrossColumnTypes
import Proofs.Erdos85SizeTwoMuNegFiveSixTenMixedExclusion
import Proofs.Erdos85SixTenNormalizedCoordinates

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

/-- At `mu=-5`, same-parity antipodal adjacency in long-cycle coordinates
has at most one target in every row, because each signed shore is a perfect
defect matching. -/
theorem orderSixtyFour_sizeTwo_muNegFive_long_sameParity_antipodal_rightUnique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hsame : ∀ i j, ZModTenEvenOffset (j - i) →
      s (v j).1 = s (v i).1) :
    ∀ i j k,
      (ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1) →
      (ZModTenEvenOffset (k - i) ∧
        (antipodalGraph G).Adj (v i).1 (v k).1) → j = k := by
  classical
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  obtain ⟨fp, fm, hfp, _hfpinv, _hfpne, hfm, _hfminv, _hfmne⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  intro i j k hj hk
  have hDj : D.Adj (v i).1 (v j).1 := Or.inl hj.2
  have hDk : D.Adj (v i).1 (v k).1 := Or.inl hk.2
  have hsj := hsame i j hj.1
  have hsk := hsame i k hk.1
  rcases hs_in (v i).1 (v i).2 with hiNeg | hiPos
  · let xi : Xm := ⟨(v i).1, (v i).2, hiNeg⟩
    let xj : Xm := ⟨(v j).1, (v j).2, hsj.trans hiNeg⟩
    let xk : Xm := ⟨(v k).1, (v k).2, hsk.trans hiNeg⟩
    have hjmate : fm xi = xj := (hfm xi xj).mp hDj
    have hkmate : fm xi = xk := (hfm xi xk).mp hDk
    apply hvinj
    apply Subtype.ext
    exact congrArg (fun x : Xm ↦ x.1) (hjmate.symm.trans hkmate)
  · let xi : Xp := ⟨(v i).1, (v i).2, hiPos⟩
    let xj : Xp := ⟨(v j).1, (v j).2, hsj.trans hiPos⟩
    let xk : Xp := ⟨(v k).1, (v k).2, hsk.trans hiPos⟩
    have hjmate : fp xi = xj := (hfp xi xj).mp hDj
    have hkmate : fp xi = xk := (hfp xi xk).mp hDk
    apply hvinj
    apply Subtype.ext
    exact congrArg (fun x : Xp ↦ x.1) (hjmate.symm.trans hkmate)

/-- The positive vertices in any parametrization of the long component are
exactly the complement, inside the positive shore, of the three positive
short-cycle coordinates. -/
theorem muNegFive_sixTen_positiveLong_image_eq_complement_short
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z ↦ s z.1) 3)
    (v : ZMod 10 → c.supp) (hvrange : Set.range v = b.supp) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Ip := {i : ZMod 10 // s (v i).1 = 1}
    let long : Ip → Xp := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
    let short : ZMod 3 → Xp := fun i ↦
      ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
    Finset.univ.image long = Finset.univ \ Finset.univ.image short := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Ip := {i : ZMod 10 // s (v i).1 = 1}
  let long : Ip → Xp := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
  let short : ZMod 3 → Xp := fun i ↦
    ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
  have hcomp : ∀ x : c.supp, x ∉ a.supp ↔ x ∈ b.supp := by
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
    have hab : a ≠ b := by
      intro hab
      rw [hab] at ha
      omega
    have hAcard : A.card = 6 := by
      have heq : A = a.supp.toFinite.toFinset := by ext x; simp [A]
      rw [heq, ← Set.ncard_eq_toFinset_card, ha]
    have hBcard : B.card = 10 := by
      have heq : B = b.supp.toFinite.toFinset := by ext x; simp [B]
      rw [heq, ← Set.ncard_eq_toFinset_card, hb]
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxa hxb
      exact hab <| (ConnectedComponent.mem_supp_iff a x).mp
        (Finset.mem_filter.mp hxa).2 |>.symm.trans
          ((ConnectedComponent.mem_supp_iff b x).mp
            (Finset.mem_filter.mp hxb).2)
    have hUcard : (Finset.univ : Finset c.supp).card = 16 := by
      rw [Finset.card_univ]
      calc
        Fintype.card c.supp = c.supp.ncard := by
          simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
        _ = 16 := by omega
    have hcover : A ∪ B = (Finset.univ : Finset c.supp) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard, hUcard]
    intro x
    have hxcover : x ∈ A ∪ B := by rw [hcover]; simp
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxcover
    constructor
    · exact fun hxa ↦ hxcover.resolve_left hxa
    · intro hxb hxa
      exact hab <| (ConnectedComponent.mem_supp_iff a x).mp hxa |>.symm.trans
        ((ConnectedComponent.mem_supp_iff b x).mp hxb)
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨i, rfl⟩
    rintro ⟨j, hj⟩
    have hva : v i.1 ∈ a.supp := by
      have hjc : coord.pval j = v i.1 := by
        apply Subtype.ext
        exact congrArg (fun z : Xp ↦ z.1) hj
      rw [← hjc]
      exact (coord.p_mem_sign j).1
    have hvb : v i.1 ∈ b.supp := by
      rw [← hvrange]
      exact ⟨i.1, rfl⟩
    have hab : a = b :=
      ((ConnectedComponent.mem_supp_iff a _).mp hva).symm.trans
        ((ConnectedComponent.mem_supp_iff b _).mp hvb)
    rw [hab] at ha
    omega
  · intro hxshort
    have hxa : (⟨x.1, x.2.1⟩ : c.supp) ∉ a.supp := by
      intro hxa
      obtain ⟨j, hj⟩ := coord.p_surjective
        ⟨x.1, x.2.1⟩ hxa x.2.2
      apply hxshort
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : c.supp ↦ z.1) hj
    have hxb : (⟨x.1, x.2.1⟩ : c.supp) ∈ b.supp := (hcomp _).mp hxa
    rw [← hvrange] at hxb
    obtain ⟨i, hi⟩ := hxb
    let ii : Ip := ⟨i, by simpa [hi] using x.2.2⟩
    refine ⟨ii, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : c.supp ↦ z.1) hi

/-- The negative vertices in a parametrization of the long component are
exactly the complement of the three negative short-cycle coordinates. -/
theorem muNegFive_sixTen_negativeLong_image_eq_complement_short
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z ↦ s z.1) 3)
    (v : ZMod 10 → c.supp) (hvrange : Set.range v = b.supp) :
    let D := secondOrderDefectGraph G
    let Xm := MuNegFiveNegativeShore D c s
    let Im := {i : ZMod 10 // s (v i).1 = -1}
    let longn : Im → Xm := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
    let shortn : ZMod 3 → Xm := fun i ↦
      ⟨(coord.nval i).1, (coord.nval i).2, (coord.n_mem_sign i).2⟩
    Finset.univ.image longn = Finset.univ \ Finset.univ.image shortn := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xm := MuNegFiveNegativeShore D c s
  let Im := {i : ZMod 10 // s (v i).1 = -1}
  let longn : Im → Xm := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
  let shortn : ZMod 3 → Xm := fun i ↦
    ⟨(coord.nval i).1, (coord.nval i).2, (coord.n_mem_sign i).2⟩
  have hcomp := sixTen_internalComponent_complement G c (by omega) a b ha hb
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, rfl⟩
    rintro ⟨j, hj⟩
    have hva : v i.1 ∈ a.supp := by
      have hjc : coord.nval j = v i.1 := by
        apply Subtype.ext
        exact congrArg (fun z : Xm ↦ z.1) hj
      rw [← hjc]
      exact (coord.n_mem_sign j).1
    have hvb : v i.1 ∈ b.supp := by
      rw [← hvrange]
      exact ⟨i.1, rfl⟩
    have hab : a = b :=
      ((ConnectedComponent.mem_supp_iff a _).mp hva).symm.trans
        ((ConnectedComponent.mem_supp_iff b _).mp hvb)
    rw [hab] at ha
    omega
  · intro hxshort
    have hxa : (⟨x.1, x.2.1⟩ : c.supp) ∉ a.supp := by
      intro hxa
      obtain ⟨j, hj⟩ := coord.n_surjective
        ⟨x.1, x.2.1⟩ hxa x.2.2
      apply hxshort
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : c.supp ↦ z.1) hj
    have hxb : (⟨x.1, x.2.1⟩ : c.supp) ∈ b.supp := (hcomp _).mp hxa
    rw [← hvrange] at hxb
    obtain ⟨i, hi⟩ := hxb
    let ii : Im := ⟨i, by simpa [hi] using x.2.2⟩
    refine ⟨ii, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : c.supp ↦ z.1) hi

/-- Transport an internal-matching cardinal through any injective
parametrization of the selected subset. -/
theorem matching_active_source_card_eq
    {X I : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    (f : Equiv.Perm X) (long : I → X) (hinj : Function.Injective long)
    (L : Finset X) (himage : Finset.univ.image long = L) :
    ((Finset.univ : Finset I).filter fun i ↦ ∃ j, f (long i) = long j).card =
      (L.filter fun x ↦ f x ∈ L).card := by
  classical
  apply Finset.card_bij (fun i _ ↦ long i)
  · intro i hi
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    constructor
    · rw [← himage]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rw [← himage]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
  · intro i hi j hj hij
    exact hinj hij
  · intro x hx
    have hxL := (Finset.mem_filter.mp hx).1
    have hfxL := (Finset.mem_filter.mp hx).2
    rw [← himage] at hxL hfxL
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxL
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hfxL
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, ?_⟩⟩, hi⟩
    rw [hi, hj]

/-- Inside a size-two defect component, equal-sign defect adjacency is
precisely antipodal adjacency: the triangle-free summand is an ambient edge
and therefore flips the signed internal eigenline. -/
theorem sizeTwo_equalSign_secondOrderDefect_iff_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (x y : c.supp) (hsame : s y.1 = s x.1) :
    (secondOrderDefectGraph G).Adj x.1 y.1 ↔
      (antipodalGraph G).Adj x.1 y.1 := by
  constructor
  · intro hD
    change ((antipodalGraph G) ⊔ triangleFreeEdgeGraph G).Adj x.1 y.1 at hD
    rcases hD with hanti | htf
    · exact hanti
    · exfalso
      have hG : G.Adj x.1 y.1 :=
        ((mem_triangleFreeNeighbors G x.1 y.1).mp
          ((triangleFreeEdgeGraph_adj G x.1 y.1).mp htf)).1
      have hymem : y.1 ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c x.1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hG,
          (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
      have hflip := (internal_alternation G hfree (by omega) hreg hcard
        c hc s hs_in hs_out hA_in x.2).2 y.1 hymem
      rcases hs_in x.1 x.2 with hxneg | hxpos <;> omega
  · intro hanti
    exact Or.inl hanti

/-- The positive long rows carrying a same-parity antipodal entry are
exactly the positive matching vertices whose mate remains long; hence there
are two of them in the `mu=-5`, `6+10` stratum. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_positive_active_card_two
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
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z ↦ s z.1) 3)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hsame : ∀ i j, ZModTenEvenOffset (j - i) ↔
      s (v j).1 = s (v i).1) :
    ((Finset.univ : Finset (ZMod 10)).filter fun i ↦
      s (v i).1 = 1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Ip := {i : ZMod 10 // s (v i).1 = 1}
  let long : Ip → Xp := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
  let short : ZMod 3 → Xp := fun i ↦
    ⟨(coord.pval i).1, (coord.pval i).2, (coord.p_mem_sign i).2⟩
  let L : Finset Xp := Finset.univ \ Finset.univ.image short
  obtain ⟨fp, _fm, hfp, _hfm, hpcount, _hmcount⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab ha hb coord
  have himage : Finset.univ.image long = L := by
    simpa [D, Xp, Ip, long, short, L] using
      muNegFive_sixTen_positiveLong_image_eq_complement_short
        G c hc s a b ha hb coord v hvrange
  have hlonginj : Function.Injective long := by
    intro i j hij
    apply Subtype.ext
    apply hvinj
    apply Subtype.ext
    exact congrArg (fun x : Xp ↦ x.1) hij
  have hsource :
      ((Finset.univ : Finset Ip).filter fun i ↦
        ∃ j, fp (long i) = long j).card = 2 := by
    rw [matching_active_source_card_eq fp long hlonginj L himage]
    simpa [D, Xp, short, L] using hpcount
  let S := (Finset.univ : Finset (ZMod 10)).filter fun i ↦
    s (v i).1 = 1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
      (antipodalGraph G).Adj (v i).1 (v j).1
  let T := (Finset.univ : Finset Ip).filter fun i ↦
    ∃ j, fp (long i) = long j
  have hcardST : S.card = T.card := by
    apply Finset.card_bij (fun i hi ↦
      (⟨i, (Finset.mem_filter.mp hi).2.1⟩ : Ip))
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hjeven, hjanti⟩ := hi'.2
      let ii : Ip := ⟨i, hi'.1⟩
      have hjsign : s (v j).1 = 1 := (hsame i j).mp hjeven |>.trans hi'.1
      let jj : Ip := ⟨j, hjsign⟩
      have hDef : D.Adj (v i).1 (v j).1 :=
        (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
          G hfree hreg hcard c hc s hs_in hs_out hA_in (v i) (v j)
            ((hsame i j).mp hjeven)).mpr hjanti
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ⟨jj, ?_⟩⟩
      exact (hfp (long ii) (long jj)).mp hDef
    · intro i hi j hj hij
      exact congrArg Subtype.val hij
    · intro i hi
      obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
      have hDef : D.Adj (v i.1).1 (v j.1).1 := (hfp (long i) (long j)).mpr hj
      have hanti := (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
        G hfree hreg hcard c hc s hs_in hs_out hA_in (v i.1) (v j.1)
          (by rw [i.2, j.2])).mp hDef
      refine ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2,
        ⟨j.1, ?_, hanti⟩⟩, ?_⟩
      · exact (hsame i.1 j.1).mpr (by rw [i.2, j.2])
      · rfl
  change S.card = 2
  rw [hcardST]
  exact hsource

/-- Negative-shore mirror of the active-row count. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_negative_active_card_two
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
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (coord : SizeTwoCycleGridCoordinates (G.induce c.supp) a.supp
      (fun z ↦ s z.1) 3)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hsame : ∀ i j, ZModTenEvenOffset (j - i) ↔
      s (v j).1 = s (v i).1) :
    ((Finset.univ : Finset (ZMod 10)).filter fun i ↦
      s (v i).1 = -1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
        (antipodalGraph G).Adj (v i).1 (v j).1).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let Xm := MuNegFiveNegativeShore D c s
  let Im := {i : ZMod 10 // s (v i).1 = -1}
  let longn : Im → Xm := fun i ↦ ⟨(v i.1).1, (v i.1).2, i.2⟩
  let shortn : ZMod 3 → Xm := fun i ↦
    ⟨(coord.nval i).1, (coord.nval i).2, (coord.n_mem_sign i).2⟩
  let L : Finset Xm := Finset.univ \ Finset.univ.image shortn
  obtain ⟨_fp, fm, _hfp, hfm, _hpcount, hmcount⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab ha hb coord
  have himage : Finset.univ.image longn = L := by
    simpa [D, Xm, Im, longn, shortn, L] using
      muNegFive_sixTen_negativeLong_image_eq_complement_short
        G c hc s a b ha hb coord v hvrange
  have hlonginj : Function.Injective longn := by
    intro i j hij
    apply Subtype.ext
    apply hvinj
    apply Subtype.ext
    exact congrArg (fun x : Xm ↦ x.1) hij
  have hsource :
      ((Finset.univ : Finset Im).filter fun i ↦
        ∃ j, fm (longn i) = longn j).card = 2 := by
    rw [matching_active_source_card_eq fm longn hlonginj L himage]
    simpa [D, Xm, shortn, L] using hmcount
  let S := (Finset.univ : Finset (ZMod 10)).filter fun i ↦
    s (v i).1 = -1 ∧ ∃ j, ZModTenEvenOffset (j - i) ∧
      (antipodalGraph G).Adj (v i).1 (v j).1
  let T := (Finset.univ : Finset Im).filter fun i ↦
    ∃ j, fm (longn i) = longn j
  have hcardST : S.card = T.card := by
    apply Finset.card_bij (fun i hi ↦
      (⟨i, (Finset.mem_filter.mp hi).2.1⟩ : Im))
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hjeven, hjanti⟩ := hi'.2
      let ii : Im := ⟨i, hi'.1⟩
      have hjsign : s (v j).1 = -1 := (hsame i j).mp hjeven |>.trans hi'.1
      let jj : Im := ⟨j, hjsign⟩
      have hDef : D.Adj (v i).1 (v j).1 :=
        (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
          G hfree hreg hcard c hc s hs_in hs_out hA_in (v i) (v j)
            ((hsame i j).mp hjeven)).mpr hjanti
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ⟨jj, ?_⟩⟩
      exact (hfm (longn ii) (longn jj)).mp hDef
    · intro i hi j hj hij
      exact congrArg Subtype.val hij
    · intro i hi
      obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
      have hDef : D.Adj (v i.1).1 (v j.1).1 :=
        (hfm (longn i) (longn j)).mpr hj
      have hanti := (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
        G hfree hreg hcard c hc s hs_in hs_out hA_in (v i.1) (v j.1)
          (by rw [i.2, j.2])).mp hDef
      refine ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2,
        ⟨j.1, ?_, hanti⟩⟩, ?_⟩
      · exact (hsame i.1 j.1).mpr (by rw [i.2, j.2])
      · rfl
  change S.card = 2
  rw [hcardST]
  exact hsource

/-- The `mu=-5`, `C6+C10` internal-cycle stratum is impossible. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_false
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
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) : False := by
  classical
  let H := G.induce c.supp
  have hdeg : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) x
  have hflip : ∀ ⦃x y : c.supp⦄, H.Adj x y → s x.1 = -s y.1 := by
    intro x y hxy
    have hymem : y.1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
    have h := (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in x.2).2 y.1 hymem
    omega
  let t : c.supp → ℤ := fun z ↦ s z.1
  obtain ⟨coord⟩ := exists_sizeTwoCycleGridCoordinates H hdeg 3
    (by omega) a (by omega) t (fun z _ ↦ hs_in z.1 z.2) (by
      intro x y hxy
      exact hflip hxy)
  obtain ⟨cv⟩ := exists_normalizedTenShoreCoordinates
    H hdeg b hb t (fun z _ ↦ hs_in z.1 z.2) (by
      intro x y hxy
      exact hflip hxy)
  have hsame : ∀ i j, ZModTenEvenOffset (j - i) ↔
      s (cv.u j).1 = s (cv.u i).1 := by
    intro i j
    exact (zmodTen_alternating_sign_eq_iff_evenOffset_sub
      (fun z ↦ s (cv.u z).1) (fun z ↦ by
        have hHedge : H.Adj (cv.u z) (cv.u (z + 1)) := by
          rw [← H.mem_neighborFinset, cv.neighbor]
          simp
        have := hflip hHedge
        omega) (fun z ↦ hs_in _ (cv.u z).2) i j).symm
  have hbtf := orderSixtyFour_sizeTwo_muNegFive_sixTen_long_allTriangleFree
    G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab ha hb
  have huniq :=
    orderSixtyFour_sizeTwo_muNegFive_long_sameParity_antipodal_rightUnique
      G hfree hreg hcard c hc s hs_out hs_in hH hD cv.u cv.injective
        (fun i j hij ↦ (hsame i j).mp hij)
  have hpos := orderSixtyFour_sizeTwo_muNegFive_sixTen_positive_active_card_two
    G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab ha hb
      coord cv.u cv.injective cv.range hsame
  have hneg := orderSixtyFour_sizeTwo_muNegFive_sixTen_negative_active_card_two
    G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab ha hb
      coord cv.u cv.injective cv.range hsame
  exact orderSixtyFour_sizeTwo_sixTen_long_allTf_false_of_signed_active_two
    G hfree hreg hcard c hc s b hbtf cv.u cv.injective cv.range cv.neighbor
      (fun i ↦ hs_in _ (cv.u i).2) huniq hpos hneg

end

end Erdos85

#print axioms Erdos85.involution_complement_internal_card
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
#print axioms Erdos85.orderSixtyFour_sizeTwo_sixTen_long_allTf_antipodal_sameParity_ne_four
#print axioms Erdos85.card_filter_product_eq_card_filter_exists_of_rightUnique
#print axioms Erdos85.orderSixtyFour_sizeTwo_sixTen_long_allTf_false_of_signed_active_two
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_long_sameParity_antipodal_rightUnique
#print axioms Erdos85.muNegFive_sixTen_positiveLong_image_eq_complement_short
#print axioms Erdos85.matching_active_source_card_eq
#print axioms Erdos85.sizeTwo_equalSign_secondOrderDefect_iff_antipodal
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_positive_active_card_two
#print axioms Erdos85.muNegFive_sixTen_negativeLong_image_eq_complement_short
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_negative_active_card_two
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_false
