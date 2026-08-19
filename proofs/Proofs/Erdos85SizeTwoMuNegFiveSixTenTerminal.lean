import Proofs.Erdos85SizeTwoMuNegFiveSixTenLongSupport
import Proofs.Erdos85ZModTenMixedSelfIntertwinerExclusion

/-! # Terminal `mu=-5`, `6+10` obstruction -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

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

end

end Erdos85

#print axioms Erdos85.involution_complement_internal_card
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_internalMatching_card_two
