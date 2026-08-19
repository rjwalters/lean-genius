import Proofs.Erdos85SizeTwoMuNegOneExtremeStructure
import Proofs.Erdos85NegativeSizeTwoExtremeRowBalance
import Proofs.Erdos85BinarySquareMuThreeExteriorGridEmbedding
import Proofs.Erdos85BranchDeficitSymmetry

/-! # Biregular same-sign owner incidence at `mu = -1` -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- At `mu = -1`, the eight positive component vertices and eight positive
extreme owners form a 2-by-2 incidence layer; symmetrically on the negative
side.  There are no component-to-opposite-extreme incidences. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extremeIncidence_twoRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-1 : ℤ) * s z) :
    let Xp := MuNegOnePositiveShore (secondOrderDefectGraph G) c s
    let Xm := MuNegOneNegativeShore (secondOrderDefectGraph G) c s
    let Ep := MuNegOnePositiveExteriorFiber G s
    let Em := MuNegOneNegativeExteriorFiber G s
    Fintype.card Xp = 8 ∧ Fintype.card Xm = 8 ∧
    (∀ x : Xp,
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card = 2 ∧
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card = 0) ∧
    (∀ x : Xm,
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card = 0 ∧
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card = 2) ∧
    (∀ z : Ep,
      ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1).card = 2) ∧
    ∀ z : Em,
      ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1).card = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegOnePositiveShore D c s
  let Xm := MuNegOneNegativeShore D c s
  let Ep := MuNegOnePositiveExteriorFiber G s
  let Em := MuNegOneNegativeExteriorFiber G s
  let w : V → ℤ := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sc := (Finset.univ : Finset V).filter fun x => D.connectedComponentMk x = c
  have hScMem : ∀ x, x ∈ Sc ↔ x ∈ c.supp := by
    intro x
    simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ConnectedComponent.mem_supp_iff c x).symm
  have hScCard : Sc.card = 16 := by
    have hSc : Sc = c.supp.toFinset := by
      ext x
      simp only [Sc, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_toFinset]
      exact ConnectedComponent.mem_supp_iff c x
    rw [hSc, ← Set.ncard_eq_toFinset_card', hc]
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-1) hs_out hs_in hH hD
  have hsignSc : ∀ x ∈ Sc, s x = -1 ∨ s x = 1 := by
    intro x hx
    exact hs_in x ((hScMem x).mp hx)
  have hsignCards := signedFinset_zeroSum_filter_cards Sc s hsignSc
    P.componentSum_eq_zero
  have hplusCard : (Sc.filter fun x => s x = 1).card = 8 := by
    omega
  have hminusCard : (Sc.filter fun x => s x = -1).card = 8 := by
    omega
  have hXpCard : Fintype.card Xp = 8 := by
    rw [Fintype.card_subtype]
    change ((Finset.univ : Finset V).filter fun x => x ∈ c.supp ∧ s x = 1).card = 8
    rw [show (Finset.univ.filter fun x : V => x ∈ c.supp ∧ s x = 1) =
        Sc.filter fun x => s x = 1 by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hScMem]]
    exact hplusCard
  have hXmCard : Fintype.card Xm = 8 := by
    rw [Fintype.card_subtype]
    change ((Finset.univ : Finset V).filter fun x => x ∈ c.supp ∧ s x = -1).card = 8
    rw [show (Finset.univ.filter fun x : V => x ∈ c.supp ∧ s x = -1) =
        Sc.filter fun x => s x = -1 by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hScMem]]
    exact hminusCard
  have howner := orderSixtyFour_sizeTwo_muNegOne_extremeOwner_profile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hEpCard : Fintype.card Ep = 8 := howner.1
  have hEmCard : Fintype.card Em = 8 := howner.2.1
  have hrow := orderSixtyFour_sizeTwo_negative_extreme_rowBalance_of_local
    G hfree hreg hcard c hc s (-1) (Or.inl rfl) hs_out hs_in hH hD
  let p := fun x => (((G.neighborFinset x).filter
    (fun y => y ∉ c.supp)).filter fun y => w y = 2).card
  let n := fun x => (((G.neighborFinset x).filter
    (fun y => y ∉ c.supp)).filter fun y => w y = -2).card
  have hpEq (x : Xp) : p x.1 =
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card := by
    apply Finset.card_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : Ep))
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz'.1).1⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact congrArg Subtype.val heq
    · intro z hz
      have hzAdj := (Finset.mem_filter.mp hz).2
      refine ⟨z.1, Finset.mem_filter.mpr ⟨?_, z.2⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzAdj,
        (howner.2.2.1 z).1⟩
  have hnEq (x : Xp) : n x.1 =
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card := by
    apply Finset.card_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : Em))
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz'.1).1⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact congrArg Subtype.val heq
    · intro z hz
      have hzAdj := (Finset.mem_filter.mp hz).2
      refine ⟨z.1, Finset.mem_filter.mpr ⟨?_, z.2⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzAdj,
        (howner.2.2.2 z).1⟩
  have hpRow (x : Xp) : p x.1 = n x.1 + 2 := by
    have hx := hrow x.1 x.2.1
    rcases hx with hx | hx
    · simpa [p, n, w] using hx.2.resolve_right (fun h => by omega)
    · exact (by omega : False).elim
  have hpsum : ∑ x : Xp, p x.1 = 16 := by
    simp_rw [hpEq]
    rw [sum_card_filter_relation_comm (Finset.univ : Finset Xp)
      (Finset.univ : Finset Ep) (fun x z => G.Adj x.1 z.1)]
    have hcol : ∀ z : Ep,
        ((Finset.univ : Finset Xp).filter fun x => G.Adj x.1 z.1).card = 2 :=
      fun z => (howner.2.2.1 z).2.1
    simp_rw [hcol]
    simp [hEpCard]
  have hnsum : ∑ x : Xp, n x.1 = 0 := by
    have hsumEq : (∑ x : Xp, p x.1) = (∑ x : Xp, n x.1) + 16 := by
      simp_rw [hpRow, Finset.sum_add_distrib]
      simp [hXpCard]
    omega
  have hnzero : ∀ x : Xp, n x.1 = 0 := by
    intro x
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
      (by simpa using hnsum) x (Finset.mem_univ _)
  have hpositiveRows : ∀ x : Xp,
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card = 2 ∧
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card = 0 := by
    intro x
    constructor
    · rw [← hpEq, hpRow, hnzero]
    · rw [← hnEq, hnzero]
  have hmEq (x : Xm) : n x.1 =
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card := by
    apply Finset.card_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : Em))
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz'.1).1⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact congrArg Subtype.val heq
    · intro z hz
      have hzAdj := (Finset.mem_filter.mp hz).2
      refine ⟨z.1, Finset.mem_filter.mpr ⟨?_, z.2⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzAdj,
        (howner.2.2.2 z).1⟩
  have mpEq (x : Xm) : p x.1 =
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card := by
    apply Finset.card_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : Ep))
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hz'.1).1⟩
    · intro z₁ hz₁ z₂ hz₂ heq
      exact congrArg Subtype.val heq
    · intro z hz
      have hzAdj := (Finset.mem_filter.mp hz).2
      refine ⟨z.1, Finset.mem_filter.mpr ⟨?_, z.2⟩, rfl⟩
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hzAdj,
        (howner.2.2.1 z).1⟩
  have hnRow (x : Xm) : n x.1 = p x.1 + 2 := by
    have hx := hrow x.1 x.2.1
    rcases hx with hx | hx
    · exact (by omega : False).elim
    · simpa [p, n, w] using hx.2.resolve_right (fun h => by omega)
  have hnsum' : ∑ x : Xm, n x.1 = 16 := by
    simp_rw [hmEq]
    rw [sum_card_filter_relation_comm (Finset.univ : Finset Xm)
      (Finset.univ : Finset Em) (fun x z => G.Adj x.1 z.1)]
    have hcol : ∀ z : Em,
        ((Finset.univ : Finset Xm).filter fun x => G.Adj x.1 z.1).card = 2 :=
      fun z => (howner.2.2.2 z).2.2
    simp_rw [hcol]
    simp [hEmCard]
  have hpsum' : ∑ x : Xm, p x.1 = 0 := by
    have hsumEq : (∑ x : Xm, n x.1) = (∑ x : Xm, p x.1) + 16 := by
      simp_rw [hnRow, Finset.sum_add_distrib]
      simp [hXmCard]
    omega
  have hpzero : ∀ x : Xm, p x.1 = 0 := by
    intro x
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
      (by simpa using hpsum') x (Finset.mem_univ _)
  have hnegativeRows : ∀ x : Xm,
      ((Finset.univ : Finset Ep).filter fun z => G.Adj x.1 z.1).card = 0 ∧
      ((Finset.univ : Finset Em).filter fun z => G.Adj x.1 z.1).card = 2 := by
    intro x
    constructor
    · rw [← mpEq, hpzero]
    · rw [← hmEq, hnRow, hpzero]
  exact ⟨hXpCard, hXmCard, hpositiveRows, hnegativeRows,
    fun z => (howner.2.2.1 z).2.1,
    fun z => (howner.2.2.2 z).2.2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extremeIncidence_twoRegular
