import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourExterior

/-!
# Signed cross-exterior split in the `mu=-1`, `(k,r)=(1,4)` cell

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The variable-cross owner CNF uses exterior rather than defect bits.  At
parameter four, each cross defect row and column has four entries, exactly
two of the same eigenline sign.  Since each opposite shore contains four
vertices of either sign, complementing the defect block leaves exactly two
same-sign and two opposite-sign exterior entries.  This file isolates that
finite-cardinality conversion from the graph adapter and the DIMACS
numbering.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Complementing a four-subset of an eight-set which meets a four-subset in
two points leaves two points on either side of the four-subset. -/
theorem card_complement_same_two_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (D S : α → Prop) [DecidablePred D] [DecidablePred S]
    (hall : Fintype.card α = 8)
    (hS : ((Finset.univ : Finset α).filter S).card = 4)
    (hD : ((Finset.univ : Finset α).filter D).card = 4)
    (hDS : ((Finset.univ : Finset α).filter fun x ↦ D x ∧ S x).card = 2) :
    ((Finset.univ : Finset α).filter fun x ↦ ¬ D x ∧ S x).card = 2 ∧
      ((Finset.univ : Finset α).filter fun x ↦ ¬ D x ∧ ¬ S x).card = 2 := by
  classical
  let U : Finset α := Finset.univ
  let DS := U.filter fun x ↦ D x ∧ S x
  let DnS := U.filter fun x ↦ D x ∧ ¬ S x
  let nDS := U.filter fun x ↦ ¬ D x ∧ S x
  let nDnS := U.filter fun x ↦ ¬ D x ∧ ¬ S x
  have hDsplit : DS.card + DnS.card = 4 := by
    rw [← hD]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := U.filter D) (p := S)
    simpa [DS, DnS, U, Finset.filter_filter, and_assoc] using hpartition
  have hSsplit : DS.card + nDS.card = 4 := by
    rw [← hS]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := U.filter S) (p := D)
    simpa [DS, nDS, U, Finset.filter_filter, and_left_comm,
      and_comm, and_assoc] using hpartition
  have hnotScard : (U.filter fun x ↦ ¬ S x).card = 4 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := U) (p := S)
    have hcardU : U.card = 8 := by simpa [U] using hall
    rw [hS, hcardU] at hpartition
    omega
  have hnotSsplit : DnS.card + nDnS.card = 4 := by
    rw [← hnotScard]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := U.filter fun x ↦ ¬ S x) (p := D)
    simpa [DnS, nDnS, U, Finset.filter_filter, and_left_comm,
      and_comm, and_assoc] using hpartition
  change nDS.card = 2 ∧ nDnS.card = 2
  change DS.card = 2 at hDS
  omega

/-- Every sign fiber of an alternating `±1` line on `ZMod 8` has four
elements.  This discharges the two `hsame` hypotheses of the cross-complement
socket directly from the eigenline alternation laws. -/
theorem zmodEight_alternating_sign_fiber_card_four
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (a : ℤ) (ha : a = -1 ∨ a = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ f i = a).card = 4 := by
  classical
  obtain ⟨x, hx : f x = a⟩ : ∃ x : ZMod 8, f x = a := by
    have hflip0 := hflip 0
    rcases hsign 0 with h0 | h0 <;> rcases ha with ha | ha
    · exact ⟨0, by simpa [h0, ha]⟩
    · refine ⟨1, ?_⟩
      norm_num [h0, ha] at hflip0 ⊢
      exact hflip0
    · refine ⟨1, ?_⟩
      norm_num [h0, ha] at hflip0 ⊢
      exact hflip0
    · exact ⟨0, by simpa [h0, ha]⟩
  have heq : ∀ i, f i = a ↔ ZModEightEvenOffset (i - x) := by
    intro i
    rw [← hx]
    exact zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip x i
  have hcard :
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ZModEightEvenOffset (i - x)).card = 4 := by
    exact (by decide : ∀ x : ZMod 8,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ZModEightEvenOffset (i - x)).card = 4) x
  simpa only [heq] using hcard

/-- Two alternating `±1` shores automatically have four vertices matching
the sign of any fixed vertex on the opposite shore, in either direction. -/
theorem zmodEight_two_alternating_sign_same_card_four
    (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j) :
    (∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      sv j = su i).card = 4) ∧
    (∀ j, ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      su i = sv j).card = 4) := by
  constructor
  · intro i
    exact zmodEight_alternating_sign_fiber_card_four
      sv hsv hflipv (su i) (hsu i)
  · intro j
    exact zmodEight_alternating_sign_fiber_card_four
      su hsu hflipu (sv j) (hsv j)

/-- Row-and-column form used by the `(−1,1,4)` variable-cross owner model.
The exterior predicate is pointwise the complement of the defect predicate;
the conclusion records the exact signed `2+2` split in both directions. -/
theorem zmodEight_crossExterior_two_two_of_complement
    (D R : ZMod 8 → ZMod 8 → Prop)
    [DecidableRel D] [DecidableRel R]
    (su sv : ZMod 8 → ℤ)
    (hcomp : ∀ i j, R i j ↔ ¬ D i j)
    (hsameRow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ sv j = su i).card = 4)
    (hsameCol : ∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ su i = sv j).card = 4)
    (hDrow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ D i j).card = 4)
    (hDcol : ∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ D i j).card = 4)
    (hDsameRow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        D i j ∧ sv j = su i).card = 2)
    (hDsameCol : ∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        D i j ∧ su i = sv j).card = 2) :
    (∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        R i j ∧ sv j = su i).card = 2 ∧
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        R i j ∧ sv j ≠ su i).card = 2) ∧
    (∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        R i j ∧ su i = sv j).card = 2 ∧
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        R i j ∧ su i ≠ sv j).card = 2) := by
  classical
  constructor
  · intro i
    have h := card_complement_same_two_two
      (fun j ↦ D i j) (fun j ↦ sv j = su i)
      (by decide) (hsameRow i) (hDrow i) (hDsameRow i)
    simpa only [hcomp] using h
  · intro j
    have h := card_complement_same_two_two
      (fun i ↦ D i j) (fun i ↦ su i = sv j)
      (by decide) (hsameCol j) (hDcol j) (hDsameCol j)
    simpa only [hcomp] using h

/-- Graph-facing adapter for the signed cross split.  It combines the
distinct-cycle exterior/complement theorem with alternating-sign fiber
cardinality, so a cell consumer only has to provide the four coordinate
defect-cardinality ledgers. -/
theorem sizeTwo_distinctCycle_crossExterior_signed_two_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (s : V → ℤ)
    (hsu : ∀ i, s (u i).1 = -1 ∨ s (u i).1 = 1)
    (hsv : ∀ j, s (v j).1 = -1 ∨ s (v j).1 = 1)
    (hflipu : ∀ i, s (u (i + 1)).1 = -s (u i).1)
    (hflipv : ∀ j, s (v (j + 1)).1 = -s (v j).1)
    (hDrow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)).card = 4)
    (hDcol : ∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)).card = 4)
    (hDsameRow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) ∧
          s (v j).1 = s (u i).1).card = 2)
    (hDsameCol : ∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) ∧
          s (u i).1 = s (v j).1).card = 2) :
    (∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j) ∧
          s (v j).1 = s (u i).1).card = 2 ∧
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j) ∧
          s (v j).1 ≠ s (u i).1).card = 2) ∧
    (∀ j,
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j) ∧
          s (u i).1 = s (v j).1).card = 2 ∧
      ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j) ∧
          s (u i).1 ≠ s (v j).1).card = 2) := by
  let D : ZMod 8 → ZMod 8 → Prop := fun i j ↦
    ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j)
  let R : ZMod 8 → ZMod 8 → Prop := fun i j ↦
    (exteriorPairGraph G c.supp).Adj (u i) (v j)
  have hcomp : ∀ i j, R i j ↔ ¬ D i j :=
    sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
      G hfree c a b hab u v hurange hvrange
  have hsame := zmodEight_two_alternating_sign_same_card_four
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
      hsu hsv hflipu hflipv
  exact zmodEight_crossExterior_two_two_of_complement
    D R (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
      hcomp hsame.1 hsame.2 hDrow hDcol hDsameRow hDsameCol

end

end Erdos85

#print axioms Erdos85.card_complement_same_two_two
#print axioms Erdos85.zmodEight_alternating_sign_fiber_card_four
#print axioms Erdos85.zmodEight_two_alternating_sign_same_card_four
#print axioms Erdos85.zmodEight_crossExterior_two_two_of_complement
#print axioms Erdos85.sizeTwo_distinctCycle_crossExterior_signed_two_two
