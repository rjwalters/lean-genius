import Proofs.Erdos85EightEightHighOwnerCnfSemantics

/-! # Counting lemmas for the variable-cross high owner bridge -/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

/-- A four-element Boolean fiber with exactly two true entries satisfies
every positive and negative triple clause on distinct fiber elements. -/
theorem dimacsTripleClausesSatisfied_of_four_exactly_two_counting
    (val : DimacsValuation) (S : Finset Nat)
    (hS : S.card = 4)
    (htrue : (S.filter fun id => val id = true).card = 2)
    {a b c : Nat} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    dimacsClauseSatisfied val [(a : Int), (b : Int), (c : Int)] ∧
      dimacsClauseSatisfied val [-(a : Int), -(b : Int), -(c : Int)] := by
  have hpos : val a = true ∨ val b = true ∨ val c = true := by
    by_contra h
    push_neg at h
    have hsub : S.filter (fun id => val id = true) ⊆ S \ {a, b, c} := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hxa; subst x; exact h.1 hx.2
      · intro hxb; subst x; exact h.2.1 hx.2
      · intro hxc; subst x; exact h.2.2 hx.2
    have hle := Finset.card_le_card hsub
    have hthree : ({a, b, c} : Finset Nat).card = 3 := by
      simp [hab, hac, hbc]
    have hsubset : ({a, b, c} : Finset Nat) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hdiff : (S \ {a, b, c}).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset, hS, hthree]
    omega
  have hneg : val a = false ∨ val b = false ∨ val c = false := by
    by_contra h
    push_neg at h
    have hsubset : ({a, b, c} : Finset Nat) ⊆
        S.filter (fun id => val id = true) := by
      simp only [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_filter]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨ha, by simpa using h.1⟩
      · exact ⟨hb, by simpa using h.2.1⟩
      · exact ⟨hc, by simpa using h.2.2⟩
    have hle := Finset.card_le_card hsubset
    have hthree : ({a, b, c} : Finset Nat).card = 3 := by
      simp [hab, hac, hbc]
    rw [hthree, htrue] at hle
    omega
  constructor
  · rcases hpos with ha' | hb' | hc'
    · exact ⟨(a : Int), by simp, by simp [dimacsLitValue, ha', ha0]⟩
    · exact ⟨(b : Int), by simp, by simp [dimacsLitValue, hb', hb0]⟩
    · exact ⟨(c : Int), by simp, by simp [dimacsLitValue, hc', hc0]⟩
  · rcases hneg with ha' | hb' | hc'
    · exact ⟨-(a : Int), by simp, by simp [dimacsLitValue, ha']⟩
    · exact ⟨-(b : Int), by simp, by simp [dimacsLitValue, hb']⟩
    · exact ⟨-(c : Int), by simp, by simp [dimacsLitValue, hc']⟩

/-- A truth-table row whose two left bits and two right bits have unequal
sums is excluded by its four-literal DIMACS clause whenever the actual
valuation satisfies the balance equation. -/
theorem dimacsIntertwiningMaskClauseSatisfied_of_balance
    (val : DimacsValuation) (a b c d : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (ba bb bc bd : Bool)
    (hbad : ba.toNat + bb.toNat ≠ bc.toNat + bd.toNat)
    (hbalance : (val a).toNat + (val b).toNat =
      (val c).toNat + (val d).toNat) :
    dimacsClauseSatisfied val
      [if ba then -(a : Int) else (a : Int),
       if bb then -(b : Int) else (b : Int),
       if bc then -(c : Int) else (c : Int),
       if bd then -(d : Int) else (d : Int)] := by
  cases hva : val a <;> cases hvb : val b <;>
    cases hvc : val c <;> cases hvd : val d <;>
    cases ba <;> cases bb <;> cases bc <;> cases bd <;>
    simp_all [dimacsClauseSatisfied, dimacsLitValue]

end Erdos85

#print axioms Erdos85.dimacsTripleClausesSatisfied_of_four_exactly_two_counting
#print axioms Erdos85.dimacsIntertwiningMaskClauseSatisfied_of_balance
