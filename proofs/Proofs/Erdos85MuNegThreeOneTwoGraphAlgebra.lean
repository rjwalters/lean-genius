import Proofs.Erdos85MuNegThreeOneTwoGraphRealization
import Proofs.Erdos85MuNegOneOneFourZModCountEnumeration
import Proofs.Erdos85MuNegThreeExplicitParameters

/-!
# Algebra adapter for the `mu=-3`, `(k,r)=(1,2)` graph endpoint

This file converts the two explicit cross-block ledgers and the oriented
same-sign matching into the three defect-shape fields of the checked owner
CNF semantics.  Owner service is deliberately left to the geometric tiling
adapter.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem list_countP_eq_filter_card'
    {A : Type*} [DecidableEq A] (l : List A) (p : A → Bool)
    (hl : l.Nodup) :
    l.countP p = (l.toFinset.filter fun x ↦ p x = true).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := (List.nodup_cons.mp hl).1
      have htail := (List.nodup_cons.mp hl).2
      have hat : a ∉ l.toFinset := by simpa using ha
      by_cases hp : p a = true
      · rw [List.countP_cons_of_pos hp, ih htail, List.toFinset_cons,
          Finset.filter_insert]
        simp [hp, hat]
      · rw [List.countP_cons_of_neg hp, ih htail, List.toFinset_cons,
          Finset.filter_insert]
        simp [hp, hat]

private theorem natEight_filter_countP_eq_univ_val_filter_card
    (p q : Nat → Bool) :
    ((List.range 8).filter p).countP q =
      ((Finset.univ : Finset (ZMod 8)).filter fun z ↦
        p z.val = true ∧ q z.val = true).card := by
  rw [list_countP_eq_filter_card' _ _ (List.nodup_range.filter _)]
  apply Finset.card_bij (fun (n : Nat) _ ↦ (n : ZMod 8))
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    rw [List.mem_toFinset, List.mem_filter] at hn
    have hn8 := List.mem_range.mp hn.1.1
    simpa [ZMod.val_natCast_of_lt hn8] using
      (show p n = true ∧ q n = true from ⟨hn.1.2, hn.2⟩)
  · intro a ha b hb hab
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_filter] at ha hb
    have hal : a < 8 := List.mem_range.mp ha.1.1
    have hbl : b < 8 := List.mem_range.mp hb.1.1
    have := congrArg ZMod.val hab
    simp only [ZMod.val_natCast_of_lt hal, ZMod.val_natCast_of_lt hbl] at this
    exact this
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_filter]
    exact ⟨⟨List.mem_range.mpr z.val_lt, hz.2.1⟩, hz.2.2⟩

private theorem crossDefect_count_row_of_ledger
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 2)
    (D : Nat → Nat → Bool)
    (hD : ∀ i j, i < 8 → j < 8 →
      D i j = decide (M (i : ZMod 8) (j : ZMod 8) = 1))
    (hpar : ∀ i j : Nat, i < 8 → j < 8 →
      (g (j : ZMod 8) = f (i : ZMod 8) ↔ i % 2 = j % 2))
    (i : Nat) (hi : i < 8) :
    (((List.range 8).filter fun j => !(i % 2 == j % 2)).countP
      fun j => D i j) = 1 := by
  rw [natEight_filter_countP_eq_univ_val_filter_card]
  have htotal := L.cross_row (i : ZMod 8)
  have hsame := L.cross_same (i : ZMod 8)
  let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    M (i : ZMod 8) j = 1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j : ZMod 8 ↦ g j = f (i : ZMod 8)) (s := A)
  have hyes : (A.filter fun j ↦ g j = f (i : ZMod 8)).card = 1 := by
    rw [show (A.filter fun j ↦ g j = f (i : ZMod 8)) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          g j = f (i : ZMod 8) ∧ M (i : ZMod 8) j = 1) by
      ext j
      simp [A, and_comm]]
    simpa using hsame
  have hno : (A.filter fun j ↦ ¬ g j = f (i : ZMod 8)).card = 1 := by
    have hA : A.card = 2 := by simpa [A] using htotal
    rw [hA, hyes] at hpart
    omega
  rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (!(i % 2 == j.val % 2)) = true ∧ D i j.val = true) =
      (A.filter fun j ↦ ¬ g j = f (i : ZMod 8)) by
    ext j
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hj : j.val < 8 := j.val_lt
    have hp := hpar i j.val hi hj
    have hd := hD i j.val hi hj
    simp only [ZMod.natCast_zmod_val] at hp hd
    rw [hd]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
    constructor
    · rintro ⟨hne, hedge⟩
      exact ⟨hedge, fun hs ↦ hne (hp.mp hs)⟩
    · rintro ⟨hedge, hne⟩
      exact ⟨fun hs ↦ hne (hp.mpr hs), hedge⟩,
    hno]

private theorem zmod_forward_eq_phi
    (t : ZMod 8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (j : ZMod 8) = t + (i : ZMod 8) ↔
      j = muNegThreePhi true t.val i := by
  fin_cases t <;> interval_cases i <;> interval_cases j <;> decide

private theorem zmod_reverse_eq_phi
    (t : ZMod 8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (j : ZMod 8) = t - (i : ZMod 8) ↔
      j = muNegThreePhi false t.val i := by
  fin_cases t <;> interval_cases i <;> interval_cases j <;> decide

/-- The explicit `(1,2)` ledgers and oriented same-sign matching discharge
all three algebra fields of the graph residual.  The parity hypothesis is
the harmless cyclic reindexing which aligns the two alternating sign lines.
-/
theorem muNegThreeOneTwo_graph_defectShape
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 1 2)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 1 2)
    (D : Nat → Nat → Bool)
    (hD₁ : ∀ i j, i < 8 → j < 8 →
      D i j = decide (M₁ (i : ZMod 8) (j : ZMod 8) = 1))
    (hD₂ : ∀ i j, i < 8 → j < 8 →
      D i j = decide (M₂ (j : ZMod 8) (i : ZMod 8) = 1))
    (hpar : ∀ i j : Nat, i < 8 → j < 8 →
      (g (j : ZMod 8) = f (i : ZMod 8) ↔ i % 2 = j % 2))
    (horient : ∃ t : ZMod 8,
      (∀ i j, (g j = f i ∧ M₁ i j = 1) ↔ j = t + i) ∨
      (∀ i j, (g j = f i ∧ M₁ i j = 1) ↔ j = t - i)) :
    ∃ fwd phase,
      (∀ i j, i < 8 → j < 8 → i % 2 == j % 2 →
        D i j = (j == muNegThreePhi fwd phase i)) ∧
      (∀ i, i < 8 →
        (((List.range 8).filter fun j => !(i % 2 == j % 2)).countP
          fun j => D i j) = 1) ∧
      (∀ j, j < 8 →
        (((List.range 8).filter fun i => !(i % 2 == j % 2)).countP
          fun i => D i j) = 1) := by
  obtain ⟨t, hfwd | hrev⟩ := horient
  · refine ⟨true, t.val, ?_, ?_, ?_⟩
    · intro i j hi hj hsame
      rw [hD₁ i j hi hj]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, beq_iff_eq]
      have hp : g (j : ZMod 8) = f (i : ZMod 8) :=
        (hpar i j hi hj).mpr (beq_iff_eq.mp hsame)
      rw [← zmod_forward_eq_phi t hi hj, ← hfwd]
      simp [hp]
    · exact crossDefect_count_row_of_ledger L₁ D hD₁ hpar
    · intro j hj
      simpa [Bool.beq_comm] using
        (crossDefect_count_row_of_ledger L₂ (fun j i ↦ D i j)
          (fun j i hj hi ↦ hD₂ i j hi hj)
          (fun j i hj hi ↦ by
            constructor
            · intro h
              exact ((hpar i j hi hj).mp h.symm).symm
            · intro h
              exact ((hpar i j hi hj).mpr h.symm).symm) j hj)
  · refine ⟨false, t.val, ?_, ?_, ?_⟩
    · intro i j hi hj hsame
      rw [hD₁ i j hi hj]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, beq_iff_eq]
      have hp : g (j : ZMod 8) = f (i : ZMod 8) :=
        (hpar i j hi hj).mpr (beq_iff_eq.mp hsame)
      rw [← zmod_reverse_eq_phi t hi hj, ← hrev]
      simp [hp]
    · exact crossDefect_count_row_of_ledger L₁ D hD₁ hpar
    · intro j hj
      simpa [Bool.beq_comm] using
        (crossDefect_count_row_of_ledger L₂ (fun j i ↦ D i j)
          (fun j i hj hi ↦ hD₂ i j hi hj)
          (fun j i hj hi ↦ by
            constructor
            · intro h
              exact ((hpar i j hi hj).mp h.symm).symm
            · intro h
              exact ((hpar i j hi hj).mpr h.symm).symm) j hj)

end

end Erdos85

#print axioms Erdos85.muNegThreeOneTwo_graph_defectShape
