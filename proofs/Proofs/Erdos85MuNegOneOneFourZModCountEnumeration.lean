import Proofs.Erdos85MuNegOneOneFourCrossCountTransport

/-!
# Nat/ZMod-8 count enumeration for the `mu=-1`, `(1,4)` bridge

Node: outline F.3, graph-to-finite-semantics instantiation (3c-i).

The graph geometry states its cross counts over `Finset.univ : Finset
(ZMod 8)`, while the checked CNF semantics enumerates coordinates with
`List.range 8`.  This file proves that the two counts are definitionally the
same after the canonical Nat-to-ZMod coercion.
-/

namespace Erdos85

private theorem list_countP_eq_filter_card
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

/-- Counting two Boolean predicates over the CNF's Nat enumeration agrees
with filtering the graph-facing `ZMod 8` universe by their conjunction. -/
theorem zmodEight_range_filter_countP_eq_univ_filter_card
    (p q : ZMod 8 → Bool) :
    ((List.range 8).filter fun (n : Nat) ↦ p (n : ZMod 8)).countP
        (fun (n : Nat) ↦ q (n : ZMod 8)) =
      ((Finset.univ : Finset (ZMod 8)).filter fun z ↦
        p z = true ∧ q z = true).card := by
  rw [list_countP_eq_filter_card _ _ (List.nodup_range.filter _)]
  apply Finset.card_bij (fun (n : Nat) _ ↦ (n : ZMod 8))
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    rw [List.mem_toFinset, List.mem_filter] at hn
    exact ⟨Finset.mem_univ _, hn.1.2, hn.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_filter] at ha hb
    have hal : a < 8 := List.mem_range.mp ha.1.1
    have hbl : b < 8 := List.mem_range.mp hb.1.1
    have hav : (a : ZMod 8).val = a := ZMod.val_natCast_of_lt hal
    have hbv : (b : ZMod 8).val = b := ZMod.val_natCast_of_lt hbl
    have := congrArg ZMod.val hab
    omega
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · rw [Finset.mem_filter, List.mem_toFinset, List.mem_filter]
      exact ⟨⟨List.mem_range.mpr z.val_lt, by
        simpa only [ZMod.natCast_zmod_val] using hz.2.1⟩, by
          simpa only [ZMod.natCast_zmod_val] using hz.2.2⟩
    · exact ZMod.natCast_zmod_val z

end Erdos85

#print axioms Erdos85.zmodEight_range_filter_countP_eq_univ_filter_card
