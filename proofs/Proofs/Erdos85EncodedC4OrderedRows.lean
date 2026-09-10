import Proofs.Erdos85EncodedC4CachedRows

namespace Erdos85

/-- Store rows once and test each distinct pair in only one order. -/
def encodedC4FreeOrderedRows {n : Nat} (B : Fin n → Fin n → Bool) : Bool :=
  let rows := (List.finRange n).map fun p => (p, Finset.univ.filter fun x => B p x)
  rows.all fun r => rows.all fun s =>
    decide (s.1 ≤ r.1) || decide ((r.2 ∩ s.2).card ≤ 1)

theorem encodedC4FreeOrderedRows_eq {n : Nat} (B : Fin n → Fin n → Bool) :
    encodedC4FreeOrderedRows B = encodedC4Free B := by
  rw [← encodedC4FreeCachedRows_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [encodedC4FreeOrderedRows, encodedC4FreeCachedRows, List.all_map,
    Function.comp_def, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h p q
    by_cases he : p = q
    · exact Or.inl he
    · apply Or.inr
      rcases lt_or_gt_of_ne he with hpq | hqp
      · rcases h p q with hle | hc
        · exact False.elim (not_le_of_gt hpq hle)
        · exact hc
      · rcases h q p with hle | hc
        · exact False.elim (not_le_of_gt hqp hle)
        · simpa only [Finset.inter_comm] using hc
  · intro h p q
    by_cases hle : q ≤ p
    · exact Or.inl hle
    · apply Or.inr
      rcases h p q with he | hc
      · exact False.elim (hle (by simp [he]))
      · exact hc

end Erdos85
#print axioms Erdos85.encodedC4FreeOrderedRows_eq
