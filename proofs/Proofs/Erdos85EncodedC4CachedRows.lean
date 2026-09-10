import Proofs.Erdos85EncodedC4Filter

namespace Erdos85

/-- Materialize each adjacency row once before testing common-neighbor counts. -/
def encodedC4FreeCachedRows {n : Nat} (B : Fin n → Fin n → Bool) : Bool :=
  let rows := (List.finRange n).map fun p =>
    (p, Finset.univ.filter fun x => B p x)
  rows.all fun r => rows.all fun s =>
    decide (r.1 = s.1) || decide ((r.2 ∩ s.2).card ≤ 1)

theorem encodedC4FreeCachedRows_eq {n : Nat} (B : Fin n → Fin n → Bool) :
    encodedC4FreeCachedRows B = encodedC4Free B := by
  have hinter (p q : Fin n) :
      (Finset.univ.filter fun x => B p x) ∩ (Finset.univ.filter fun x => B q x) =
        Finset.univ.filter (fun x => B p x && B q x) := by
    ext x
    simp
  apply Bool.eq_iff_iff.mpr
  simp only [encodedC4FreeCachedRows, List.all_map, Function.comp_def, List.all_eq_true,
    List.mem_finRange, forall_const, Bool.or_eq_true, decide_eq_true_eq,
    encodedC4Free, hinter]
  constructor
  · intro h p q hpq
    rcases h p q with he | hc
    · exact False.elim (hpq he)
    · exact hc
  · intro h p q
    by_cases hpq : p = q
    · exact Or.inl hpq
    · exact Or.inr (h p q hpq)

end Erdos85
#print axioms Erdos85.encodedC4FreeCachedRows_eq
