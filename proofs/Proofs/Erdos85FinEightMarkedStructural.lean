import Proofs.Erdos85OneHighCanonicalMate

/-! # Structural canonicalization of marked standard mate endpoints -/

namespace Erdos85

theorem finEight_standardMate_canonicalize_marked_structural
    (marked : Fin 8 → Bool)
    (hpair : ∀ i, marked i = true →
      marked (oneHighStandardMate i) = false) :
    ∃ τ : Equiv.Perm (Fin 8),
      (∀ i, τ (oneHighStandardMate i) = oneHighStandardMate (τ i)) ∧
      ∀ i,
        marked (τ.symm i) =
          decide (i.val % 2 = 0 ∧
            i.val / 2 < (Finset.univ.filter fun j => marked j).card) :=
  finEight_standardMate_canonicalize_marked marked hpair

end Erdos85
