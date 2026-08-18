import Proofs.Erdos85OneHighRootPairDecoder

/-! # Graph-level decoding of canonical root-pair colors -/

namespace Erdos85

noncomputable section

/-- Under a canonical root labeling, equality of pair quotient colors means
exactly equality of source branches or the root-mate relation. -/
theorem oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
    {R : Type*} [Fintype R] [DecidableEq R]
    (rootMate : R → R) (branchLabel : R ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    (s t : R) :
    oneHighRootPair (branchLabel s) = oneHighRootPair (branchLabel t) ↔
      s = t ∨ s = rootMate t := by
  rw [oneHighRootPair_eq_iff_eq_or_standardMate]
  constructor
  · rintro (hst | hstm)
    · exact Or.inl (branchLabel.injective hst)
    · exact Or.inr (branchLabel.injective (hstm.trans (hbranchMate t).symm))
  · rintro (rfl | hsm)
    · exact Or.inl rfl
    · exact Or.inr (by rw [hsm, hbranchMate])

/-- Distinct branches with equal pair quotient colors are root mates. -/
theorem eq_rootMate_of_oneHighRootPair_branchLabel_eq_of_ne
    {R : Type*} [Fintype R] [DecidableEq R]
    (rootMate : R → R) (branchLabel : R ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    {s t : R}
    (hp : oneHighRootPair (branchLabel s) =
      oneHighRootPair (branchLabel t))
    (hst : s ≠ t) : s = rootMate t := by
  rcases (oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
    rootMate branchLabel hbranchMate s t).mp hp with h | h
  · exact (hst h).elim
  · exact h

end

end Erdos85
