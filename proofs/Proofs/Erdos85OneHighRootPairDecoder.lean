import Proofs.Erdos85OneHighSourcePairTurn

/-! # Decoding canonical root mate-pairs

The quotient `oneHighRootPair : Fin 8 → Fin 4` has exactly the standard
mate-pairs as fibers.  This transports graph-side far-branch membership into
the pair inequalities consumed by the source-turn classifier.
-/

namespace Erdos85

noncomputable section

/-- Two canonical root labels have the same pair quotient exactly when they
are equal or standard mates. -/
theorem oneHighRootPair_eq_iff_eq_or_standardMate (x y : Fin 8) :
    oneHighRootPair x = oneHighRootPair y ↔
      x = y ∨ x = oneHighStandardMate y := by
  decide +revert

/-- A graph root lying in a source's far set has a different canonical
mate-pair from that source. -/
theorem oneHighRootPair_ne_of_branch_mem_far
    {R : Type*} [Fintype R] [DecidableEq R]
    (mate : R → R) (branchLabel : R ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (mate s) =
      oneHighStandardMate (branchLabel s))
    (s a : R)
    (ha : a ∈ ((Finset.univ.erase s).erase (mate s))) :
    oneHighRootPair (branchLabel s) ≠
      oneHighRootPair (branchLabel a) := by
  intro hp
  have hp' : oneHighRootPair (branchLabel a) =
      oneHighRootPair (branchLabel s) := hp.symm
  rcases (oneHighRootPair_eq_iff_eq_or_standardMate
    (branchLabel a) (branchLabel s)).mp hp' with h | h
  · have has : a = s := branchLabel.injective h
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1 has
  · have ham : a = mate s := branchLabel.injective
      (h.trans (hbranchMate s).symm)
    exact (Finset.mem_erase.mp ha).1 ham

end

end Erdos85
