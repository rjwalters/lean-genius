import Proofs.Erdos85OneHighSourcePairTurn

/-! # Decoding canonical root mate-pairs

The quotient `oneHighRootPair : Fin 8 → Fin 4` has exactly the standard
mate-pairs as fibers.  This transports graph-side far-branch membership into
the pair inequalities consumed by the source-turn classifier.
-/

namespace Erdos85

noncomputable section

/-- Every canonical mate-pair fiber contains exactly two root labels. -/
theorem card_oneHighRootPair_fiber (p : Fin 4) :
    ((Finset.univ : Finset (Fin 8)).filter fun x =>
      oneHighRootPair x = p).card = 2 := by
  fin_cases p <;> decide +revert

/-- Three labels in one mate-pair fiber cannot be pairwise distinct. -/
theorem three_same_oneHighRootPair_not_pairwise_distinct
    (x y z : Fin 8)
    (hxy : oneHighRootPair x = oneHighRootPair y)
    (hxz : oneHighRootPair x = oneHighRootPair z) :
    x = y ∨ x = z ∨ y = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all [oneHighRootPair]

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
