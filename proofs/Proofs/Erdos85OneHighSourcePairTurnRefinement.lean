import Proofs.Erdos85OneHighRootPairGraphDecoder
import Proofs.Erdos85OneHighSourcePairTurn

/-! # Graph refinement of the source-pair turn trichotomy -/

namespace Erdos85

noncomputable section

/-- Refining the equal-source-pair branch through the graph decoder yields
four mutually meaningful consumers: the source branches are literally equal,
they are root mates, or one source pair equals the opposite outer endpoint
pair. -/
theorem oneHigh_sourcePair_turn_fourWay
    {R : Type*} [Fintype R] [DecidableEq R]
    (rootMate : R → R) (branchLabel : R ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    (a c s t : R)
    (hturn :
      oneHighRootPair (branchLabel s) = oneHighRootPair (branchLabel t) ∨
      oneHighRootPair (branchLabel s) = oneHighRootPair (branchLabel c) ∨
      oneHighRootPair (branchLabel t) = oneHighRootPair (branchLabel a)) :
    s = t ∨ s = rootMate t ∨
      oneHighRootPair (branchLabel s) = oneHighRootPair (branchLabel c) ∨
      oneHighRootPair (branchLabel t) = oneHighRootPair (branchLabel a) := by
  rcases hturn with hst | hsc | hta
  · rcases (oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
      rootMate branchLabel hbranchMate s t).mp hst with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl hsc))
  · exact Or.inr (Or.inr (Or.inr hta))

end

end Erdos85
