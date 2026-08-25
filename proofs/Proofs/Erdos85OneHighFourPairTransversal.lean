import Proofs.Erdos85OneHighRootPairDecoder

/-!
# Exhaustion by four canonical root mate-pairs

Four pairwise-distinct values in `Fin 4` exhaust the type.  The graph-facing
wrapper below applies this elementary fact to the canonical quotient of the
eight root labels by `oneHighStandardMate`.
-/

namespace Erdos85

set_option maxHeartbeats 0 in
theorem finFour_eq_one_of_four_of_pairwise_ne
    (a b c d z : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    z = a ∨ z = b ∨ z = c ∨ z = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases z <;> simp_all

/-- Four root labels occupying distinct canonical mate-pairs form a
transversal: every root label lies in one of those four mate-pairs. -/
theorem oneHighRootPair_eq_one_of_four_of_pairwise_ne
    (a b c d z : Fin 8)
    (hab : oneHighRootPair a ≠ oneHighRootPair b)
    (hac : oneHighRootPair a ≠ oneHighRootPair c)
    (had : oneHighRootPair a ≠ oneHighRootPair d)
    (hbc : oneHighRootPair b ≠ oneHighRootPair c)
    (hbd : oneHighRootPair b ≠ oneHighRootPair d)
    (hcd : oneHighRootPair c ≠ oneHighRootPair d) :
    oneHighRootPair z = oneHighRootPair a ∨
      oneHighRootPair z = oneHighRootPair b ∨
      oneHighRootPair z = oneHighRootPair c ∨
      oneHighRootPair z = oneHighRootPair d :=
  finFour_eq_one_of_four_of_pairwise_ne
    (oneHighRootPair a) (oneHighRootPair b)
    (oneHighRootPair c) (oneHighRootPair d)
    (oneHighRootPair z) hab hac had hbc hbd hcd

end Erdos85
