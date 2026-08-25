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

/-- The exact form of four-pair exhaustion produced by a separated repeated
key: the two owner labels are distinct non-mates, the key endpoints are
distinct non-mates, and both endpoints are far from both owner pairs. -/
theorem oneHighRootPair_eq_owner_or_key_of_separated
    (s t a b z : Fin 8)
    (hst : s ≠ t) (htm : t ≠ oneHighStandardMate s)
    (hab : a ≠ b) (hbm : b ≠ oneHighStandardMate a)
    (haS : a ≠ s ∧ a ≠ oneHighStandardMate s)
    (hbS : b ≠ s ∧ b ≠ oneHighStandardMate s)
    (haT : a ≠ t ∧ a ≠ oneHighStandardMate t)
    (hbT : b ≠ t ∧ b ≠ oneHighStandardMate t) :
    oneHighRootPair z = oneHighRootPair s ∨
      oneHighRootPair z = oneHighRootPair t ∨
      oneHighRootPair z = oneHighRootPair a ∨
      oneHighRootPair z = oneHighRootPair b := by
  apply oneHighRootPair_eq_one_of_four_of_pairwise_ne s t a b z
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate hst.symm htm).symm
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate haS.1 haS.2).symm
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate hbS.1 hbS.2).symm
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate haT.1 haT.2).symm
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate hbT.1 hbT.2).symm
  · exact (oneHighRootPair_ne_of_ne_of_ne_standardMate hab.symm hbm).symm

end Erdos85
