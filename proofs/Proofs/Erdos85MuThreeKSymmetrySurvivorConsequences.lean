import Proofs.Erdos85MuThreeAllTriangleKSymmetryEnumeration

/-!
# Consumer theorems for the mu-three K-symmetry enumeration

These statements hide the executable search and expose exactly the explicit
row-support conclusions needed by the fixed-K certificate dispatcher.
-/

namespace Erdos85

theorem mem_mu3KSurvivorsH16AllTriangle_of_admissible
    (rows : Mu3KRows)
    (h : Mu3KSectorSearchAdmissible mu3H16Row mu3EmptyRows rows) :
    rows ∈ mu3KSurvivorsH16AllTriangle := by
  have hmem := mu3KSectorEnumeration_complete _ _ rows h
  rwa [mu3KSectorEnumeration_H16_allTriangle_eq] at hmem

theorem mem_mu3KSurvivorsH88AllTriangle_of_admissible
    (rows : Mu3KRows)
    (h : Mu3KSectorSearchAdmissible mu3H88Row mu3EmptyRows rows) :
    rows ∈ mu3KSurvivorsH88AllTriangle := by
  have hmem := mu3KSectorEnumeration_complete _ _ rows h
  rwa [mu3KSectorEnumeration_H88_allTriangle_eq] at hmem

theorem eq_mu3KSurvivorH88FirstTf_of_admissible
    (rows : Mu3KRows)
    (h : Mu3KSectorSearchAdmissible mu3H88Row mu3H88FirstTfRows rows) :
    rows = mu3KSurvivorH88FirstTf := by
  have hmem := mu3KSectorEnumeration_complete _ _ rows h
  rw [mu3KSectorEnumeration_H88_firstTf_eq] at hmem
  simpa using hmem

theorem eq_mu3KSurvivorH88SecondTf_of_admissible
    (rows : Mu3KRows)
    (h : Mu3KSectorSearchAdmissible mu3H88Row mu3H88SecondTfRows rows) :
    rows = mu3KSurvivorH88SecondTf := by
  have hmem := mu3KSectorEnumeration_complete _ _ rows h
  rw [mu3KSectorEnumeration_H88_secondTf_eq] at hmem
  simpa using hmem

theorem eq_mu3KSurvivorH106SixTf_of_admissible
    (rows : Mu3KRows)
    (h : Mu3KSectorSearchAdmissible mu3H106Row mu3H106SixTfRows rows) :
    rows = mu3KSurvivorH106SixTf := by
  have hmem := mu3KSectorEnumeration_complete _ _ rows h
  rw [mu3KSectorEnumeration_H106_sixTf_eq] at hmem
  simpa using hmem

end Erdos85

#print axioms Erdos85.mem_mu3KSurvivorsH16AllTriangle_of_admissible
#print axioms Erdos85.mem_mu3KSurvivorsH88AllTriangle_of_admissible
#print axioms Erdos85.eq_mu3KSurvivorH88FirstTf_of_admissible
#print axioms Erdos85.eq_mu3KSurvivorH88SecondTf_of_admissible
#print axioms Erdos85.eq_mu3KSurvivorH106SixTf_of_admissible
