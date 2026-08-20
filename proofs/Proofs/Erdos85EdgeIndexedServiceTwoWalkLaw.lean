import Proofs.Erdos85EdgeIndexedServiceAlgebraPackage

/-! # Entrywise two-walk law for edge-indexed service -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- In the 2-by-6 regular service regime, the number-valued service two-walk
entry exceeds the corresponding internal two-walk endpoint entry by four. -/
theorem edgeIndexedService_twoWalkLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : V) (a : R.edgeFinset) :
    (edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
        Cedge.adjMatrix ℂ) u a =
      (H.adjMatrix ℂ * H.adjMatrix ℂ *
        edgeEndpointIncidenceMatrix R) u a + 4 := by
  have hsq := edgeIndexedService_squaredEquation_of_regular
    H R Cedge hservice 2 6 hHreg hCreg
  have hua := congrFun (congrFun hsq u) a
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    edgeIndexedOnesMatrix] at hua
  norm_num at hua ⊢
  linear_combination -hua

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_twoWalkLaw
