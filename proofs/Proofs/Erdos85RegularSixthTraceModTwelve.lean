import Proofs.Erdos85RegularCubicTraceModFour
import Proofs.Erdos85RegularSixthTraceDivisibility

/-! # A general mod-twelve sixth-trace criterion

Node: F.3 GENERALIZATION.  This packages the interaction between the
parameterized mod-four cubic ledger and the regular mod-six divisibility
criterion.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- If `3 ∣ |V|d` and the explicit cubic-row/triangle residue vanishes
modulo four, then the sixth adjacency trace is divisible by twelve. -/
theorem twelve_dvd_regular_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ x, G.degree x = d)
    (hcard : 3 ≤ Fintype.card V)
    (hcardDegree : (3 : ℤ) ∣ (Fintype.card V : ℤ) * d)
    (htriangleResidue : (4 : ℤ) ∣
      (Fintype.card V : ℤ) * (d : ℤ) ^ 3 -
        6 * (adjacencyTriangleMinorFinset G).card) :
    (12 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hmodFour := regular_trace_pow_six_mod_four G d hreg hcard
  obtain ⟨u, hu⟩ := hmodFour
  obtain ⟨v, hv⟩ := htriangleResidue
  have hfour : (4 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    refine ⟨u + v, ?_⟩
    linear_combination hu + hv
  have hsix := six_dvd_regular_trace_pow_six G d hreg hcardDegree
  have hthree : (3 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) :=
    dvd_trans (by norm_num : (3 : ℤ) ∣ 6) hsix
  exact IsCoprime.mul_dvd (by norm_num : IsCoprime (3 : ℤ) 4)
    hthree hfour

end


end Erdos85

#print axioms Erdos85.twelve_dvd_regular_trace_pow_six
