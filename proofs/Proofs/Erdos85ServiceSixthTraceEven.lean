import Proofs.Erdos85ResidualSixthMomentStrict
import Proofs.Erdos85CubicTraceParity

/-! # Parity rounding of the strict service sixth trace -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The strict complex h305 threshold becomes the even integer threshold
`61250` after scalar descent to the integer adjacency matrix. -/
theorem trace_int_adjMatrix_pow_six_ge_61250_of_complex_strict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstrict : 61248 < (Matrix.trace ((G.adjMatrix ℂ) ^ 6)).re) :
    61250 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hcast := trace_complex_adjMatrix_pow_eq_intCast G 6
  rw [hcast] at hstrict
  norm_num at hstrict
  have hstrictInt : (61248 : ℤ) <
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    exact_mod_cast hstrict
  exact even_strict_sixthMoment_ge_61250 _
    (even_trace_adjMatrix_pow_six G) hstrictInt

end


end Erdos85

#print axioms
  Erdos85.trace_int_adjMatrix_pow_six_ge_61250_of_complex_strict
