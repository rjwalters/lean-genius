import Mathlib.Tactic

/-! The integer cross-entry implication in the H5 defect-component argument.
This scalar theorem does not formalize the graph-to-Perron quotient bridge. -/
namespace Erdos85

theorem h5_integral_perron_cross_entry_zero
    (alpha beta gamma delta : ℤ)
    (hbeta : beta = 0 ∨ beta = 1)
    (hdelta : delta = 0 ∨ delta = 1)
    (hcount : alpha + 7 * beta ≤ 7)
    (hfirst : 64 * alpha + 398 * beta = 100 * gamma + 640 * delta)
    (hsecond : 50 * alpha + 320 * beta = 60 * gamma + 500 * delta) :
    alpha = 0 ∧ beta = 0 ∧ gamma = 0 ∧ delta = 0 := by
  have hparity : 2 * gamma + beta = 0 := by omega
  have hb : beta = 0 := by omega
  have hg : gamma = 0 := by omega
  have ha : alpha = 10 * delta := by omega
  have hd : delta = 0 := by omega
  omega

end Erdos85

#print axioms Erdos85.h5_integral_perron_cross_entry_zero
