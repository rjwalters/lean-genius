import Proofs.Erdos85ResidualSixthMomentHankel
import Proofs.Erdos85HermitianCharpolyPowerSums

/-! # Sixth-moment trace bound from a real residual factor -/

open Polynomial Matrix

namespace Erdos85

noncomputable section

/-- A real-rooted residual with the h305 second and fourth moments, together
with a complex complementary factor of sixth moment `46912`, forces the
ambient Hermitian sixth trace to be at least `61248` in real part. -/
theorem h305_trace_sixth_lower_of_realResidual_factor
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℂ) (p : ℝ[X]) (q : ℂ[X])
    (hA : A.IsHermitian) (hsplit : p.Splits) (hp : p ≠ 0)
    (hq : q ≠ 0)
    (hfactor : A.charpoly = p.map (algebraMap ℝ ℂ) * q)
    (hsecond : complexRootPowerSum (p.map (algebraMap ℝ ℂ)) 2 = 224)
    (hfourth : complexRootPowerSum (p.map (algebraMap ℝ ℂ)) 4 = 1792)
    (hqsixth : complexRootPowerSum q 6 = 46912) :
    (61248 : ℝ) ≤ (Matrix.trace (A ^ 6)).re := by
  have hpmap : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    simpa using (Polynomial.map_injective (algebraMap ℝ ℂ)
      (algebraMap ℝ ℂ).injective).ne hp
  have hsecondReal : realRootPowerSum p 2 = 224 := by
    have hmap := complexRootPowerSum_map_real_eq p 2 hsplit hp
    rw [hsecond] at hmap
    exact_mod_cast congrArg Complex.re hmap.symm
  have hfourthReal : realRootPowerSum p 4 = 1792 := by
    have hmap := complexRootPowerSum_map_real_eq p 4 hsplit hp
    rw [hfourth] at hmap
    exact_mod_cast congrArg Complex.re hmap.symm
  have hsixthReal : 14336 ≤ realRootPowerSum p 6 :=
    h305_realResidual_sixthMoment_lower p hsecondReal hfourthReal
  have hsixthMap := complexRootPowerSum_map_real_eq p 6 hsplit hp
  have hadd := complexRootPowerSum_mul hpmap hq 6
  rw [← hfactor, complexRootPowerSum_charpoly_eq_trace_pow A hA 6,
    hqsixth, hsixthMap] at hadd
  have hre := congrArg Complex.re hadd
  norm_num at hre
  exact_mod_cast (show (61248 : ℝ) ≤ (Matrix.trace (A ^ 6)).re by
    linarith)

end


end Erdos85

#print axioms Erdos85.h305_trace_sixth_lower_of_realResidual_factor
