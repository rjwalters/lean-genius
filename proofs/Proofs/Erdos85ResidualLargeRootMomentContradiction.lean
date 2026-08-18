import Mathlib
import Proofs.Erdos85RealRootPowerSums

/-! # Residual large-root moment contradictions -/

open Polynomial

namespace Erdos85

noncomputable section

theorem false_of_residual_degree_thirteen_largeRoot
    (Q : ℚ[X]) (lambda : ℝ)
    (hQmonic : Q.Monic) (hdegree : Q.natDegree = 13)
    (hsecond : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 = 110)
    (hfourth : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 = 3246)
    (hsplit : (Q.map (algebraMap ℚ ℝ)).Splits)
    (hlambda : lambda ∈ (Q.map (algebraMap ℚ ℝ)).roots)
    (hlower : (2686 : ℝ) / 49 ≤ lambda ^ 2) : False := by
  let Qr := Q.map (algebraMap ℚ ℝ)
  have hrootsCard : Qr.roots.card = 13 := by
    rw [← hsplit.natDegree_eq_card_roots]
    simpa [Qr] using hdegree
  have hsecondR : realRootPowerSum Qr 2 = 110 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 2 hsplit hQmonic.ne_zero
    rw [hsecond] at hc
    exact_mod_cast hc.symm
  have hfourthR : realRootPowerSum Qr 4 = 3246 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 4 hsplit hQmonic.ne_zero
    rw [hfourth] at hc
    exact_mod_cast hc.symm
  have hcauchy := realRootPowerSum_cauchy_erase Qr hlambda
  rw [hrootsCard, hsecondR, hfourthR] at hcauchy
  norm_num at hcauchy
  have hcauchy' :
      (110 - lambda ^ 2) ^ 2 ≤ 12 * (3246 - (lambda ^ 2) ^ 2) := by
    convert hcauchy using 1 <;> ring
  nlinarith [sq_nonneg (lambda ^ 2 - (2686 : ℝ) / 49)]

theorem false_of_residual_degree_nine_largeRoot
    (Q : ℚ[X]) (lambda : ℝ)
    (hQmonic : Q.Monic) (hdegree : Q.natDegree = 9)
    (hsecond : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 = 84)
    (hfourth : complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 = 3108)
    (hsplit : (Q.map (algebraMap ℚ ℝ)).Splits)
    (hlambda : lambda ∈ (Q.map (algebraMap ℚ ℝ)).roots)
    (hlower : (2716 : ℝ) / 49 ≤ lambda ^ 2) : False := by
  let Qr := Q.map (algebraMap ℚ ℝ)
  have hrootsCard : Qr.roots.card = 9 := by
    rw [← hsplit.natDegree_eq_card_roots]
    simpa [Qr] using hdegree
  have hsecondR : realRootPowerSum Qr 2 = 84 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 2 hsplit hQmonic.ne_zero
    rw [hsecond] at hc
    exact_mod_cast hc.symm
  have hfourthR : realRootPowerSum Qr 4 = 3108 := by
    have hc := complexRootPowerSum_rat_map_eq_real Q 4 hsplit hQmonic.ne_zero
    rw [hfourth] at hc
    exact_mod_cast hc.symm
  have hcauchy := realRootPowerSum_cauchy_erase Qr hlambda
  rw [hrootsCard, hsecondR, hfourthR] at hcauchy
  norm_num at hcauchy
  have hcauchy' :
      (84 - lambda ^ 2) ^ 2 ≤ 8 * (3108 - (lambda ^ 2) ^ 2) := by
    convert hcauchy using 1 <;> ring
  nlinarith [sq_nonneg (lambda ^ 2 - (2716 : ℝ) / 49)]

end


end Erdos85
