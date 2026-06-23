/-
  Power Mean equality condition — NEGATIVE exponents `r < t < 0`.

  Extends `PowerMeanEqualityCase.power_mean_eq_iff_all_eq_pos` (positive case,
  `CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01.lean:84`) to negative exponents
  via the duality `M_p(z,w) = M_{-p}(z⁻¹,w)⁻¹` (`power_mean_neg_inv`,
  `AmgmInequalityOQ03.lean:230`). Mirrors the compiled template
  `power_mean_monotone_neg` (`AmgmInequalityOQ03.lean:292`) line-for-line for the
  duality bookkeeping.

  STATUS: build-VERIFIED (0 sorry / 0 axiom) and REGISTERED in Proofs.lean.
  `docker-build Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01OQ01` →
  `✔ [3060/3060] Built` (researcher-8, 2026-06-16). Drafted by researcher-7.

  All cited lemmas verified present on main (v4.26.0):
  - `power_mean_neg_inv` (AmgmInequalityOQ03.lean:230)
  - `PowerMeanEqualityCase.power_mean_eq_iff_all_eq_pos`
    (CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01.lean:84)
  - `inv_inj : a⁻¹ = b⁻¹ ↔ a = b` (Mathlib/Algebra/Group/Basic.lean:294)

  Cross-zero case `r < 0 < t` is a SEPARATE follow-up (needs the geometric mean
  M₀, outside `weightedPowerMean`'s `p ≠ 0` domain); not bundled here.
-/
import Mathlib.Tactic
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01

namespace PowerMeanEqualityNegCase
open Real Finset
variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

theorem power_mean_eq_iff_all_eq_neg
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hrt : r < t) (ht : t < 0) (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne = weightedPowerMean s w z t htne ↔
    ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  have hzinv : ∀ i ∈ s, 0 < (fun i => (z i)⁻¹) i := fun i hi => inv_pos.mpr (hz i hi)
  have hnt_pos : 0 < -t := neg_pos.mpr ht
  have hnr_pos : 0 < -r := neg_pos.mpr (hrt.trans ht)
  have hntr : -t < -r := neg_lt_neg hrt
  rw [power_mean_neg_inv s w z hw0 hz hrne, power_mean_neg_inv s w z hw0 hz htne, inv_inj]
  rw [eq_comm,
      PowerMeanEqualityCase.power_mean_eq_iff_all_eq_pos s w (fun i => (z i)⁻¹)
        hw hw' hzinv hnt_pos hnr_pos hntr]
  constructor
  · exact fun h j hj k hk => inv_inj.mp (h j hj k hk)
  · exact fun h j hj k hk => inv_inj.mpr (h j hj k hk)

end PowerMeanEqualityNegCase
