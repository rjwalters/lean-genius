import Proofs.Erdos85CofinalLowerBound
import Proofs.Erdos85RamseyPlateau

/-!
# Plateau-core degrees diverge

The full-sequence divergence of the forcing threshold excludes bounded-degree
families of plateau cores.
-/

open Filter

namespace Erdos85

/-- At large orders, every plateau core has arbitrarily large certified
minimum degree. -/
theorem eventually_plateauCore_degree_ge (B : ℕ) :
    ∀ᶠ m in atTop, ∀ {d : ℕ}, C4PlateauCore m d → B ≤ d := by
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp minDegreeForC4_tendsto_atTop) B
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 4] with m hmN hm4
  intro d hcore
  have hthreshold : B ≤ minDegreeForC4 (m + 1) := hN (m + 1) (by omega)
  exact hthreshold.trans (hcore.threshold_bounds hm4).2

/-- In particular, canonical cores witnessing downward jumps cannot recur at
bounded threshold degree. -/
theorem eventually_threshold_plateauCore_degree_ge (B : ℕ) :
    ∀ᶠ m in atTop,
      C4PlateauCore m (minDegreeForC4 (m + 1)) →
        B ≤ minDegreeForC4 (m + 1) := by
  filter_upwards [eventually_plateauCore_degree_ge B] with m hm
  exact fun hcore => hm hcore

/-- Quantitative localization from the full polarity deletion band.  A
degree-`d` core must occur before the displayed conductor, for some prime
`p` between `2(d+2)` and `4(d+2)`.  Since the base is `p²+d` and the width is
`p-d`, this is an explicit cubic-in-`d` window. -/
theorem C4PlateauCore.order_lt_prime_band_conductor {m d : ℕ}
    (hcore : C4PlateauCore m d) :
    ∃ p : ℕ, p.Prime ∧ 2 * (d + 2) < p ∧ p ≤ 4 * (d + 2) ∧
      m + 1 < ((p * p + d) / (p - d) + 1) * (p * p + d) := by
  obtain ⟨p, hp, hlower, hupper, hw⟩ := exists_prime_band_eventual_witness d
  refine ⟨p, hp, hlower, hupper, ?_⟩
  by_contra hnot
  have hbound : ((p * p + d) / (p - d) + 1) * (p * p + d) ≤ m + 1 := by
    omega
  obtain ⟨G, hdec, hmin, hfree⟩ := hw (m + 1) hbound
  rcases hcore with ⟨K, hKdec, hKmin, hKfree, hKcover, hnext⟩
  exact hfree (hnext G hdec hmin)

/-- Clean cubic localization: every degree-`d` plateau core has order below
`400(d+2)^3`. -/
theorem C4PlateauCore.order_lt_cubic {m d : ℕ}
    (hcore : C4PlateauCore m d) :
    m + 1 < 400 * (d + 2) ^ 3 := by
  by_contra hnot
  have hbound : 400 * (d + 2) ^ 3 ≤ m + 1 := by omega
  obtain ⟨G, hdec, hmin, hfree⟩ :=
    c4FreeMinDegreeWitness_of_cubic_order hbound
  rcases hcore with ⟨K, hKdec, hKmin, hKfree, hKcover, hnext⟩
  exact hfree (hnext G hdec hmin)

end Erdos85
