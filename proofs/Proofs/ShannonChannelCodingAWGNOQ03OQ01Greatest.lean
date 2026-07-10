/-
# Shannon AWGN water-filling, oq-03-oq-01 — capacity is the attained maximum

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`, which
proves optimality of `Pᵢ⋆ = (μ − Nᵢ)₊` in *inequality* form — `waterfilling_optimal`
shows every feasible allocation's rate is `≤` the water-filling rate — together
with the closed-form optimum and existence/uniqueness of the water level `μ`).

The companions `…EqualNoise.lean` and `…Monotone.lean` record the equal-noise
closed form and the structural monotonicities.  This file supplies the missing
**variational packaging**: the water-filling rate is not merely an upper bound on
achievable rates, it is *attained* — it is the greatest element, and hence the
supremum, of the set of rates realisable by feasible allocations.  This is the
canonical "the constrained capacity is achieved" statement of the water-filling
theorem (Cover & Thomas, *Elements of Information Theory*, Thm 9.9.1).

All axiom-free / sorry-free:

* `waterAlloc_feasible`        — the water-filling allocation `Pᵢ⋆ = (μ − Nᵢ)₊` is
  itself feasible: non-negative, with total power `= P ≤ P`.
* `waterfilling_isGreatest`    — **the headline**: the water-filling rate
  `R(waterAlloc μ N)` is the *greatest* element of the achievable-rate set
  `{ R | ∃ feasible x, parallelRate N x = R }`.  Membership is `waterAlloc_feasible`
  (the optimum is itself achievable); the upper-bound half is `waterfilling_optimal`.
* `waterfilling_rate_isLUB`    — consequently it is the *least upper bound*
  (supremum) of the achievable-rate set: the constrained capacity equals
  `sup { parallelRate N x | x feasible }`.

Tags: information-theory, shannon, awgn, water-filling, capacity, supremum
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The set of total rates achievable by a **feasible** power allocation over the
parallel Gaussian channel with noise powers `N` and total-power budget `P`: an
allocation `x` is feasible when every component is non-negative and the total power
`∑ᵢ xᵢ` does not exceed `P`. -/
def achievableRates (N : ι → ℝ) (P : ℝ) : Set ℝ :=
  { R : ℝ | ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i ≤ P) ∧ parallelRate N x = R }

/-- **The water-filling allocation is feasible.**  For the water level `μ` realising
a budget `P` (`∑ᵢ (μ − Nᵢ)₊ = P`), the allocation `Pᵢ⋆ = (μ − Nᵢ)₊` is non-negative
and its total power is exactly `P`, so in particular `≤ P`: the optimum is itself an
achievable point, not just an unattained bound. -/
theorem waterAlloc_feasible (N : ι → ℝ) {μ P : ℝ} (hbudget : waterBudget N μ = P) :
    (∀ i, 0 ≤ waterAlloc μ N i) ∧ ∑ i, waterAlloc μ N i ≤ P :=
  ⟨fun i => waterAlloc_nonneg μ N i, le_of_eq hbudget⟩

/-- **The water-filling rate is the greatest achievable rate.**  Let `μ > 0` be the
water level realising a budget `P` (`∑ᵢ (μ − Nᵢ)₊ = P`), with positive noise floors.
Then the water-filling rate `R(waterAlloc μ N)` is the *greatest element* of the
achievable-rate set: it is itself achievable (by the feasible allocation `Pᵢ⋆`) and
it dominates every achievable rate.

This upgrades `waterfilling_optimal` from a one-sided inequality to the full
"maximum is attained" statement.  The two halves are exactly feasibility
(`waterAlloc_feasible` ⇒ membership) and optimality (`waterfilling_optimal` ⇒ upper
bound). -/
theorem waterfilling_isGreatest
    (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ : ℝ} (hμ : 0 < μ) {P : ℝ} (hbudget : waterBudget N μ = P) :
    IsGreatest (achievableRates N P) (parallelRate N (waterAlloc μ N)) := by
  obtain ⟨hnn, hsum⟩ := waterAlloc_feasible N hbudget
  constructor
  · -- membership: the water-filling allocation itself achieves this rate
    exact ⟨waterAlloc μ N, hnn, hsum, rfl⟩
  · -- upper bound: every feasible rate is dominated (optimality)
    rintro R ⟨x, hx, hxsum, rfl⟩
    exact waterfilling_optimal N hN hμ hbudget x hx hxsum

/-- **The water-filling rate is the supremum of the achievable rates.**  Being the
greatest achievable rate, it is a fortiori the *least upper bound*: the constrained
parallel-channel capacity equals `sup { parallelRate N x | x feasible }`.  This is
the variational characterisation of the water-filling capacity. -/
theorem waterfilling_rate_isLUB
    (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ : ℝ} (hμ : 0 < μ) {P : ℝ} (hbudget : waterBudget N μ = P) :
    IsLUB (achievableRates N P) (parallelRate N (waterAlloc μ N)) :=
  (waterfilling_isGreatest N hN hμ hbudget).isLUB

end ShannonWaterFilling
