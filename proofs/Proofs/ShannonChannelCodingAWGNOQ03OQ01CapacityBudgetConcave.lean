/-
# Shannon AWGN water-filling, oq-03-oq-01 — capacity is CONCAVE in the total power budget

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`).

The value function of the water-filling convex program,

    C(P) = max { R(x) : xᵢ ≥ 0, ∑ᵢ xᵢ ≤ P },   R(x) = ∑ᵢ ½ log(1 + xᵢ/Nᵢ),

is the parallel-Gaussian channel capacity as a function of the *total* power
budget `P`.  The companion `…EqualNoise.lean` proves scalar-power concavity only
in the degenerate **equal-noise** case `C(P) = (n/2)·log(1 + P/(nc))`; the
`…Concave.lean` / `…StrictConcave.lean` files prove concavity in the power
**vector** and `…WidebandConcave.lean` proves it in the **bandwidth/channel
count**.  What no existing file supplies is the classical macroscopic law for a
*general* noise profile: the optimal capacity `C(P)` is a **concave** function of
the scalar total power `P` — spending more total power yields *diminishing
marginal capacity*.  This file fills that gap, all axiom-free / sorry-free.

The proof is the standard "value function of a concave program over a
budget-scaled convex feasible set is concave" argument, with no envelope theorem
needed.  Given optimal allocations at water levels `μ₁, μ₂` realising budgets
`P₁ = g(μ₁)`, `P₂ = g(μ₂)`, the convex combination
`x = a·waterAlloc μ₁ N + b·waterAlloc μ₂ N` is a feasible allocation for the
budget `a·P₁ + b·P₂`:

* it is non-negative (`waterAlloc_nonneg`, `mul_nonneg`, `add_nonneg`), and
* its total power is exactly `a·P₁ + b·P₂ = g(μ₃)`, the budget realised by the
  combined water level `μ₃`.

Hence by optimality of water-filling at level `μ₃` (`waterfilling_optimal`),
`R(x) ≤ R(waterAlloc μ₃ N) = C(a·P₁ + b·P₂)`, while joint concavity of `R` in the
power vector (`parallelRate_concaveOn_power`) gives
`a·C(P₁) + b·C(P₂) = a·R(waterAlloc μ₁ N) + b·R(waterAlloc μ₂ N) ≤ R(x)`.
Chaining the two inequalities is the concavity of `C`.

* `capacity_concave_budget` — the general midpoint/convex-combination form:
  `a·C(P₁) + b·C(P₂) ≤ C(a·P₁ + b·P₂)` (concavity of the value function).
* `capacity_midpoint_concave_budget` — the `a = b = ½` specialisation making the
  "diminishing returns in total power" reading explicit.

Tags: information-theory, shannon, awgn, water-filling, capacity, concavity, value-function, convex-program
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01Concave

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **The water-filling capacity is concave in the total power budget.**
Let `μ₁, μ₂` be water levels realising budgets `P₁ = g(μ₁)`, `P₂ = g(μ₂)`, and let
`μ₃` (with `μ₃ > 0`) realise the convexly-combined budget
`g(μ₃) = a·P₁ + b·P₂` for weights `a, b ≥ 0`, `a + b = 1`.  Then the optimal
capacities satisfy

    a · C(P₁) + b · C(P₂) ≤ C(a·P₁ + b·P₂),

where `C(g(μ)) = parallelRate N (waterAlloc μ N)` is the water-filling rate.  This
is the concavity of the capacity–power value function for a *general* noise
profile `N` — the macroscopic "capacity is a concave function of total power",
i.e. diminishing marginal returns as the total power budget grows.

Proof: the convex combination `x = a·waterAlloc μ₁ N + b·waterAlloc μ₂ N` is a
feasible allocation for the budget `g(μ₃)` (non-negative, total power `a·P₁+b·P₂`).
Optimality of water-filling at level `μ₃` (`waterfilling_optimal`) bounds
`R(x) ≤ R(waterAlloc μ₃ N)`, and joint concavity of `R` in the power vector
(`parallelRate_concaveOn_power`) bounds `a·R(waterAlloc μ₁ N)+b·R(waterAlloc μ₂ N)
≤ R(x)`; chaining gives the claim. -/
theorem capacity_concave_budget (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ₁ μ₂ μ₃ : ℝ} (hμ₃ : 0 < μ₃) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h3 : waterBudget N μ₃ = a * waterBudget N μ₁ + b * waterBudget N μ₂) :
    a * parallelRate N (waterAlloc μ₁ N) + b * parallelRate N (waterAlloc μ₂ N)
      ≤ parallelRate N (waterAlloc μ₃ N) := by
  -- the convex-combination allocation
  set x : ι → ℝ := a • waterAlloc μ₁ N + b • waterAlloc μ₂ N with hx_def
  -- `x` is a non-negative allocation
  have hxnonneg : ∀ i, 0 ≤ x i := by
    intro i
    have h := add_nonneg (mul_nonneg ha (waterAlloc_nonneg μ₁ N i))
      (mul_nonneg hb (waterAlloc_nonneg μ₂ N i))
    simpa [hx_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  -- its total power equals the combined budget `g(μ₃)`
  have hxsum : ∑ i, x i ≤ waterBudget N μ₃ := by
    have hsumeq : ∑ i, x i = a * waterBudget N μ₁ + b * waterBudget N μ₂ := by
      simp only [hx_def, waterBudget, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsumeq, ← h3]
  -- membership of the two optimal allocations in the non-negative orthant
  have hmem : ∀ μ : ℝ,
      waterAlloc μ N ∈ Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ) := by
    intro μ
    rw [Set.mem_univ_pi]
    intro i
    exact Set.mem_Ici.mpr (waterAlloc_nonneg μ N i)
  -- concavity of `R` in the power vector applied to the two optima
  have hconc := (parallelRate_concaveOn_power N hN).2 (hmem μ₁) (hmem μ₂) ha hb hab
  simp only [smul_eq_mul] at hconc
  rw [← hx_def] at hconc
  -- optimality of water-filling at level `μ₃`
  have hopt := waterfilling_optimal N hN hμ₃ (rfl : waterBudget N μ₃ = waterBudget N μ₃)
    x hxnonneg hxsum
  linarith [hconc, hopt]

/-- **Diminishing returns in total power (midpoint form).**  The `a = b = ½`
specialisation of `capacity_concave_budget`: if `μ₃` (with `μ₃ > 0`) realises the
average budget `g(μ₃) = (g(μ₁) + g(μ₂))/2`, then

    (C(P₁) + C(P₂)) / 2 ≤ C((P₁ + P₂)/2).

The average of the capacities at two budgets never exceeds the capacity at their
average budget — the concave "diminishing marginal capacity" law for a general
noise profile. -/
theorem capacity_midpoint_concave_budget (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ₁ μ₂ μ₃ : ℝ} (hμ₃ : 0 < μ₃)
    (h3 : waterBudget N μ₃ = (waterBudget N μ₁ + waterBudget N μ₂) / 2) :
    (parallelRate N (waterAlloc μ₁ N) + parallelRate N (waterAlloc μ₂ N)) / 2
      ≤ parallelRate N (waterAlloc μ₃ N) := by
  have hmain := capacity_concave_budget N hN hμ₃ (μ₁ := μ₁) (μ₂ := μ₂)
    (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by rw [h3]; ring)
  linarith [hmain]

end ShannonWaterFilling
