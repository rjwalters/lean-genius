/-
# Shannon AWGN water-filling, oq-03-oq-01 — STRICT joint concavity & uniqueness

Source: parallel-Gaussian-channel water-filling (see
`ShannonChannelCodingAWGNOQ03OQ01.lean`, namespace `ShannonWaterFilling`).

The companion `…Concave.lean` proves the *weak* joint concavity of the parallel
capacity `parallelRate_concaveOn_power` (the structural reason the KKT
water-filling point is a global optimum) together with the single-channel *strict*
concavity `perUseCapacity_strictConcaveOn`.  What it does **not** supply is the
joint *strict* concavity of the whole power-vector objective — the fact that pins
the water-filling optimum as the **unique** global maximizer (not merely one of a
possibly-flat set of optima).  This file fills that gap, all axiom-free /
sorry-free:

* `parallelRate_strictConcaveOn_power` — the total rate
  `R(P) = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ)` is *strictly* concave in the whole power **vector**
  `P` on the nonnegative orthant `{P | ∀ i, 0 ≤ Pᵢ}`.  Two distinct allocations
  must differ in some coordinate `i₀`, whose per-channel term is strictly concave
  (`perUseCapacity_strictConcaveOn`) while every other term is weakly concave
  (`perUseCapacity_concaveOn`); `Finset.sum_lt_sum` turns "one strict, the rest
  weak" into a strict inequality for the sum.
* `parallelRate_unique_maximizer` — the operational payoff: on the convex orthant a
  strictly concave objective has **at most one** maximizer, so any two power
  allocations that are both optimal over the orthant coincide.

Tags: information-theory, shannon, awgn, water-filling, capacity, strict-concavity, uniqueness
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01Concave

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **The parallel-Gaussian capacity is jointly STRICTLY concave in the power
vector.**  For a positive noise profile `N`, the total rate
`R(P) = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ)` is strictly concave as a function of the whole power
**vector** `P` on the nonnegative orthant `{P | ∀ i, 0 ≤ Pᵢ}`, sharpening the weak
`parallelRate_concaveOn_power`.

Two distinct allocations `x ≠ y` differ in some coordinate `i₀` (`x i₀ ≠ y i₀`);
there the per-channel rate is strictly concave (`perUseCapacity_strictConcaveOn`),
while at every coordinate it is at least weakly concave (`perUseCapacity_concaveOn`).
`Finset.sum_lt_sum` (all terms `≤`, one term `<`) lifts this to a strict inequality
for the total rate.  This is what makes the water-filling optimum the *unique*
global maximizer of the convex program. -/
theorem parallelRate_strictConcaveOn_power (N : ι → ℝ) (hN : ∀ i, 0 < N i) :
    StrictConcaveOn ℝ (Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ))
      (fun P => parallelRate N P) := by
  set s : Set (ι → ℝ) := Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ) with hs_def
  have hs : Convex ℝ s := convex_pi fun i _ => convex_Ici 0
  have hmem : ∀ (P : ι → ℝ), P ∈ s ↔ ∀ i, 0 ≤ P i := by
    intro P; rw [hs_def, Set.mem_univ_pi]; simp only [Set.mem_Ici]
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  -- a coordinate where the two vectors differ
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  have hx' : ∀ i, 0 ≤ x i := (hmem x).mp hx
  have hy' : ∀ i, 0 ≤ y i := (hmem y).mp hy
  -- per-coordinate weak concavity
  have hle : ∀ i ∈ (Finset.univ : Finset ι),
      a * perUseCapacity (x i) (N i) + b * perUseCapacity (y i) (N i)
        ≤ perUseCapacity (a * x i + b * y i) (N i) := by
    intro i _
    have := (perUseCapacity_concaveOn (hN i)).2 (Set.mem_Ici.mpr (hx' i))
      (Set.mem_Ici.mpr (hy' i)) ha.le hb.le hab
    simpa only [smul_eq_mul] using this
  -- strict concavity at the differing coordinate
  have hlt : a * perUseCapacity (x i₀) (N i₀) + b * perUseCapacity (y i₀) (N i₀)
        < perUseCapacity (a * x i₀ + b * y i₀) (N i₀) := by
    have := (perUseCapacity_strictConcaveOn (hN i₀)).2 (Set.mem_Ici.mpr (hx' i₀))
      (Set.mem_Ici.mpr (hy' i₀)) hi₀ ha hb hab
    simpa only [smul_eq_mul] using this
  have hsum := Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ i₀, hlt⟩
  simp only [smul_eq_mul, parallelRate]
  calc a * ∑ i, perUseCapacity (x i) (N i) + b * ∑ i, perUseCapacity (y i) (N i)
      = ∑ i, (a * perUseCapacity (x i) (N i) + b * perUseCapacity (y i) (N i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ < ∑ i, perUseCapacity (a * x i + b * y i) (N i) := hsum
    _ = ∑ i, perUseCapacity ((a • x + b • y) i) (N i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Uniqueness of the water-filling optimum.**  Because `parallelRate` is
strictly concave on the convex nonnegative orthant, it has *at most one* maximizer:
any two power allocations `x`, `y` in the orthant that are both maximal over it must
coincide.  This is the operational upshot of `parallelRate_strictConcaveOn_power` —
the water-filling allocation of `parallel_gaussian_capacity` is not merely *a*
global optimum but *the* global optimum. -/
theorem parallelRate_unique_maximizer (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {x y : ι → ℝ}
    (hx : x ∈ Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ))
    (hy : y ∈ Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ))
    (hxmax : IsMaxOn (fun P => parallelRate N P)
      (Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ)) x)
    (hymax : IsMaxOn (fun P => parallelRate N P)
      (Set.univ.pi fun _ : ι => Set.Ici (0 : ℝ)) y) : x = y :=
  (parallelRate_strictConcaveOn_power N hN).eq_of_isMaxOn hxmax hymax hx hy

end ShannonWaterFilling
