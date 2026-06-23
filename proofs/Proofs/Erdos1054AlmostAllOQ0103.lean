import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic

/-!
# Erdős #1054 OQ-01 → OQ-03: The analytic engine needs only the harmonic series

The parent entry (`erdos-1054-oq-01`) formalizes Part II of Erdős Problem 1054 via
the **sigma bound** `f(σ(m)) ≤ m`, which gives `f(σ(m))/σ(m) ≤ m/σ(m) = 1/(σ(m)/m)`.
To push this ratio to `0` one needs an explicit sequence `mₙ` with `σ(mₙ)/mₙ → ∞`.
The parent attributes this analytic input to **Gronwall's theorem**
`σ(m)/(m log log m) → e^γ` (1913) or **Mertens' theorem**, neither of which is in
Mathlib, and so axiomatizes the conclusion.

This entry answers the derived open question

> *Can Mertens/Gronwall's theorem be added to Mathlib to complete the proof?*

with a sharper observation: **for the divergence `σ(m)/m → ∞` the full strength of
Mertens/Gronwall is not required.** The elementary identity

$$\frac{\sigma(m)}{m} \;=\; \sum_{d \mid m} \frac 1 d$$

shows that, along the sequence `mₙ = lcm(1, …, n)`, the ratio dominates the harmonic
partial sum:

$$\frac{\sigma(m_n)}{m_n} \;=\; \sum_{d \mid m_n} \frac 1 d \;\ge\; \sum_{k=1}^{n} \frac 1 k \;=\; H_n,$$

because every `k ≤ n` divides `lcm(1, …, n)`. Since the harmonic series already
diverges in Mathlib (`Real.tendsto_sum_range_one_div_nat_succ_atTop`), we obtain

$$\frac{\sigma(m_n)}{m_n} \longrightarrow \infty$$

**without any Mertens/Gronwall machinery**. This is the analytic input the parent
axiomatized, here supplied with `0` axioms.

## Main results

* `sigma_div_eq_sum_inv` : `(σ m : ℝ)/m = ∑_{d ∣ m} 1/d` for `m ≥ 1`.
* `harmonic_le_sigma_ratio` : `∑_{i<n} 1/(i+1) ≤ σ(lcmUpTo n)/(lcmUpTo n)`.
* `sigma_ratio_tendsto_atTop` : `σ(lcmUpTo n)/(lcmUpTo n) → ∞`.
* `f_sigma_ratio_tendsto_zero` (corollary phrasing) : the upper bound
  `(lcmUpTo n)/σ(lcmUpTo n)` on `f(σ(mₙ))/σ(mₙ)` tends to `0`.
-/

namespace Erdos1054AlmostAllOQ0103

open Finset Filter
open scoped BigOperators Topology

/-- The σ function: sum of all divisors (matching the parent's definition). -/
def sigma (m : ℕ) : ℕ := m.divisors.sum id

/-- The least common multiple of `{1, 2, …, n}`. This is the explicit sequence
    along which `σ(m)/m` diverges. -/
def lcmUpTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- `lcmUpTo n` is positive: it is the lcm of nonzero numbers. -/
theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  rw [lcmUpTo, zero_lt_iff, Finset.lcm_ne_zero_iff]
  intro x hx
  rw [Finset.mem_Icc] at hx
  simpa [id] using Nat.one_le_iff_ne_zero.mp hx.1

/-- Every `k` with `1 ≤ k ≤ n` divides `lcmUpTo n`. -/
theorem dvd_lcmUpTo {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : k ∣ lcmUpTo n := by
  have hmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
  simpa [id] using Finset.dvd_lcm (f := id) hmem

/-- **Key identity.** Over `ℝ`, the abundancy ratio is the sum of reciprocals of
    divisors:  `σ(m)/m = ∑_{d ∣ m} 1/d`. The proof reindexes the divisor sum by
    `d ↦ m/d`, a bijection of `divisors m`. -/
theorem sigma_div_eq_sum_inv (m : ℕ) (hm : 1 ≤ m) :
    (sigma m : ℝ) / m = ∑ d ∈ m.divisors, (1 / (d : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Rewrite each `1/d` as `(m/d : ℕ)/m` (valid since `d ∣ m`).
  have key : ∀ d ∈ m.divisors, (1 / (d : ℝ)) = ((m / d : ℕ) : ℝ) / m := by
    intro d hd
    have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    rw [Nat.cast_div hdvd hd0]
    field_simp
  rw [Finset.sum_congr rfl key]
  -- `∑ d, (m/d : ℕ)/m = ∑ d, (d : ℕ)/m` by reindexing `d ↦ m/d`.
  have hreindex :
      (∑ d ∈ m.divisors, ((m / d : ℕ) : ℝ) / m)
        = ∑ d ∈ m.divisors, ((d : ℕ) : ℝ) / m :=
    Nat.sum_div_divisors m (fun x => (x : ℝ) / m)
  rw [hreindex, ← Finset.sum_div]
  congr 1
  -- `∑ d ∈ divisors, (d : ℝ) = (σ m : ℝ)`.
  rw [sigma, Nat.cast_sum]
  simp [id]

/-- Lower bound: the abundancy ratio of `lcmUpTo n` dominates the `n`-th harmonic
    partial sum `Hₙ = ∑_{i<n} 1/(i+1)`. -/
theorem harmonic_le_sigma_ratio (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ))
      ≤ (sigma (lcmUpTo n) : ℝ) / (lcmUpTo n) := by
  have hpos := lcmUpTo_pos n
  -- The shifted range `{i+1 : i < n}` is a set of divisors of `lcmUpTo n`.
  have hsub : (Finset.range n).image (fun x : ℕ => x + 1) ⊆ (lcmUpTo n).divisors := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    rw [Finset.mem_range] at hi
    rw [Nat.mem_divisors]
    exact ⟨dvd_lcmUpTo (by omega) (by omega), hpos.ne'⟩
  -- Re-express the harmonic sum as a sum over that image.
  have himg :
      (∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ))
        = ∑ d ∈ (Finset.range n).image (fun x : ℕ => x + 1), (1 / (d : ℝ)) := by
    rw [Finset.sum_image (by intro x _ y _ h; dsimp only at h; omega)]
    apply Finset.sum_congr rfl
    intro i _; push_cast; ring
  rw [himg, sigma_div_eq_sum_inv (lcmUpTo n) hpos]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)

/-- **Main theorem.** The abundancy ratio `σ(m)/m` is unbounded: along the explicit
    sequence `mₙ = lcm(1, …, n)` it tends to `+∞`. This is the analytic engine that
    the parent (`erdos-1054-oq-01`) axiomatized via Gronwall/Mertens — here it is
    derived with **0 axioms** from the divergence of the harmonic series alone. -/
theorem sigma_ratio_tendsto_atTop :
    Tendsto (fun n => (sigma (lcmUpTo n) : ℝ) / (lcmUpTo n)) atTop atTop :=
  tendsto_atTop_mono harmonic_le_sigma_ratio
    Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- **Corollary (the parent's blocking step).** Since `f(σ(mₙ)) ≤ mₙ`, we have
    `f(σ(mₙ))/σ(mₙ) ≤ mₙ/σ(mₙ) = 1/(σ(mₙ)/mₙ) → 0`. We record the upper bound
    `mₙ/σ(mₙ) → 0`, which forces `liminf f(n)/n = 0` along this sequence. -/
theorem f_sigma_ratio_tendsto_zero :
    Tendsto (fun n => (lcmUpTo n : ℝ) / (sigma (lcmUpTo n))) atTop (𝓝 0) := by
  have hev : (fun n => (lcmUpTo n : ℝ) / (sigma (lcmUpTo n)))
      =ᶠ[atTop] (fun n => ((sigma (lcmUpTo n) : ℝ) / (lcmUpTo n))⁻¹) := by
    filter_upwards [eventually_atTop.mpr ⟨1, fun n _ => trivial⟩] with n _
    rw [inv_div]
  rw [tendsto_congr' hev]
  exact (sigma_ratio_tendsto_atTop).inv_tendsto_atTop

/-- The abundancy ratio is in particular **unbounded**: for every bound `C` there is
    an `n` with `σ(lcmUpTo n)/(lcmUpTo n) > C`. -/
theorem sigma_ratio_unbounded (C : ℝ) :
    ∃ n : ℕ, (sigma (lcmUpTo n) : ℝ) / (lcmUpTo n) > C := by
  have h := (sigma_ratio_tendsto_atTop).eventually_gt_atTop C
  obtain ⟨n, hn⟩ := h.exists
  exact ⟨n, hn⟩

end Erdos1054AlmostAllOQ0103
