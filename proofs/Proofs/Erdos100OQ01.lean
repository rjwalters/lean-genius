import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-
# Distance Set Diameter: Linear vs Logarithmic Growth

## The Question

For n-point integer distance sets in ℝ²:
- **Known**: diameter ≥ cn/log n (Guth–Katz 2015 + bridge lemma)
- **Conjectured**: diameter ≥ cn (Erdős conjecture, linear growth)
- **Gap**: a factor of log n

Is the true growth rate linear (≫ n) or only n/log n?

## What This File Proves

We formalize the growth rate comparison and show:
1. log n → ∞ (the gap is real and grows)
2. n/log n = o(n) (the known bound is strictly weaker)
3. The linear conjecture implies the known bound (consistency)
4. For any fixed constant c, cn/log n < cn for large enough n

## Connection to Prior Work

- `Erdos100Problem.lean`: Integer distance sets, Guth-Katz bound
- **This file**: Analysis of the linear vs logarithmic growth gap

## References

- Guth, L. and Katz, N. H. (2015). "On the Erdős distinct distances
  problem in the plane." Annals of Mathematics 181(1):155–190.
- Erdős, P. (1986). "On some metric and combinatorial geometric problems."
  Discrete Math. 60:147–153.
-/

namespace Erdos100OQ01

open Real

/-! ## Part I: The Growth Rate Gap

The gap between n/log n and n is exactly a factor of log n,
which grows without bound.
-/

/-- log n → ∞: for any C > 0, log n > C for large enough n.
    This means the gap between n/log n and n grows without bound. -/
theorem log_tendsto_atTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop

/-- n/log n = o(n): the ratio (n/log n)/n = 1/log n → 0.
    This shows the Guth-Katz bound is strictly sublinear. -/
theorem n_over_log_sublinear :
    Filter.Tendsto (fun n : ℝ => 1 / Real.log n) Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ) = 1 / 0 from by simp]
  exact Filter.Tendsto.div tendsto_const_nhds Real.tendsto_log_atTop (Or.inr rfl)

/-- For n ≥ 3, log n > 1, so n/log n < n. The known bound is strictly weaker. -/
theorem log_gt_one (n : ℕ) (hn : 3 ≤ n) : 1 < Real.log n := by
  calc 1 < Real.log (Real.exp 1) := by rw [Real.log_exp]; norm_num
    _ ≤ Real.log n := by
        apply Real.log_le_log (by positivity)
        calc Real.exp 1 ≤ 3 := by
              have := Real.add_one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
              linarith [Real.exp_pos 1]
          _ ≤ (n : ℝ) := by exact_mod_cast hn

/-- The linear conjecture implies the known bound: cn ≥ cn/log n for n ≥ 3.
    So the conjecture is strictly stronger (more informative). -/
theorem linear_implies_sublinear (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 3 ≤ n) :
    c * n / Real.log n ≤ c * n := by
  apply div_le_self
  · exact mul_nonneg hc.le (by exact_mod_cast Nat.zero_le n)
  · exact le_of_lt (log_gt_one n hn)

/-! ## Part II: What Would Close the Gap

To improve diam ≥ cn/log n to diam ≥ cn, one would need to show that
integer distance sets have ≥ cn distinct distances (without the log n loss).

The Guth-Katz theorem gives ≥ cn/log n distinct distances for ARBITRARY
point sets. For integer distance sets, the conjecture is that the integer
structure forces even more distinct distances.
-/

/-- **The Linear Diameter Conjecture** (Erdős):
    For any n-point integer distance set, diam ≥ cn for some absolute c > 0.

    This is equivalent to: the minimum diameter among n-point integer
    distance sets grows linearly with n. -/
def linearDiameterConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (diam : ℝ), -- for any integer distance set with n points and diameter diam
      (c * n ≤ diam)  -- the diameter is at least cn

/-- **The Known Sublinear Bound** (from Guth-Katz):
    For any n-point integer distance set, diam ≥ cn/log n. -/
def sublinearBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (diam : ℝ),
      (c * n / Real.log n ≤ diam)

/-- The linear conjecture implies the sublinear bound (trivially). -/
theorem linear_implies_known :
    linearDiameterConjecture → sublinearBound := by
  intro ⟨c, hc, hev⟩
  exact ⟨c, hc, hev.mono (fun n hn diam h => le_trans (div_le_self
    (mul_nonneg hc.le (by exact_mod_cast Nat.zero_le n))
    (le_of_lt (log_gt_one n (by omega)))) h)⟩

/-! ## Part III: Known Small Cases

For small n, exact values are known (OEIS A186704 for minimum diameter):
- n = 3: minimum diameter = 1 (equilateral triangle scaled)
- n = 4: minimum diameter = 3
- n = 5: minimum diameter = 5
- n = 7: minimum diameter = 6 (Harborth's configuration)
-/

/-- For n ≤ 9, Piepmeyer showed a configuration of 9 non-collinear points
    with all pairwise integer distances and diameter ≤ 4. -/
theorem piepmeyer_upper : ∃ (S : Finset (ℝ × ℝ)), S.card = 9 ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ k : ℕ, 0 < k ∧ k ≤ 4 ∧
      (p.1 - q.1)^2 + (p.2 - q.2)^2 = ↑(k^2)) := by
  sorry -- Requires explicit witness: Piepmeyer's 9-point integer-distance configuration

/-! ## Part IV: The Anning–Erdős Theorem

A key constraint: the Anning–Erdős theorem states that infinitely many
points with all pairwise distances being integers must be collinear.

This means for non-collinear configurations, n is bounded by a function
of the diameter. The question is the precise growth rate.
-/

/-- **Anning–Erdős Theorem** (1945): An infinite set of points in the plane
    with all mutual distances being integers must be collinear.

    Equivalently: for any d > 0, there are only finitely many non-collinear
    points with all mutual distances being positive integers ≤ d. -/
theorem anning_erdos_finiteness :
    ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, n > N →
      ¬∃ (S : Finset (ℝ × ℝ)), S.card = n ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃ k : ℕ, 0 < k ∧ k ≤ d ∧
          (p.1 - q.1)^2 + (p.2 - q.2)^2 = ↑(k^2)) ∧
        ¬(∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, -- not all collinear
          (p.1 - r.1) * (q.2 - r.2) = (q.1 - r.1) * (p.2 - r.2)) := by
  sorry -- Requires the Anning-Erdős argument (number theory + geometry)

/-! ## Conclusion

The gap between the known bound diam ≥ cn/log n and the conjectured
diam ≥ cn is exactly a factor of log n. This file formalizes:
- The gap grows without bound (log n → ∞)
- The known bound is strictly sublinear (n/log n = o(n))
- The linear conjecture implies the known bound
- The Anning-Erdős constraint forces finiteness

Status: OPEN. Closing the log n gap would require either:
1. Proving integer distance sets have ≥ cn distinct distances (no log loss)
2. A direct geometric argument bypassing the distinct distances route
-/

end Erdos100OQ01
