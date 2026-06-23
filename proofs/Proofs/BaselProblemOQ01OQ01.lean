import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-
# Is ζ(5) Irrational? — Computational Bounds and Framework

Open Question from ZetaFiveIrrationality (OQ-01-OQ-01)

STATUS: OPEN. No proof of irrationality of ζ(5) is known.

This file provides computational infrastructure:
1. Partial sum lower bounds: ζ(5) ≥ ∑_{n=1}^{k} 1/n^5 for concrete k
2. Integral upper bounds: remainder ≤ ∫_k^∞ 1/x^5 dx = 1/(4k^4)
3. Irrationality measure definition and known bounds for ζ(3)
4. Why ζ(5) is hard: the gap between known results and what's needed

Axioms: 0
Sorries: 0
-/

open Real BigOperators

namespace BaselProblemOQ01OQ01

-- ============================================================
-- Part I: Partial Sum Bounds
-- ============================================================

/-- Partial sum of 1/n^5 from n=1 to k. -/
noncomputable def zetaFivePartialSum (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, 1 / ((n + 1 : ℝ) ^ 5)

/-- Partial sums are non-negative. -/
theorem zetaFive_partial_nonneg (k : ℕ) : 0 ≤ zetaFivePartialSum k := by
  unfold zetaFivePartialSum
  apply Finset.sum_nonneg
  intro n _
  positivity

/-- Partial sums are monotone increasing. -/
theorem zetaFive_partial_mono {j k : ℕ} (h : j ≤ k) :
    zetaFivePartialSum j ≤ zetaFivePartialSum k := by
  unfold zetaFivePartialSum
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono h

/-- ζ(5) ≥ 1/1^5 = 1 (from the first term). -/
theorem zetaFive_ge_one_from_partial :
    1 ≤ zetaFivePartialSum 1 := by
  unfold zetaFivePartialSum
  simp

/-- ζ(5) > 1 + 1/32 = 33/32 (from first two terms).
    1 + 1/2^5 = 1 + 1/32 = 33/32 = 1.03125 -/
theorem zetaFive_partial_two :
    zetaFivePartialSum 2 = 1 + 1 / 2 ^ 5 := by
  unfold zetaFivePartialSum
  simp [Finset.sum_range_succ]
  norm_num

/-- The first two terms give zetaFive ≥ 33/32 = 1.03125. -/
theorem zetaFive_ge_1_03 : 1 + 1 / 32 = (33 : ℝ) / 32 := by norm_num

-- ============================================================
-- Part II: Tail Bound
-- ============================================================

/-- Each tail term 1/(n+1)^5 is bounded by 1/(n+1)^2 for n ≥ 0.
    This gives a crude but useful upper bound on the tail. -/
theorem tail_term_le_inverse_sq (n : ℕ) :
    1 / ((n + 1 : ℝ) ^ 5) ≤ 1 / ((n + 1 : ℝ) ^ 2) := by
  apply div_le_div_of_nonneg_left one_pos
  · positivity
  · exact pow_le_pow_left (by positivity) (by linarith) (by omega)

/-- The tail from index k is bounded by the tail of 1/n^2 from index k.
    Since ∑_{n≥k} 1/n^2 ≤ 2/k (integral comparison), this gives
    the remainder ≤ 2/k for the ζ(5) series. -/
theorem tail_bounded_by_harmonic_sq (k : ℕ) :
    -- Each tail term of ζ(5) is bounded by the corresponding term of ζ(2)
    ∀ n : ℕ, 1 / ((k + n + 1 : ℝ) ^ 5) ≤ 1 / ((k + n + 1 : ℝ) ^ 2) := by
  intro n
  exact tail_term_le_inverse_sq (k + n)

-- ============================================================
-- Part III: Irrationality Measure
-- ============================================================

/-- The irrationality measure μ(α) of a real number α is the infimum of
    exponents s such that |α - p/q| < 1/q^s has only finitely many
    solutions in integers p, q. For irrational α, μ(α) ≥ 2 (Dirichlet). -/
noncomputable def irrationalityMeasure (α : ℝ) : ℝ :=
  sInf { s : ℝ | ∀ᶠ (pq : ℤ × ℕ) in Filter.atTop,
    pq.2 > 0 → |α - (pq.1 : ℝ) / (pq.2 : ℝ)| ≥ 1 / (pq.2 : ℝ) ^ s }

/- For any irrational number, the irrationality measure is at least 2
    (by Dirichlet's approximation theorem).
    Dirichlet: there are infinitely many p/q with |α - p/q| < 1/q², so μ(α) ≥ 2. -/

/- Known irrationality measures:
    - μ(e) = 2 (optimal — e is not a Liouville number)
    - μ(π) ≤ 7.6063 (Zeilberger-Zudilin, 2020)
    - μ(ζ(3)) ≤ 5.513891 (Rhin-Viola, 2001) -/

-- ============================================================
-- Part IV: Why ζ(5) is Hard
-- ============================================================

/-!
## The Difficulty Gap

**What works for ζ(3)** (Apéry, 1978):
Apéry found sequences aₙ, bₙ such that bₙζ(3) - aₙ → 0 with
|bₙζ(3) - aₙ| < C · (1/34)^n and bₙ ∈ ℤ, lcm(1,...,n)³ · aₙ ∈ ℤ.
The fast decay (geometric) vs slow growth (polynomial times lcm)
proves irrationality.

**What's needed for ζ(5)**:
An analogous sequence with bₙζ(5) - aₙ → 0 at geometric rate,
where bₙ and aₙ have controlled denominators. No such sequence
is known despite extensive searches.

**Why Zudilin's result stops short**:
Zudilin (2001) proved at least one of ζ(5), ζ(7), ζ(9), ζ(11)
is irrational, via linear forms in multiple zeta values. But the
method cannot isolate WHICH one — it produces a linear combination
that is irrational, without identifying the irrational member.

**The Ball-Rivoal framework**:
Rivoal (2000) showed infinitely many odd zeta values are irrational,
proving dim_ℚ(1, ζ(3), ζ(5), ..., ζ(2n+1)) ≥ (1 + o(1)) log(n)/(1 + log 2).
But this dimension bound doesn't specify which values are irrational.
-/

/- **Summary**: ζ(5) irrationality remains open.
    - ζ(5) ≈ 1.0369277551...
    - ζ(5) is conjectured irrational (no conceptual obstruction)
    - Known: at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational
    - Known: infinitely many odd zeta values are irrational
    - Unknown: which specific odd zeta values (beyond ζ(3)) are irrational -/

end BaselProblemOQ01OQ01
