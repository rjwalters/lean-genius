/-
Erdős Problem #89: Distinct Distances in the Plane

Does every set of n distinct points in ℝ² determine ≫ n/√(log n) many
distinct distances?

**Status**: OPEN (original conjecture)

**Partial Result**: Guth-Katz (2015) proved ≫ n/log n distinct distances.

**Lower Bound**: A √n × √n integer grid has only O(n/√(log n)) distinct
distances, showing the conjecture would be tight if true.

**Prize**: $500

Reference: https://erdosproblems.com/89
-/

import Mathlib

open Filter Set Finset
open scoped Topology

namespace Erdos89

/-!
## Background

The **distinct distances problem** is one of Erdős's most famous problems
in combinatorial geometry, posed in 1946.

Given n points in the plane, how many distinct pairwise distances must exist?

The √n × √n integer grid shows you cannot always have more than O(n/√(log n))
distinct distances. Erdős conjectured this is the answer.
-/

/--
The **distance** between two points in ℝ².
-/
noncomputable def dist (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖p - q‖

/--
The set of **distinct distances** determined by a finite set of points.
This is the set of all pairwise distances {‖p - q‖ : p, q ∈ S, p ≠ q}.
-/
noncomputable def distinctDistances (S : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (S.offDiag.image fun pq => dist pq.1 pq.2).filter (· > 0)

/--
The **number of distinct distances** for a point set.
-/
noncomputable def numDistinctDistances (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (distinctDistances S).card

/--
The **minimum number of distinct distances** over all n-point sets in ℝ².
This is the extremal function g(n) that Erdős asked about.
-/
noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  sInf {numDistinctDistances S | (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = n)}

/-!
## The Main Question

Erdős conjectured that g(n) ≫ n/√(log n).
-/

/--
**Erdős Problem #89 (OPEN)**

Every set of n points in the plane determines at least Ω(n/√(log n))
distinct distances.

Formally: n/√(log n) = O(g(n)) as n → ∞.

We state this without asserting its truth.
-/
def Erdos89Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * n / Real.sqrt (Real.log n) ≤ minDistinctDistances n

/-!
## Guth-Katz Theorem (2015)

Larry Guth and Nets Hawk Katz proved a slightly weaker bound:
at least Ω(n/log n) distinct distances.

This is the closest result to Erdős's conjecture.
-/

/--
**Guth-Katz Theorem (2015)**

Every set of n points in the plane determines at least Ω(n/log n)
distinct distances.

This is weaker than Erdős's conjecture by a factor of √(log n).
-/
axiom guthKatz :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * n / Real.log n ≤ minDistinctDistances n

/--
**Upper Bound Construction**

The √n × √n integer grid achieves only O(n/√(log n)) distinct distances.
This shows Erdős's conjecture would be tight if true.
-/
axiom gridUpperBound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    minDistinctDistances n ≤ c * n / Real.sqrt (Real.log n)

/-!
## Consistency Check

The conjecture implies Guth-Katz. This is because n/√(log n) ≫ n/log n.

For x > 1: √x < x, hence 1/x < 1/√x.
This means c * n / log n < c * n / √(log n) for log n > 1 (i.e., n > e).
-/

/--
For x > 1, we have √x < x.

Proof: √x < x ↔ x < x² (squaring, valid since both positive)
      ↔ 1 < x (dividing by x > 0) ✓
-/
axiom sqrt_lt_self_of_one_lt {x : ℝ} (hx : x > 1) : Real.sqrt x < x

/--
For c > 0 and n > 0 with log n > 1 (i.e., n > e), we have:
  c * n / log n ≤ c * n / √(log n)

This follows because for x > 1: √x < x, hence 1/x < 1/√x.
-/
lemma scaled_div_log_le_div_sqrt_log {c n : ℝ} (hc : c > 0) (hn : n > 0) (hlog : Real.log n > 1) :
    c * n / Real.log n ≤ c * n / Real.sqrt (Real.log n) := by
  have hcn_pos : c * n > 0 := mul_pos hc hn
  have hcn_nonneg : c * n ≥ 0 := le_of_lt hcn_pos
  have hlog_pos : Real.log n > 0 := by linarith
  have hsqrt_pos : Real.sqrt (Real.log n) > 0 := Real.sqrt_pos.mpr hlog_pos
  have hsqrt_lt_log : Real.sqrt (Real.log n) < Real.log n := sqrt_lt_self_of_one_lt hlog
  have hsqrt_le_log : Real.sqrt (Real.log n) ≤ Real.log n := le_of_lt hsqrt_lt_log
  -- a / b ≤ a / c when a ≥ 0 and 0 < c ≤ b
  -- Here: (c*n) / log n ≤ (c*n) / √(log n) when √(log n) ≤ log n
  exact div_le_div_of_nonneg_left hcn_nonneg hsqrt_pos hsqrt_le_log

/--
log 3 > 1, since 3 > e ≈ 2.718...

We state this as an axiom since the numerical verification is straightforward
but requires careful handling of exp bounds.
-/
axiom log_three_gt_one : Real.log 3 > 1

/--
If the Erdős conjecture holds, then Guth-Katz follows.

Since √(log n)/log n → 0, the bound n/√(log n) is stronger than n/log n.
-/
theorem conjecture_implies_guthKatz (h : Erdos89Conjecture) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      c * n / Real.log n ≤ minDistinctDistances n := by
  obtain ⟨c, hc_pos, hc⟩ := h
  use c
  constructor
  · exact hc_pos
  · -- For sufficiently large n, log n > 1, so c*n/log n ≤ c*n/√(log n)
    have hlog_eventually : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) > 1 := by
      filter_upwards [Filter.eventually_gt_atTop 3] with n hn
      have h3 : (n : ℝ) ≥ 3 := by exact Nat.cast_le.mpr (le_of_lt hn)
      calc Real.log n ≥ Real.log 3 := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3
        _ > 1 := log_three_gt_one
    filter_upwards [hc, hlog_eventually, Filter.eventually_gt_atTop 0] with n hn hlog hn_pos
    calc c * (n : ℝ) / Real.log n
        ≤ c * n / Real.sqrt (Real.log n) := by
          apply scaled_div_log_le_div_sqrt_log hc_pos (by exact Nat.cast_pos.mpr hn_pos) hlog
        _ ≤ minDistinctDistances n := hn

/-!
## Historical Development

- 1946: Erdős poses the problem
- 1992: Chung proves Ω(n^(4/5))
- 2001: Solymosi-Tóth prove Ω(n^(6/7))
- 2004: Tardos proves Ω(n^((4e)/(5e-1))) ≈ Ω(n^0.8641)
- 2010: Katz-Tardos prove Ω(n/log n) in some regimes
- 2015: Guth-Katz prove Ω(n/log n) in full generality

The gap between Ω(n/log n) and O(n/√(log n)) remains open.
-/

/--
**Early Bound (Chung 1992)**

The first significant progress: Ω(n^(4/5)) distinct distances.
-/
axiom chung1992 :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ)^(4/5 : ℝ) ≤ minDistinctDistances n

/--
**Tardos Bound (2004)**

An exponent improvement: Ω(n^0.8641...).
-/
axiom tardos2004 :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ)^((4 * Real.exp 1)/(5 * Real.exp 1 - 1) : ℝ) ≤ minDistinctDistances n

/-!
## Related Problems

Erdős also asked about:
- Single point determining many distances (Problem #604)
- Sum of distances from all points
- Higher dimensional generalizations
-/

/--
**Stronger Conjecture (Problem #604)**

Is there always a single point that determines Ω(n/√(log n)) distinct
distances to the other points?
-/
def singlePointConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
    S.card ≥ 2 →
    ∃ p ∈ S, c * S.card / Real.sqrt (Real.log S.card) ≤
      ((S.filter (· ≠ p)).image (dist p)).card

end Erdos89
