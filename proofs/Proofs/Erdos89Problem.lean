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
-/

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
  · filter_upwards [hc] with n hn
    calc c * (n : ℝ) / Real.log n
        ≤ c * n / Real.sqrt (Real.log n) := by
          sorry -- n/log n ≤ n/√(log n) for large n
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
