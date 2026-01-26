/-!
# Erdős Problem #1084: Unit Distances Among Separated Points

Let f_d(n) be the maximum number of pairs at distance exactly 1 among
n points in ℝ^d with all pairwise distances ≥ 1. Estimate f_d(n).

## Key Results

- d = 1: f_1(n) = n - 1
- d = 2: f_2(n) = ⌊3n - √(12n-3)⌋ (Harborth, 1974)
- d = 2: f_2(n) < 3n - c√n (Erdős)
- d = 3: 6n - c₁n^{2/3} < f_3(n) < 6n - c₂n^{2/3} (conjectured,
  upper bound by Bezdek–Reid 2013)
- General: (d - o(1))n ≤ f_d(n) ≤ 2^{O(d)} · n

## References

- Erdős (1946, 1975)
- Harborth (1974): exact formula for d = 2
- Bezdek–Reid (2013): d = 3 upper bound
- <https://erdosproblems.com/1084>
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A configuration of n points in ℝ^d where all pairwise distances are ≥ 1. -/
structure SeparatedConfig (d n : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin d)
  separated : ∀ i j : Fin n, i ≠ j →
    dist (points i) (points j) ≥ 1

/-- The number of unit-distance pairs in a configuration. -/
noncomputable def unitDistPairs {d n : ℕ} (C : SeparatedConfig d n) : ℕ :=
  Finset.card (Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ dist (C.points p.1) (C.points p.2) = 1)
    Finset.univ)

/-- f_d(n): maximum number of unit-distance pairs among n separated
    points in ℝ^d. -/
axiom maxUnitDistPairs (d n : ℕ) : ℕ

/-! ## One-Dimensional Case -/

/-- f_1(n) = n - 1: on the line, separated points at consecutive
    unit intervals give n-1 unit pairs, and this is optimal. -/
axiom f1_exact (n : ℕ) (hn : n ≥ 1) :
  maxUnitDistPairs 1 n = n - 1

/-! ## Two-Dimensional Case -/

/-- Erdős's upper bound: f_2(n) < 3n - c√n for some c > 0.
    The leading coefficient 3 comes from the triangular lattice
    where each point has at most 6 unit neighbors. -/
axiom f2_upper_erdos :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (maxUnitDistPairs 2 n : ℝ) < 3 * n - c * Real.sqrt n

/-- Harborth's exact formula (1974):
    f_2(n) = ⌊3n - √(12n - 3)⌋ for all n ≥ 2. -/
axiom harborth_exact (n : ℕ) (hn : n ≥ 2) :
  maxUnitDistPairs 2 n = Nat.floor (3 * (n : ℝ) - Real.sqrt (12 * n - 3))

/-- The triangular lattice achieves the maximum: a hexagonal patch
    of n points in the triangular lattice with unit spacing
    realizes f_2(n) unit pairs. -/
axiom triangular_lattice_optimal (n : ℕ) (hn : n ≥ 2) :
  ∃ C : SeparatedConfig 2 n, unitDistPairs C = maxUnitDistPairs 2 n

/-- Upper bound: f_2(n) < 3n (each point has ≤ 6 unit neighbors
    in the plane, giving ≤ 6n/2 = 3n pairs). -/
axiom f2_trivial_upper (n : ℕ) (hn : n ≥ 1) :
  maxUnitDistPairs 2 n < 3 * n

/-! ## Three-Dimensional Case -/

/-- Leading coefficient in d=3: f_3(n) ~ 6n.
    Each point in ℝ³ with pairwise distances ≥ 1 has at most 12
    unit neighbors (kissing number), giving ≤ 12n/2 = 6n pairs. -/
axiom f3_leading :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    |(maxUnitDistPairs 3 n : ℝ) / n - 6| < ε

/-- Bezdek–Reid (2013): f_3(n) < 6n - 0.926 · n^(2/3). -/
axiom bezdek_reid_upper :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (maxUnitDistPairs 3 n : ℝ) < 6 * n - c * (n : ℝ) ^ (2/3 : ℝ)

/-- **Erdős conjecture for d=3**: f_3(n) = 6n - Θ(n^{2/3}).
    Both upper and lower bounds have the n^{2/3} correction. -/
axiom erdos_1084_d3_conjecture :
  ∃ c₁ c₂ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
      6 * (n : ℝ) - c₁ * (n : ℝ) ^ (2/3 : ℝ) ≤ (maxUnitDistPairs 3 n : ℝ) ∧
      (maxUnitDistPairs 3 n : ℝ) ≤ 6 * (n : ℝ) - c₂ * (n : ℝ) ^ (2/3 : ℝ)

/-! ## General Dimension -/

/-- Lower bound: f_d(n) ≥ (d - o(1)) · n.
    Lattice packings in ℝ^d give configurations where each point
    has ≈ 2d unit neighbors. -/
axiom fd_lower_general :
  ∀ d : ℕ, d ≥ 1 → ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
      (maxUnitDistPairs d n : ℝ) ≥ ((d : ℝ) - ε) * n

/-- Upper bound: f_d(n) ≤ 2^{O(d)} · n.
    The kissing number in dimension d is 2^{O(d)}, bounding the
    maximum degree in the unit-distance graph. -/
axiom fd_upper_general :
  ∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d ≥ 1 → ∀ n : ℕ, n ≥ 1 →
    (maxUnitDistPairs d n : ℝ) ≤ (2 : ℝ) ^ (C * d) * n
