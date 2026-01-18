/-
  Erdős Problem #1089: Distinct Distances in Higher Dimensions

  Source: https://erdosproblems.com/1089
  Status: OPEN

  Statement:
  Let g_d(n) be minimal such that every collection of g_d(n) points in ℝ^d
  determines at least n distinct distances. Estimate g_d(n). In particular,
  does lim_{d→∞} g_d(n)/d^{n-1} exist?

  Background:
  This is the higher-dimensional generalization of the distinct distances
  problem. In ℝ^d, we ask: how many points guarantee n distinct pairwise
  distances? The function g_d(n) captures this threshold.

  Known results:
  • g_1(3) = 4 (4 points on a line give 3 distances)
  • g_2(3) = 6 (6 points in plane guarantee 3 distinct distances)
  • g_3(3) = 7 (Croft 1962)
  • Lower bound: g_d(n) ≫ d^{n-1} (Erdős, "easy")
  • Upper bound: g_d(n) ≤ c^{d^{1-b_n}} for some constants (Erdős-Straus)
  • Cube bound: g_d(d+1) > 2^d (vertices of d-cube have ≤ d distances)

  The main question: does g_d(n)/d^{n-1} converge as d → ∞?

  References:
  [Er75f] Erdős, "Problems and results in combinatorial geometry" (1975)
  [Cr62] Croft, "On a claim of Erdős" (1962)

  Tags: discrete-geometry, distinct-distances, high-dimensions, open-problem
-/

import Mathlib

open Set Finset

/-
## Points and Distances

Points in d-dimensional Euclidean space and their pairwise distances.
-/

/-- A point in d-dimensional Euclidean space -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Euclidean distance between two points -/
noncomputable def dist {d : ℕ} (p q : Point d) : ℝ :=
  ‖p - q‖

/-- The set of distinct distances determined by a point set -/
noncomputable def distinctDistances {d : ℕ} (P : Finset (Point d)) : Finset ℝ :=
  (P.product P).image (fun (p, q) => dist p q) |>.filter (· > 0)

/-- Number of distinct distances -/
noncomputable def numDistinctDistances {d : ℕ} (P : Finset (Point d)) : ℕ :=
  (distinctDistances P).card

/-
## The Function g_d(n)

g_d(n) is the minimal number of points guaranteeing n distinct distances.
-/

/-- A point set determines at least n distinct distances -/
def determinesNDistances {d : ℕ} (P : Finset (Point d)) (n : ℕ) : Prop :=
  numDistinctDistances P ≥ n

/-- g_d(n): minimal m such that every m-point set determines ≥ n distances -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (Point d), P.card = m → determinesNDistances P n}

/-- g is well-defined for n ≥ 1 -/
axiom g_well_defined :
  ∀ d n : ℕ, n ≥ 1 → ∃ m : ℕ, ∀ P : Finset (Point d), P.card = m → determinesNDistances P n

/-
## Small Cases

Known exact values of g_d(n).
-/

/-- g_1(3) = 4: four points on a line give 3 distinct distances -/
axiom g_1_3 : g 1 3 = 4

/-- g_2(3) = 6: six points in the plane guarantee 3 distinct distances -/
axiom g_2_3 : g 2 3 = 6

/-- g_3(3) = 7 (Croft 1962) -/
axiom g_3_3 : g 3 3 = 7

/-- Trivial: g_d(1) = 2 (any two distinct points give 1 distance) -/
theorem g_d_1 (d : ℕ) (hd : d ≥ 1) : g d 1 = 2 := by
  sorry

/-- Trivial: g_d(2) = 3 for d ≥ 1 -/
axiom g_d_2 : ∀ d ≥ 1, g d 2 = 3

/-
## Lower Bound

g_d(n) ≫ d^{n-1} via cube construction.
-/

/-- The vertices of the d-dimensional unit cube -/
def cubeVertices (d : ℕ) : Finset (Point d) := sorry

/-- Cube has 2^d vertices -/
axiom cube_card : ∀ d : ℕ, (cubeVertices d).card = 2^d

/-- Cube vertices determine at most d distinct distances -/
axiom cube_distances :
  ∀ d : ℕ, numDistinctDistances (cubeVertices d) ≤ d

/-- Cube gives lower bound: g_d(d+1) > 2^d -/
theorem cube_lower_bound (d : ℕ) : g d (d + 1) > 2^d := by
  sorry

/-- General lower bound: g_d(n) ≥ c·d^{n-1} for some constant c -/
axiom erdos_lower_bound :
  ∀ n ≥ 2, ∃ c : ℝ, c > 0 ∧ ∀ d ≥ 1, (g d n : ℝ) ≥ c * d^(n - 1 : ℕ)

/-
## Upper Bound

Erdős-Straus upper bound.
-/

/-- Erdős-Straus bound: g_d(n) ≤ c^{d^{1-b_n}} -/
axiom erdos_straus_upper_bound :
  ∀ n ≥ 2, ∃ c b : ℝ, c > 1 ∧ b > 0 ∧
    ∀ d ≥ 1, (g d n : ℝ) ≤ c^(d^(1 - b) : ℝ)

/-
## The Main Conjecture

Does g_d(n)/d^{n-1} converge as d → ∞?
-/

/-- The normalized ratio g_d(n)/d^{n-1} -/
noncomputable def gRatio (d n : ℕ) : ℝ :=
  (g d n : ℝ) / d^(n - 1 : ℕ)

/-- Conjecture: the limit exists for each fixed n -/
def erdos1089Conjecture (n : ℕ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun d => gRatio d n) Filter.atTop (nhds L)

/-- Weaker: is the ratio bounded? -/
def ratioIsBounded (n : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ d ≥ 1, gRatio d n ≤ C

/-- Lower bound implies ratio is bounded below -/
theorem ratio_bounded_below (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ ∀ d ≥ 1, gRatio d n ≥ c := by
  obtain ⟨c, hc, h⟩ := erdos_lower_bound n hn
  exact ⟨c, hc, fun d hd => by simp only [gRatio]; linarith [h d hd]⟩

/-
## Monotonicity Properties

How g_d(n) changes with d and n.
-/

/-- g_d(n) is increasing in n -/
axiom g_mono_n :
  ∀ d n₁ n₂ : ℕ, n₁ ≤ n₂ → g d n₁ ≤ g d n₂

/-- g_d(n) is generally increasing in d -/
axiom g_mono_d :
  ∀ d₁ d₂ n : ℕ, d₁ ≤ d₂ → n ≥ 2 → g d₁ n ≤ g d₂ n

/-
## Connection to f_d(n)

The inverse function from problem #1083.
-/

/-- f_d(n) = max distinct distances from n points in ℝ^d -/
noncomputable def f (d n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (Point d), P.card = n ∧ numDistinctDistances P = k}

/-- Relationship: g_d(n) = min{m : f_d(m) ≥ n} -/
axiom g_f_relationship :
  ∀ d n : ℕ, n ≥ 1 → g d n = sInf {m : ℕ | f d m ≥ n}

/-
## The Open Problem

The limit question remains unresolved.
-/

/-- The main open question -/
def erdos1089OpenProblem : Prop :=
  ∀ n ≥ 2, erdos1089Conjecture n

#check g
#check gRatio
#check erdos1089Conjecture
#check erdos_lower_bound
#check erdos_straus_upper_bound
