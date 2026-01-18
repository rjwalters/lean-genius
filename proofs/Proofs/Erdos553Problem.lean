/-
  Erdős Problem #553: Multi-Color Ramsey Asymptotics

  Source: https://erdosproblems.com/553
  Status: SOLVED (Alon-Rödl, 2005)

  Statement:
  Let R(3,3,n) denote the smallest integer m such that if we 3-color the
  edges of K_m, then there is either a monochromatic triangle in one of
  the first two colors or a monochromatic K_n in the third color.

  Define R(3,n) similarly but with two colors (monochromatic triangle
  or monochromatic K_n).

  Show that R(3,3,n) / R(3,n) → ∞ as n → ∞.

  Solution (Alon-Rödl 2005):
  - R(3,3,n) ≍ n³ (log n)^O(1)
  - R(3,n) ≪ n² / log n  (Shearer 1983)
  - Therefore R(3,3,n) / R(3,n) ≍ n (log n)^O(1) → ∞

  The key insight is that the third color in R(3,3,n) allows much denser
  triangle-free graphs, dramatically increasing the threshold.

  Related: Problem #925, Ramsey Theory Problem #22
-/

import Mathlib

open Finset Function Set

/-! ## Graph Coloring Basics -/

/-- An edge coloring of a complete graph on n vertices with k colors -/
def EdgeColoring (n k : ℕ) := Fin n × Fin n → Fin k

/-- A coloring is symmetric (for undirected edges) -/
def EdgeColoring.IsSymmetric {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∀ i j : Fin n, c (i, j) = c (j, i)

/-- A set of vertices forms a monochromatic clique in color col -/
def IsMonochromaticClique {n k : ℕ} (c : EdgeColoring n k)
    (S : Finset (Fin n)) (col : Fin k) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c (i, j) = col

/-- A monochromatic triangle in color col -/
def HasMonochromaticTriangle {n k : ℕ} (c : EdgeColoring n k) (col : Fin k) : Prop :=
  ∃ a b d : Fin n, a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
    c (a, b) = col ∧ c (b, d) = col ∧ c (a, d) = col

/-- A monochromatic clique of size m in color col -/
def HasMonochromaticClique {n k : ℕ} (c : EdgeColoring n k) (col : Fin k) (m : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = m ∧ IsMonochromaticClique c S col

/-! ## Two-Color Ramsey Number R(3,n) -/

/-- R(3,n): smallest m such that any 2-coloring of K_m has either
    a monochromatic triangle in color 0 or a monochromatic K_n in color 1 -/
def R_3_n (n : ℕ) : ℕ :=
  Nat.find (ramsey_3_n_exists n)
where
  ramsey_3_n_exists (n : ℕ) : ∃ m : ℕ, ∀ c : EdgeColoring m 2,
      c.IsSymmetric → HasMonochromaticTriangle c 0 ∨ HasMonochromaticClique c 1 n := by
    sorry

/-- Alternative definition via Prop (avoids Nat.find) -/
def IsR3n (m n : ℕ) : Prop :=
  (∀ c : EdgeColoring m 2, c.IsSymmetric →
    HasMonochromaticTriangle c 0 ∨ HasMonochromaticClique c 1 n) ∧
  (∀ m' < m, ∃ c : EdgeColoring m' 2, c.IsSymmetric ∧
    ¬HasMonochromaticTriangle c 0 ∧ ¬HasMonochromaticClique c 1 n)

/-! ## Three-Color Ramsey Number R(3,3,n) -/

/-- R(3,3,n): smallest m such that any 3-coloring of K_m has either
    a monochromatic triangle in color 0 or 1, or a monochromatic K_n in color 2 -/
def R_3_3_n (n : ℕ) : ℕ :=
  Nat.find (ramsey_3_3_n_exists n)
where
  ramsey_3_3_n_exists (n : ℕ) : ∃ m : ℕ, ∀ c : EdgeColoring m 3,
      c.IsSymmetric → HasMonochromaticTriangle c 0 ∨
        HasMonochromaticTriangle c 1 ∨ HasMonochromaticClique c 2 n := by
    sorry

/-- Alternative definition via Prop -/
def IsR33n (m n : ℕ) : Prop :=
  (∀ c : EdgeColoring m 3, c.IsSymmetric →
    HasMonochromaticTriangle c 0 ∨ HasMonochromaticTriangle c 1 ∨
    HasMonochromaticClique c 2 n) ∧
  (∀ m' < m, ∃ c : EdgeColoring m' 3, c.IsSymmetric ∧
    ¬HasMonochromaticTriangle c 0 ∧ ¬HasMonochromaticTriangle c 1 ∧
    ¬HasMonochromaticClique c 2 n)

/-! ## Known Bounds -/

/-- Shearer's bound (1983): R(3,n) ≤ C n² / log n for some constant C -/
theorem shearer_upper_bound : ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 2, (R_3_n n : ℝ) ≤ C * n^2 / Real.log n := by
  sorry

/-- Lower bound: R(3,n) ≥ c n² / (log n)² for some constant c -/
theorem R_3_n_lower_bound : ∃ c : ℝ, c > 0 ∧
    ∀ n ≥ 2, (R_3_n n : ℝ) ≥ c * n^2 / (Real.log n)^2 := by
  sorry

/-- Alon-Rödl (2005): R(3,3,n) ≍ n³ (log n)^O(1) -/
theorem alon_rodl_upper_bound : ∃ C : ℝ, ∃ k : ℕ, C > 0 ∧
    ∀ n ≥ 2, (R_3_3_n n : ℝ) ≤ C * n^3 * (Real.log n)^k := by
  sorry

theorem alon_rodl_lower_bound : ∃ c : ℝ, ∃ k : ℕ, c > 0 ∧
    ∀ n ≥ 2, (R_3_3_n n : ℝ) ≥ c * n^3 / (Real.log n)^k := by
  sorry

/-! ## The Main Result -/

/-- The ratio R(3,3,n) / R(3,n) tends to infinity -/
def RatioTendsToInfinity : Prop :=
  ∀ M : ℝ, M > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (R_3_3_n n : ℝ) / (R_3_n n : ℝ) > M

/-- Main theorem: R(3,3,n) / R(3,n) → ∞ as n → ∞
    This follows from the bounds:
    - R(3,3,n) ≥ c n³ / (log n)^k
    - R(3,n) ≤ C n² / log n
    So R(3,3,n)/R(3,n) ≥ (c/C) · n · (log n)^(1-k) → ∞ -/
theorem erdos_553_main : RatioTendsToInfinity := by
  sorry

/-! ## Intuition: Why the Third Color Helps -/

/-- In a 2-coloring, avoiding a triangle in color 0 means color-0 edges
    form a triangle-free graph, which by Turán has ≤ n²/4 edges.
    This limits how long we can avoid a K_n in color 1. -/
theorem triangle_free_turán (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    G.edgeFinset.card ≤ n^2 / 4 := by
  sorry

/-- In a 3-coloring, we can use two colors for triangle-free graphs.
    The union of two triangle-free graphs can have up to n²/2 edges,
    giving much more room for the third color. -/
theorem two_triangle_free_union (G H : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (hH : H.CliqueFree 3) :
    G.edgeFinset.card + H.edgeFinset.card ≤ n^2 / 2 := by
  sorry

/-! ## Connection to Off-Diagonal Ramsey Numbers -/

/-- Standard off-diagonal Ramsey number R(s,t) -/
def R (s t : ℕ) : ℕ :=
  Nat.find (ramsey_exists s t)
where
  ramsey_exists (s t : ℕ) : ∃ m : ℕ, ∀ c : EdgeColoring m 2,
      c.IsSymmetric → HasMonochromaticClique c 0 s ∨ HasMonochromaticClique c 1 t := by
    sorry

/-- R(3,3) = 6 (classical result) -/
theorem ramsey_3_3 : R 3 3 = 6 := by
  sorry

/-- R(3,n) is the smallest m with: any 2-coloring has K₃ in red or Kₙ in blue -/
theorem R_3_n_eq : ∀ n, R_3_n n = R 3 n := by
  sorry

/-! ## Asymptotic Notation -/

/-- f ≍ g means c₁ g ≤ f ≤ c₂ g for constants c₁, c₂ > 0 -/
def AsymptoticEquiv (f g : ℕ → ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ,
    ∀ n ≥ N, c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

notation:50 f " ≍ " g => AsymptoticEquiv f g

/-- The Alon-Rödl result in asymptotic notation -/
theorem alon_rodl : ∃ k : ℕ,
    (fun n => (R_3_3_n n : ℝ)) ≍ (fun n => n^3 * (Real.log n)^k) := by
  sorry

/-- Shearer's result in asymptotic notation -/
theorem shearer : (fun n => (R_3_n n : ℝ)) ≍ (fun n => n^2 / Real.log n) := by
  sorry

/-! ## Generalizations -/

/-- General multi-color Ramsey number R(k₁, k₂, ..., kᵣ) -/
def MultiColorRamsey (params : List ℕ) : ℕ := by
  sorry

/-- Erdős-Sós conjecture about general ratios -/
def erdosSosGeneralization : Prop :=
  ∀ r s : ℕ, r < s →
    ∀ M : ℝ, M > 0 → ∃ N : ℕ, ∀ n ≥ N,
      (MultiColorRamsey (List.replicate s 3 ++ [n]) : ℝ) /
      (MultiColorRamsey (List.replicate r 3 ++ [n]) : ℝ) > M

/-! ## Main Result Summary -/

/-- Erdős Problem #553: SOLVED by Alon-Rödl (2005)

    The ratio R(3,3,n)/R(3,n) → ∞ because:
    - R(3,3,n) grows like n³ (with log factors)
    - R(3,n) grows like n²/log n

    The third color allows much denser triangle-avoidance,
    dramatically increasing the threshold for the off-diagonal clique. -/
theorem erdos_553 : RatioTendsToInfinity := erdos_553_main

#check erdos_553
#check alon_rodl_upper_bound
#check shearer_upper_bound
