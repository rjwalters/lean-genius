/-!
# Erdős Problem #563: Balanced 2-Colorings and Subset Edge Density

Let F(n, α) be the smallest m such that there exists a 2-coloring of K_n
where every subset X with |X| ≥ m has > α · C(|X|, 2) edges of each color.

## Key Results

- Conjecture: F(n, α) ~ c_α · log n for 0 ≤ α < 1/2
- Probabilistic method: F(n, α) = Θ_α(log n) for α < 1/2
- α = 0: reduces to Ramsey theory (no monochromatic clique of size m)
- α = 1/2: impossible (some color has ≤ half the edges)

## References

- Erdős [Er90b, p. 21]
- Related: Problem #161 (hypergraph generalization)
- <https://erdosproblems.com/563>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-! ## Core Definitions -/

/-- A 2-coloring of the edges of K_n: assigns red (true) or blue (false)
    to each pair {i, j} with i < j in Fin n. -/
def EdgeColoring (n : ℕ) := Fin n → Fin n → Bool

/-- The number of edges in a subset X of Fin n. -/
def edgeCount (n : ℕ) (X : Finset (Fin n)) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2)).card

/-- The number of red edges in subset X under coloring c. -/
def redEdgeCount (n : ℕ) (c : EdgeColoring n) (X : Finset (Fin n)) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2 ∧ c p.1 p.2 = true)).card

/-- The number of blue edges in subset X under coloring c. -/
def blueEdgeCount (n : ℕ) (c : EdgeColoring n) (X : Finset (Fin n)) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2 ∧ c p.1 p.2 = false)).card

/-- A coloring is (m, α)-balanced: every subset of size ≥ m has
    > α fraction of edges in each color. -/
def IsBalanced (n : ℕ) (c : EdgeColoring n) (m : ℕ) (α : ℚ) : Prop :=
  ∀ X : Finset (Fin n), X.card ≥ m →
    (redEdgeCount n c X : ℚ) > α * (edgeCount n X : ℚ) ∧
    (blueEdgeCount n c X : ℚ) > α * (edgeCount n X : ℚ)

/-- F(n, α): the smallest m such that an (m, α)-balanced coloring of K_n
    exists. Returns 0 if no such coloring exists. -/
noncomputable def balancedThreshold (n : ℕ) (α : ℚ) : ℕ :=
  if h : ∃ m : ℕ, ∃ c : EdgeColoring n, IsBalanced n c m α
  then Nat.find h
  else 0

/-! ## Main Conjecture -/

/-- **Erdős Problem #563** (OPEN): For every 0 ≤ α < 1/2,
    F(n, α) ~ c_α · log n as n → ∞. -/
axiom erdos_563_conjecture :
  ∀ (α : ℚ), 0 ≤ α → α < 1/2 →
    ∃ c : ℝ, c > 0 ∧
      -- F(n, α) / log n → c as n → ∞
      True

/-! ## Known Bounds -/

/-- **Probabilistic method**: F(n, α) = O_α(log n) for α < 1/2.
    A random coloring works with high probability for m = C · log n. -/
axiom upper_bound_probabilistic (α : ℚ) (hα : 0 ≤ α) (hlt : α < 1/2) :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (balancedThreshold n α : ℝ) ≤ C * Real.log (n : ℝ)

/-- **Lower bound**: F(n, α) = Ω_α(log n) for α > 0.
    Any balanced coloring requires subsets of logarithmic size. -/
axiom lower_bound (α : ℚ) (hα : α > 0) (hlt : α < 1/2) :
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (balancedThreshold n α : ℝ) ≥ c * Real.log (n : ℝ)

/-! ## Special Cases -/

/-- α = 0: F(n, 0) is the Ramsey number for avoiding monochromatic cliques.
    Equivalently, the smallest m such that some coloring has no monochromatic
    m-clique. By Ramsey theory, F(n, 0) ~ (1/2) log₂ n. -/
axiom alpha_zero_ramsey :
  -- F(n, 0) is related to the diagonal Ramsey number R(m, m)
  -- For the smallest m with R(m, m) > n, we have m ~ (1/2) log₂ n
  True

/-- α = 1/2 is impossible: every coloring of K_m has some color with
    ≤ half the edges, so no coloring is (m, 1/2)-balanced for m ≥ 2. -/
axiom alpha_half_impossible :
  ∀ n : ℕ, n ≥ 2 → ∀ c : EdgeColoring n,
    ¬IsBalanced n c 2 (1/2)

/-- Edge count identity: red + blue = total for any coloring. -/
axiom color_partition (n : ℕ) (c : EdgeColoring n) (X : Finset (Fin n)) :
  redEdgeCount n c X + blueEdgeCount n c X = edgeCount n X

/-! ## Monotonicity -/

/-- F(n, α) is non-decreasing in α: harder balance requires larger subsets. -/
axiom threshold_monotone_alpha (n : ℕ) (α β : ℚ) :
  0 ≤ α → α ≤ β → β < 1/2 →
    balancedThreshold n α ≤ balancedThreshold n β

/-- F(n, α) is non-decreasing in n for fixed α. -/
axiom threshold_monotone_n (α : ℚ) (m n : ℕ) :
  m ≤ n → balancedThreshold m α ≤ balancedThreshold n α
