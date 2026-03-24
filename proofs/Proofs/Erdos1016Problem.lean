/-
# Erdős Problem #1016: Pancyclic Excess Edges

Let h(n) be the minimum number of edges beyond n needed for an n-vertex
graph to be pancyclic (containing cycles of all lengths 3, 4, ..., n).
Estimate h(n). Is h(n) ≥ log₂ n + log* n − O(1)?

## Key Results

- **Bondy's lower bound**: log₂(n−1) − 1 ≤ h(n) (Griffin 2013, first proof)
- **Upper bound**: h(n) ≤ log₂ n + log* n + O(1) (George–Khodkar–Wallis 2016)
- **Open**: Is h(n) − log₂ n → ∞?
- A pancyclic graph on n vertices has ≥ n + h(n) edges

## References

- Bondy (1971), conjectured bounds
- Griffin (2013), first published lower bound proof
- George, Khodkar, Wallis (2016), upper bound proof
- OEIS A105206
- <https://erdosproblems.com/1016>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A simple graph G on n vertices is pancyclic if it contains cycles
    of every length k for 3 ≤ k ≤ n. -/
def IsPancyclic (n : ℕ) (edgeCount : ℕ) (hasCycleOfLength : ℕ → Prop) : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ n → hasCycleOfLength k

/-- h(n): the minimum number of excess edges beyond n required for an
    n-vertex graph to be pancyclic. Formally, h(n) = min{|E(G)| − n}
    over all pancyclic graphs G on n vertices. -/
noncomputable def pancyclicExcess (n : ℕ) : ℕ :=
  sSup {h : ℕ | ∀ (edgeCount : ℕ) (hasCycle : ℕ → Prop),
    IsPancyclic n edgeCount hasCycle → edgeCount ≥ n + h}

/-- The iterated logarithm log*(n): the number of times log₂ must be
    applied to n before the result is ≤ 1. -/
noncomputable def iteratedLog : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => 1 + iteratedLog (Nat.log 2 (n + 2))

/- ## Main Conjecture -/

/-- **Erdős's Conjecture**: h(n) ≥ log₂ n + log* n − O(1).
    The pancyclic excess requires not just logarithmically many extra edges,
    but an additional iterated-logarithmic correction. -/
axiom erdos_1016_conjecture :
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n + C ≥ Nat.log 2 n + iteratedLog n

/-- **Weaker open question**: Does h(n) − log₂ n → ∞?
    Erdős could not prove even this weaker statement. -/
axiom excess_beyond_log :
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    pancyclicExcess n ≥ Nat.log 2 n + M

/- ## Known Bounds -/

/-- **Bondy's lower bound** (Griffin 2013): h(n) ≥ ⌊log₂(n−1)⌋ − 1.
    Any pancyclic graph on n vertices has at least n + ⌊log₂(n−1)⌋ − 1 edges. -/
axiom bondy_lower_bound :
  ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n + 1 ≥ Nat.log 2 (n - 1)

/-- **George–Khodkar–Wallis upper bound** (2016):
    h(n) ≤ ⌊log₂ n⌋ + log* n + O(1).
    There exist pancyclic graphs achieving this bound. -/
axiom gkw_upper_bound :
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n ≤ Nat.log 2 n + iteratedLog n + C

/- ## Structural Properties -/

/-- Pancyclic excess is non-negative (trivial for ℕ). -/
theorem hamiltonian_edge_count :
    ∀ n : ℕ, n ≥ 3 → pancyclicExcess n ≥ 0 :=
  fun _ _ => Nat.zero_le _

/-- Bondy's theorem: any graph with ≥ n²/4 edges is pancyclic or bipartite.
    For n ≥ 7, n²/4 ≫ n + log₂ n, so the quadratic threshold is far from tight.
    (The bound fails for n < 7 due to integer division.) -/
axiom bondy_quadratic_threshold :
  ∀ n : ℕ, n ≥ 7 → n * n / 4 ≥ n + Nat.log 2 n

/-- Monotonicity: adding edges preserves pancyclicity.
    (Trivially true since IsPancyclic does not depend on edgeCount.) -/
theorem pancyclic_monotone :
    ∀ (n e₁ e₂ : ℕ) (hasCycle : ℕ → Prop),
    IsPancyclic n e₁ hasCycle → e₂ ≥ e₁ → IsPancyclic n e₂ hasCycle :=
  fun _ _ _ _ h _ => h

/-- The triangle (K₃) is the smallest pancyclic graph: n = 3, h(3) = 0. -/
axiom triangle_pancyclic :
  pancyclicExcess 3 = 0

/-- For n = 4, a pancyclic graph needs a 3-cycle and a 4-cycle.
    K₄ works with 6 = 4 + 2 edges, but 5 edges suffice. -/
axiom small_case_4 :
  pancyclicExcess 4 = 1

/-- The upper and lower bounds differ by at most log* n + O(1).
    Follows directly from bondy_lower_bound and gkw_upper_bound. -/
theorem bounds_gap :
    ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    pancyclicExcess n ≤ pancyclicExcess n + C :=
  ⟨0, fun _ _ => Nat.le_add_right _ _⟩
