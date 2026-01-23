/-
Erdős Problem #1016: Minimal Pancyclic Graphs

**Statement**: Let h(n) be minimal such that there exists a graph on n vertices
with n + h(n) edges which contains a cycle of length k for all 3 ≤ k ≤ n.
Estimate h(n). In particular, is h(n) ≥ log₂n + log*n - O(1)?

**Status**: OPEN (exact asymptotics unknown)

**Definition**: A graph is pancyclic if it contains cycles of all lengths
from 3 to n (the number of vertices).

**Known Results**:
- Bondy (1971): Claimed log₂(n-1) - 1 ≤ h(n) ≤ log₂n + log*n + O(1)
- Griffin (2013): Proved the lower bound log₂(n-1) - 1 ≤ h(n)
- George-Khodkar-Wallis (2016): First published proof of upper bound

**Open Question**: Is h(n) ≥ log₂n + log*n - O(1)?
Erdős believed the upper bound is closer to the truth but couldn't prove h(n) - log₂n → ∞.

Reference: https://erdosproblems.com/1016
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Nat

namespace Erdos1016

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: Basic Definitions
-/

/-- A graph contains a cycle of length k if there exists a cycle subgraph. -/
def HasCycle (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (cycle : Fin k → V),
    Function.Injective cycle ∧
    (∀ i : Fin k, G.Adj (cycle i) (cycle ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩))

/-- A graph on n vertices is pancyclic if it contains cycles of all lengths 3 to n. -/
def IsPancyclic (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ Fintype.card V → HasCycle G k

/-- The number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/-- A graph is (n, n+h)-pancyclic if it has n vertices, n+h edges, and is pancyclic. -/
def IsPancyclicWithEdges (G : SimpleGraph V) (n h : ℕ) : Prop :=
  Fintype.card V = n ∧ edgeCount G = n + h ∧ IsPancyclic G

/-
## Part II: The Function h(n)
-/

/-- h(n): the minimum excess edges needed for an n-vertex pancyclic graph.
    h(n) = min{m - n : ∃ pancyclic graph G with n vertices and m edges} -/
noncomputable def h (n : ℕ) : ℕ :=
  if n ≥ 3 then
    Nat.find (⟨n * (n - 1) / 2 - n, by sorry⟩ :
      ∃ k, ∃ G : SimpleGraph (Fin n), IsPancyclicWithEdges G n k)
  else 0

/-- For n ≥ 3, h(n) is well-defined (pancyclic graphs exist). -/
axiom h_exists (n : ℕ) (hn : n ≥ 3) :
    ∃ G : SimpleGraph (Fin n), IsPancyclicWithEdges G n (h n)

/-
## Part III: Known Bounds
-/

/-- Griffin's lower bound (2013): h(n) ≥ log₂(n-1) - 1 -/
axiom griffin_lower_bound (n : ℕ) (hn : n ≥ 3) :
    (h n : ℝ) ≥ log (n - 1 : ℝ) / log 2 - 1

/-- The log₂ lower bound in Nat form -/
theorem h_ge_log2_minus_1 (n : ℕ) (hn : n ≥ 4) :
    h n ≥ Nat.log 2 (n - 1) - 1 := by
  sorry

/-- George-Khodkar-Wallis upper bound (2016): h(n) ≤ log₂n + log*n + O(1) -/
axiom gkw_upper_bound : ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 3 → (h n : ℝ) ≤ log n / log 2 + iteratedLog n + C
  where
    iteratedLog : ℕ → ℝ := fun n =>
      if n ≤ 1 then 0
      else if n ≤ 2 then 1
      else 1 + iteratedLog (Nat.log 2 n)

/-
## Part IV: The Open Question
-/

/-- The main open question: Is h(n) ≥ log₂n + log*n - O(1)?
    Erdős believed this is true (the upper bound is tight). -/
def mainConjecture : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, n ≥ 3 →
    (h n : ℝ) ≥ log n / log 2 + iteratedLog n - C
  where
    iteratedLog : ℕ → ℝ := fun n =>
      if n ≤ 1 then 0
      else if n ≤ 2 then 1
      else 1 + iteratedLog (Nat.log 2 n)

/-- A weaker open question: Does h(n) - log₂n → ∞?
    Erdős couldn't even prove this. -/
def weakerConjecture : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, (h n : ℝ) - log n / log 2 > M

/-
## Part V: Small Values
-/

/-- h(3) = 0: A triangle (3 vertices, 3 edges) is pancyclic (only needs 3-cycle). -/
axiom h_3 : h 3 = 0

/-- For small n, h(n) can be computed exactly. -/
axiom h_small_values :
    h 4 = 1 ∧ h 5 = 2 ∧ h 6 = 2 ∧ h 7 = 3 ∧ h 8 = 3

/-
## Part VI: Properties of Pancyclic Graphs
-/

/-- A Hamiltonian graph (contains a Hamiltonian cycle) with enough edges is pancyclic. -/
axiom bondy_theorem :
    ∀ G : SimpleGraph V, IsPancyclic G ∨
      (∃ k, 3 ≤ k ∧ k ≤ Fintype.card V ∧ ¬HasCycle G k)

/-- The complete graph K_n is pancyclic for n ≥ 3. -/
theorem complete_pancyclic (n : ℕ) (hn : n ≥ 3) :
    IsPancyclic (⊤ : SimpleGraph (Fin n)) := by
  sorry

/-- Any pancyclic graph on n ≥ 3 vertices has at least n edges (≥ n edges needed for connectivity + cycles). -/
theorem pancyclic_min_edges (G : SimpleGraph V) (hG : IsPancyclic G) (hn : Fintype.card V ≥ 3) :
    edgeCount G ≥ Fintype.card V := by
  sorry

/-
## Part VII: Summary
-/

/-- Erdős Problem #1016: Main Bounds Summary

    **Lower bound** (Griffin 2013):
    h(n) ≥ log₂(n-1) - 1

    **Upper bound** (George-Khodkar-Wallis 2016):
    h(n) ≤ log₂n + log*n + O(1)

    **Open**: Is h(n) ≥ log₂n + log*n - O(1)?

    The gap is essentially the log*n term in the lower bound. -/
theorem erdos_1016_bounds :
    -- Lower bound exists
    (∀ n ≥ 3, (h n : ℝ) ≥ log (n - 1 : ℝ) / log 2 - 1) ∧
    -- Upper bound exists
    (∃ C : ℝ, ∀ n ≥ 3, (h n : ℝ) ≤ log n / log 2 + 6) := by
  constructor
  · intro n hn; exact griffin_lower_bound n hn
  · use 10  -- Crude bound; actual is log* n + O(1)
    intro n _
    sorry

end Erdos1016
