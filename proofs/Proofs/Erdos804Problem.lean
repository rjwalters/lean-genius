/-
Erdős Problem #804: Independent Sets in Locally Independent Graphs

Source: https://erdosproblems.com/804
Status: DISPROVED (Alon-Sudakov, 2007)

Statement:
Let f(m, n) be the maximum such that any graph on n vertices in which every
induced subgraph on m vertices has an independent set of size ≥ log n must
contain an independent set of size ≥ f(n).

Questions:
1. Is f((log n)², n) ≥ n^(1/2 - o(1))?
2. Is f((log n)³, n) ≫ (log n)³?

Answer: NO to both! (Alon-Sudakov, 2007)

The actual bounds are:
- (log n)² / log log n ≪ f((log n)², n) ≪ (log n)²
- f((log n)³, n) ≍ (log n)² / log log n

Key insight: The conjecture overestimated how much "local" independent set
structure forces "global" independent sets. The true bounds are much smaller.

Reference: [AlSu07] Alon-Sudakov (2007), [Er91] Erdős (1991)
See also: Erdős Problem #805
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot

open Nat Finset Set Filter SimpleGraph

namespace Erdos804

/-
## Part I: Independent Sets in Graphs

An independent set (or stable set) is a set of vertices with no edges between them.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Independent Set:**
A set S of vertices is independent if no two vertices in S are adjacent.
-/
def IsIndependent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/--
**Independence Number:**
α(G) = maximum size of an independent set in G.
-/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  Finset.sup (Finset.univ.powerset.filter (fun S => IsIndependent G S)) Finset.card

/--
**Basic fact: Empty set is independent**
-/
theorem empty_is_independent (G : SimpleGraph V) : IsIndependent G ∅ := by
  intro u hu
  exact absurd hu (Finset.not_mem_empty u)

/-
## Part II: The Function f(m, n)

f(m, n) captures the relationship between local and global independent set structure.
-/

/--
**Local Independence Property:**
A graph G on n vertices has the (m, k)-local independence property if
every induced subgraph on m vertices has an independent set of size ≥ k.
-/
def HasLocalIndependence (G : SimpleGraph V) (m k : ℕ) : Prop :=
  ∀ S : Finset V, S.card = m →
    ∃ I : Finset V, I ⊆ S ∧ IsIndependent G I ∧ I.card ≥ k

/-
## Part III: Erdős-Hajnal's Conjectures

Erdős and Hajnal conjectured strong bounds on f(m, n).
-/

/--
**Conjecture 1 (DISPROVED):**
f((log n)², n) ≥ n^(1/2 - o(1))

This would mean: if every (log n)²-vertex subgraph has independent set ≥ log n,
then the whole graph has independent set nearly √n.

This was TOO optimistic!
-/
axiom erdos_hajnal_conjecture_1_false :
    ¬(∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) →
          independenceNumber G ≥ n / n ^ ε)

/--
**Conjecture 2 (DISPROVED):**
f((log n)³, n) ≫ (log n)³

This would mean: if every (log n)³-vertex subgraph has independent set ≥ log n,
then the whole graph has independent set much larger than (log n)³.

Also TOO optimistic!
-/
axiom erdos_hajnal_conjecture_2_false :
    ¬(∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        HasLocalIndependence G ((Nat.log n) ^ 3) (Nat.log n) →
          independenceNumber G ≥ (Nat.log n) ^ 3 * Nat.log n)

/-
## Part IV: Alon-Sudakov's Resolution (2007)

They established the true bounds, disproving both conjectures.
-/

/--
**Alon-Sudakov Upper Bound for (log n)²:**
f((log n)², n) ≪ (log n)²

There exist graphs where every (log n)²-vertex subgraph has independent
set ≥ log n, but the global independence number is only O((log n)²).
-/
axiom alon_sudakov_upper_bound_1 :
    ∃ C : ℝ, C > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) ∧
            independenceNumber G ≤ C * (Nat.log n) ^ 2

/--
**Alon-Sudakov Lower Bound for (log n)²:**
f((log n)², n) ≫ (log n)² / log log n

Any graph where every (log n)²-vertex subgraph has independent set ≥ log n
must have global independence number at least (log n)² / log log n.
-/
axiom alon_sudakov_lower_bound_1 :
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) →
            (independenceNumber G : ℝ) ≥ c * (Nat.log n) ^ 2 / Nat.log (Nat.log n)

/--
**Alon-Sudakov Tight Bound for (log n)³:**
f((log n)³, n) ≍ (log n)² / log log n

The answer is only (log n)² / log log n, NOT (log n)³ as conjectured!
-/
axiom alon_sudakov_tight_bound_2 :
    -- Lower bound
    (∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 3) (Nat.log n) →
            (independenceNumber G : ℝ) ≥ c * (Nat.log n) ^ 2 / Nat.log (Nat.log n)) ∧
    -- Upper bound
    (∃ C : ℝ, C > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 3) (Nat.log n) ∧
            (independenceNumber G : ℝ) ≤ C * (Nat.log n) ^ 2 / Nat.log (Nat.log n))

/-
## Part V: Main Results
-/

/--
**Erdős Problem #804: DISPROVED (Alon-Sudakov, 2007)**

Q1: Is f((log n)², n) ≥ n^(1/2 - o(1))?
A: NO. The true answer is Θ((log n)² / log log n).

Q2: Is f((log n)³, n) ≫ (log n)³?
A: NO. The true answer is Θ((log n)² / log log n).

Key insight: Local independent set structure doesn't propagate to global
structure as strongly as Erdős and Hajnal expected.
-/
theorem erdos_804 :
    -- Both original conjectures are false
    ¬(∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) →
            independenceNumber G ≥ n / n ^ ε) ∧
    ¬(∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 3) (Nat.log n) →
            independenceNumber G ≥ (Nat.log n) ^ 3 * Nat.log n) := by
  exact ⟨erdos_hajnal_conjecture_1_false, erdos_hajnal_conjecture_2_false⟩

/-
## Part VI: Alon-Sudakov Full Resolution
-/

/--
**Complete resolution of Problem #804:**

The true bounds are:
1. f((log n)², n) = Θ((log n)² / log log n) — between lower and upper bounds
2. f((log n)³, n) = Θ((log n)² / log log n) — tight characterization

Both conjectures overestimated the local-to-global propagation strength.

Remarkably, increasing m from (log n)² to (log n)³ does NOT significantly
improve the global bound — the bottleneck is elsewhere.
-/
theorem erdos_804_resolution :
    -- Conjectures are false
    (¬(∀ ε > 0, ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) →
            independenceNumber G ≥ n / n ^ ε)) ∧
    (¬(∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 3) (Nat.log n) →
            independenceNumber G ≥ (Nat.log n) ^ 3 * Nat.log n)) ∧
    -- But precise bounds exist (Alon-Sudakov 2007)
    (∃ C : ℝ, C > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) ∧
            independenceNumber G ≤ C * (Nat.log n) ^ 2) ∧
    (∃ c : ℝ, c > 0 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          HasLocalIndependence G ((Nat.log n) ^ 2) (Nat.log n) →
            (independenceNumber G : ℝ) ≥ c * (Nat.log n) ^ 2 / Nat.log (Nat.log n)) :=
  ⟨erdos_hajnal_conjecture_1_false, erdos_hajnal_conjecture_2_false,
   alon_sudakov_upper_bound_1, alon_sudakov_lower_bound_1⟩

end Erdos804
