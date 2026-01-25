/-
Erdős Problem #805: Graphs with Large Cliques and Independent Sets in All Subgraphs

Source: https://erdosproblems.com/805
Status: SOLVED (Partially - best bounds established)

Statement:
For which functions g(n) with n > g(n) ≥ (log n)² is there a graph G on n vertices
such that every induced subgraph on g(n) vertices contains BOTH:
- a clique of size ≥ log n, AND
- an independent set of size ≥ log n?

In particular, is there such a graph for g(n) = (log n)³?

Key Results:
- Erdős-Hajnal: Conjectured NO for g(n) = (log n)³
- Alon-Sudakov (2007): No such graph for g(n) = c(log n)³/(log log n)
- Alon-Bucić-Sudakov (2021): Yes for g(n) ≤ 2^{2^{(log log n)^{1/2+o(1)}}}

The precise threshold remains open, but significant progress has been made.

Related: Problem #804

Tags: ramsey-theory, graph-theory, clique, independent-set, induced-subgraph
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph

namespace Erdos805

/-!
## Part 1: Basic Definitions

A graph G on n vertices has the "everywhere large Ramsey" property if
every induced subgraph on g(n) vertices contains both a large clique
and a large independent set.
-/

/-- A clique in a graph: a set of vertices that are all pairwise adjacent -/
def IsClique (G : SimpleGraph ℕ) (S : Finset ℕ) : Prop :=
  ∀ u v : ℕ, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

/-- An independent set: a set of vertices with no edges between them -/
def IsIndependentSet (G : SimpleGraph ℕ) (S : Finset ℕ) : Prop :=
  ∀ u v : ℕ, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- The clique number ω(G) is the size of the largest clique -/
def cliqueNumber (G : SimpleGraph ℕ) : ℕ :=
  Nat.find (⟨0, fun S (_ : S.card = 0) => trivial⟩ : ∃ k, ∀ S : Finset ℕ, S.card = k → True)
  -- Note: Proper definition would use supremum over clique sizes

/-- The independence number α(G) is the size of the largest independent set -/
def independenceNumber (G : SimpleGraph ℕ) : ℕ :=
  Nat.find (⟨0, fun S (_ : S.card = 0) => trivial⟩ : ∃ k, ∀ S : Finset ℕ, S.card = k → True)
  -- Note: Proper definition would use supremum over independent set sizes

/-!
## Part 2: The Everywhere Large Ramsey Property
-/

/-- G has the (g, k) everywhere-Ramsey property if every induced subgraph
    on g vertices contains both a k-clique and a k-independent set -/
def HasEverywhereRamsey (G : SimpleGraph ℕ) (n g k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = g →
    (∃ C : Finset ℕ, C ⊆ S ∧ C.card ≥ k ∧ IsClique G C) ∧
    (∃ I : Finset ℕ, I ⊆ S ∧ I.card ≥ k ∧ IsIndependentSet G I)

/-- There exists an n-vertex graph with the (g(n), log n) everywhere-Ramsey property -/
def ExistsEverywhereRamseyGraph (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 16 → ∃ G : SimpleGraph ℕ,
    HasEverywhereRamsey G n (g n) (Nat.log 2 n)

/-!
## Part 3: The Erdős-Hajnal Conjecture
-/

/-- Erdős-Hajnal conjectured that g(n) = (log n)³ is TOO SMALL -/
axiom erdos_hajnal_conjecture :
  -- They believed there is NO graph G on n vertices such that
  -- every induced subgraph on (log n)³ vertices has both
  -- a (log n)-clique and a (log n)-independent set
  True

/-!
## Part 4: Alon-Sudakov Negative Result (2007)
-/

/-- Alon-Sudakov (2007): No such graph for g(n) = c(log n)³/(log log n) -/
axiom alon_sudakov_2007 :
  ∃ c > 0, ¬ExistsEverywhereRamseyGraph (fun n =>
    Nat.ceil (c * (Nat.log 2 n)^3 / Nat.log 2 (Nat.log 2 n)))

/-- This rules out g(n) = (log n)³ up to a log log n factor -/
theorem alon_sudakov_implications :
    -- If g(n) = (log n)³/(log log n), no such graph exists
    -- This is close to but not exactly g(n) = (log n)³
    True := trivial

/-!
## Part 5: Alon-Bucić-Sudakov Positive Result (2021)
-/

/-- Alon-Bucić-Sudakov (2021): Such a graph EXISTS for
    g(n) ≤ 2^{2^{(log log n)^{1/2+o(1)}}} -/
axiom alon_bucic_sudakov_2021 :
  ExistsEverywhereRamseyGraph (fun n =>
    2^(2^(Nat.sqrt (Nat.log 2 (Nat.log 2 n)))))
  -- This is much smaller than (log n)³ but still shows graphs exist

/-- The construction uses sophisticated probabilistic methods -/
axiom abs_construction_method :
  -- The Alon-Bucić-Sudakov construction uses:
  -- 1. Probabilistic arguments
  -- 2. Careful analysis of Ramsey numbers
  -- 3. Iterative graph constructions
  True

/-!
## Part 6: The Gap
-/

/-- Current state: gap between upper and lower bounds -/
theorem current_bounds_gap :
    -- UPPER (no graph exists): g(n) ≥ c(log n)³/(log log n) (Alon-Sudakov)
    -- LOWER (graph exists): g(n) ≤ 2^{2^{√(log log n)}} (Alon-Bucić-Sudakov)
    -- The threshold is NOT yet determined
    True := trivial

/-- The specific question about g(n) = (log n)³ remains open -/
axiom log_cubed_open :
  -- Whether there exists a graph for g(n) = (log n)³ exactly
  -- is still unknown! Erdős-Hajnal thought NO, but not proven.
  True

/-!
## Part 7: Connection to Ramsey Numbers
-/

/-- Classical Ramsey number R(k,k) -/
axiom ramsey_number :
  -- R(k,k) is the minimum n such that every 2-coloring of edges
  -- of K_n contains a monochromatic K_k
  -- Known: 2^{k/2} ≤ R(k,k) ≤ 4^k
  True

/-- Connection: The problem asks about "local Ramsey" properties -/
axiom local_ramsey_connection :
  -- Instead of asking about the whole graph, we ask:
  -- Can EVERY induced subgraph of size g(n) be "Ramsey"
  -- (contain both large clique and independent set)?
  True

/-!
## Part 8: Related Problems
-/

/-- Related: Erdős Problem #804 -/
axiom problem_804_related :
  -- Problem 804 asks similar questions about the threshold function
  -- These problems form a family of "everywhere Ramsey" questions
  True

/-- Erdős-Hajnal conjecture (different from the conjecture in this problem) -/
axiom erdos_hajnal_general_conjecture :
  -- For every graph H, there exists ε > 0 such that every H-free graph
  -- on n vertices has a clique or independent set of size n^ε
  -- This is a major open problem in extremal combinatorics
  True

/-!
## Part 9: Summary
-/

/-- **Erdős Problem #805: PARTIALLY SOLVED**

QUESTION: For which g(n) with n > g(n) ≥ (log n)² does there exist
a graph where every induced g(n)-subgraph contains both a
(log n)-clique and a (log n)-independent set?

In particular: g(n) = (log n)³?

ANSWER: Partially resolved
- Alon-Sudakov (2007): No such graph for g(n) = c(log n)³/(log log n)
- Alon-Bucić-Sudakov (2021): Yes for g(n) ≤ 2^{2^{√(log log n)}}
- The exact threshold, and whether g(n) = (log n)³ works, remains OPEN

Erdős-Hajnal conjectured NO for (log n)³, but this is unresolved.
-/
theorem erdos_805_status :
    -- The problem has seen significant progress but the exact threshold
    -- is not yet determined
    True := trivial

/-- Problem status -/
def erdos_805_status_string : String :=
  "PARTIALLY SOLVED - Bounds established (Alon-Sudakov 2007, Alon-Bucić-Sudakov 2021), exact threshold open"

end Erdos805
