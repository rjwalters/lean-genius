/-
Erdős Problem #805: Graphs with Large Cliques and Independent Sets in All Subgraphs

Source: https://erdosproblems.com/805
Status: PARTIALLY SOLVED (bounds established)

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

The precise threshold remains open.

Related: Problem #804

References:
- Alon-Sudakov (2007)
- Alon-Bucić-Sudakov (2021)
- https://erdosproblems.com/805
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph

namespace Erdos805

/- ## Part I: Basic Definitions -/

/-- A clique in a graph: a set of vertices that are all pairwise adjacent. -/
def IsClique (G : SimpleGraph ℕ) (S : Finset ℕ) : Prop :=
  ∀ u v : ℕ, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

/-- An independent set: a set of vertices with no edges between them. -/
def IsIndependentSet (G : SimpleGraph ℕ) (S : Finset ℕ) : Prop :=
  ∀ u v : ℕ, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/- ## Part II: The Everywhere Ramsey Property -/

/-- G has the (g, k) everywhere-Ramsey property if every induced subgraph
    on g vertices contains both a k-clique and a k-independent set. -/
def HasEverywhereRamsey (G : SimpleGraph ℕ) (n g k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = g →
    (∃ C : Finset ℕ, C ⊆ S ∧ C.card ≥ k ∧ IsClique G C) ∧
    (∃ I : Finset ℕ, I ⊆ S ∧ I.card ≥ k ∧ IsIndependentSet G I)

/-- There exists an n-vertex graph with the (g(n), log n) everywhere-Ramsey property. -/
def ExistsEverywhereRamseyGraph (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 16 → ∃ G : SimpleGraph ℕ,
    HasEverywhereRamsey G n (g n) (Nat.log 2 n)

/- ## Part III: Alon-Sudakov Negative Result (2007) -/

/-- Alon-Sudakov (2007): No such graph exists for g(n) = c(log n)³/(log log n).
This provides an upper bound on the threshold, ruling out graphs when g(n) is too large. -/
axiom alon_sudakov_2007 :
  ∃ c > 0, ¬ExistsEverywhereRamseyGraph (fun n =>
    Nat.ceil (c * (Nat.log 2 n)^3 / Nat.log 2 (Nat.log 2 n)))

/- ## Part IV: Alon-Bucić-Sudakov Positive Result (2021) -/

/-- Alon-Bucić-Sudakov (2021): Such a graph EXISTS for
g(n) ≤ 2^{2^{(log log n)^{1/2+o(1)}}}. This is much smaller than (log n)³
but establishes that graphs with the property exist. -/
axiom alon_bucic_sudakov_2021 :
  ExistsEverywhereRamseyGraph (fun n =>
    2^(2^(Nat.sqrt (Nat.log 2 (Nat.log 2 n)))))

/- ## Part V: The Conjectured Threshold -/

/-- Erdős-Hajnal conjectured that g(n) = (log n)³ is too small — no graph
should exist with the everywhere-Ramsey property at this threshold. -/
def ErdosHajnalConjecture805 : Prop :=
  ¬ExistsEverywhereRamseyGraph (fun n => (Nat.log 2 n)^3)

/- ## Part VI: Summary -/

/-- **Erdős Problem #805: PARTIALLY SOLVED**

QUESTION: For which g(n) with n > g(n) ≥ (log n)² does there exist
a graph where every induced g(n)-subgraph contains both a
(log n)-clique and a (log n)-independent set?

ANSWER: Partially resolved
- Alon-Sudakov (2007): No such graph for g(n) = c(log n)³/(log log n)
- Alon-Bucić-Sudakov (2021): Yes for g(n) ≤ 2^{2^{√(log log n)}}
- The exact threshold, and whether g(n) = (log n)³ works, remains OPEN -/
theorem erdos_805 :
    (∃ c > 0, ¬ExistsEverywhereRamseyGraph (fun n =>
      Nat.ceil (c * (Nat.log 2 n)^3 / Nat.log 2 (Nat.log 2 n)))) ∧
    ExistsEverywhereRamseyGraph (fun n =>
      2^(2^(Nat.sqrt (Nat.log 2 (Nat.log 2 n))))) :=
  ⟨alon_sudakov_2007, alon_bucic_sudakov_2021⟩

end Erdos805
