/-
Erdős Problem #61: The Erdős–Hajnal Conjecture

For any graph H, does there exist c = c(H) > 0 such that every graph G on n
vertices that does NOT contain H as an induced subgraph contains either:
- A clique of size ≥ n^c, OR
- An independent set of size ≥ n^c?

**Status**: OPEN (the main conjecture)

**Partial Results**:
- Erdős-Hajnal (1989): Proved exp(c_H √(log n)) bound
- Bucić-Nguyen-Scott-Seymour (2023): Improved to exp(c_H √(log n · log log n))

The conjecture remains open for the polynomial bound n^c.

Reference: https://erdosproblems.com/61
-/

import Mathlib

open Filter
open SimpleGraph
open Real

namespace Erdos61

/-!
## Background

The Erdős–Hajnal conjecture connects two fundamental concepts in graph theory:
1. **Induced subgraphs**: H is an induced subgraph of G if we can find H inside G
   by selecting vertices and keeping exactly the edges between them
2. **Ramsey numbers**: Every graph contains either a large clique or large independent set

The Ramsey number R(k,k) guarantees a clique or independent set of size k in any
graph on R(k,k) vertices. But R(k,k) grows exponentially, giving only log(n) bound.

Erdős and Hajnal conjectured that FORBIDDING a fixed induced subgraph H should
give a much better (polynomial) bound.
-/

/-!
## The Main Definition

For a graph H, we say f(n) is an "Erdős-Hajnal lower bound" if every H-free graph
on n vertices has a clique or independent set of size at least f(n).
-/

/--
A function f is an **Erdős-Hajnal lower bound** for graph H if:
for all sufficiently large n, every graph G on n vertices that does NOT
contain H as an induced subgraph has either:
- An independent set of size ≥ f(n), OR
- A clique of size ≥ f(n)

This captures the key property the conjecture asks about.
-/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-!
## The Main Conjecture (OPEN)

The Erdős–Hajnal conjecture asks whether we can always achieve a polynomial
bound n^c for some c > 0 depending on H.
-/

/--
**The Erdős–Hajnal Conjecture (OPEN)**

For every graph H, there exists a constant c = c(H) > 0 such that
n^c is an Erdős-Hajnal lower bound for H.

In other words: forbidding any fixed induced subgraph forces a polynomial-size
clique or independent set.

This conjecture remains OPEN as of 2025. We state it without claiming truth value.
-/
def ErdosHajnalConjecture : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
    ∃ c : ℝ, c > 0 ∧ IsErdosHajnalLowerBound H (fun n => (n : ℝ) ^ c)

/-!
## Partial Results (PROVED)

While the main conjecture is open, weaker bounds have been established.
-/

/--
**Erdős-Hajnal 1989 Bound**

Erdős and Hajnal proved that for any graph H, there exists c_H > 0 such that
exp(c_H · √(log n)) is an Erdős-Hajnal lower bound for H.

This is weaker than the conjectured n^c but still much better than the
log(n) bound from general Ramsey theory.

We state this as an axiom since the proof requires probabilistic and
combinatorial techniques beyond current Mathlib formalization.
-/
axiom erdosHajnal1989 :
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
    ∃ c : ℝ, c > 0 ∧ IsErdosHajnalLowerBound H (fun n => exp (c * sqrt (log n)))

/--
**Bucić-Nguyen-Scott-Seymour 2023 Bound**

In 2023, Bucić, Nguyen, Scott, and Seymour improved the Erdős-Hajnal bound to
exp(c_H · √(log n · log log n)).

This is the current best known bound toward the conjecture.
-/
axiom bnss2023 :
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
    ∃ c : ℝ, c > 0 ∧ IsErdosHajnalLowerBound H (fun n => exp (c * sqrt (log n * log (log n))))

/-!
## Comparison of Bounds

To understand the progress, compare the bounds for a graph on n = 10^6 vertices:
- Ramsey bound: log n ≈ 6 (from Ramsey theory)
- Erdős-Hajnal 1989: exp(c√6) ≈ exp(2.4c)
- BNSS 2023: exp(c√(6·log 6)) ≈ exp(3.4c)
- Conjectured: n^c = 10^(6c)

The gap between the best known bound and the conjecture is enormous.
-/

/-- The triangle graph K₃ on 3 vertices. -/
def triangleGraph : SimpleGraph (Fin 3) := completeGraph (Fin 3)

/-- The path graph P₃ on 3 vertices (a-b-c with edges ab, bc). -/
def threePathGraph : SimpleGraph (Fin 3) where
  Adj := fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
  symm := by intro i j h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all
  loopless := by intro i h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all

/--
The Erdős-Hajnal conjecture is known to be true for several specific graphs H,
including paths, cycles, and complete bipartite graphs.
-/
axiom erdosHajnalForPaths :
  ∃ c : ℝ, c > 0 ∧ IsErdosHajnalLowerBound threePathGraph (fun n => (n : ℝ) ^ c)

end Erdos61
