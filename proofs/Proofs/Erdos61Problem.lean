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

/-
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

/-
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

/-
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

/-
## Partial Results (PROVED)

While the main conjecture is open, weaker bounds have been established.
-/

/- 
**Erdős-Hajnal 1989 Bound**

Erdős and Hajnal proved that for any graph H, there exists c_H > 0 such that
exp(c_H · √(log n)) is an Erdős-Hajnal lower bound for H.

This is weaker than the conjectured n^c but still much better than the
log(n) bound from general Ramsey theory.

This bound is documented here in prose only; the proof requires probabilistic
and combinatorial techniques beyond current Mathlib formalization and is not
stated as a Lean axiom or theorem.
-/
/- 
**Bucić-Nguyen-Scott-Seymour 2023 Bound**

In 2023, Bucić, Nguyen, Scott, and Seymour improved the Erdős-Hajnal bound to
exp(c_H · √(log n · log log n)).

This is the current best known bound toward the conjecture.
-/
/-
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
  symm := by constructor; intro i j h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all
  loopless := by constructor; intro i h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> simp_all

/-
The Erdős-Hajnal conjecture is known to be true for several specific graphs H,
including paths, cycles, and complete bipartite graphs.
-/

/-
## Foundational lemmas (axiom-free)

The main conjecture and the two partial bounds (Erdős–Hajnal 1989, BNSS 2023)
are deep results documented in the header prose only — they are not formalised.
What follows are the machine-checkable structural facts about the
`IsErdosHajnalLowerBound` predicate itself, proved with no axioms and no `sorry`.
Together they isolate *why* the conjecture is nontrivial: a lower bound of size
`0` always exists, so the entire content of the conjecture is the *growth rate*
(the polynomial exponent `c > 0`), not mere existence.
-/

/-- The constant bound `0` is always an Erdős–Hajnal lower bound: the independence
    number is a nonnegative integer, so the left disjunct holds for every graph.
    Hence the conjecture is entirely about the *rate* `n^c`, not existence. -/
theorem isErdosHajnalLowerBound_zero {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) : IsErdosHajnalLowerBound H (fun _ => 0) :=
  Filter.Eventually.of_forall fun _ _ _ => Or.inl (by simp only [ge_iff_le]; positivity)

/-- Erdős–Hajnal lower bounds are downward closed: weakening the target function
    pointwise preserves the property. So the difficulty is monotone in the demanded
    rate — establishing a *larger* bound is what is hard. -/
theorem IsErdosHajnalLowerBound.mono {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} {f g : ℕ → ℝ} (hg : IsErdosHajnalLowerBound H g)
    (hfg : ∀ n, f n ≤ g n) : IsErdosHajnalLowerBound H f := by
  filter_upwards [hg] with n hn
  intro G hG
  rcases hn G hG with hi | hc
  · exact Or.inl (le_trans (hfg n) hi)
  · exact Or.inr (le_trans (hfg n) hc)

end Erdos61
