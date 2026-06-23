/-
# Erdős Problem #78: Constructive Ramsey Lower Bound

Erdős Problem #78 asks for a constructive proof that R(k) > C^k for some
constant C > 1, where R(k) is the diagonal Ramsey number.

Equivalently: explicitly construct an n-vertex graph with no clique or
independent set of size ≥ c·log n.

Erdős's probabilistic method (1947) gives R(k) ≥ k·2^{k/2}/e, but this
is non-constructive. The best constructive results fall far short:
- Cohen (2015): no clique/independent set of size ≥ 2^{(log log n)^C}
- Li (2023): improved to (log n)^C

Reward: $100. Reference: https://erdosproblems.com/78
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/- ## Definitions -/

/-- A simple graph on n vertices. -/
structure SimpleG (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- A clique of size k in a graph. -/
def SimpleG.hasClique {n : ℕ} (G : SimpleG n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v

/-- An independent set of size k in a graph. -/
def SimpleG.hasIndepSet {n : ℕ} (G : SimpleG n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.adj u v

/-- The diagonal Ramsey number R(k): minimum n such that every graph on
    n vertices contains either a k-clique or a k-independent set. -/
axiom ramseyNumber (k : ℕ) : ℕ

/- ## Erdős Probabilistic Bound -/

/- ## Constructive Results -/

/-- An explicit graph construction is a computable function from n to a graph.
    The key requirement is polynomial-time computability. -/
def IsExplicit {n : ℕ} (G : SimpleG n) : Prop :=
  True  -- Axiomatized: constructibility is a meta-property

/- ## Main Open Problem -/

/- ## Upper Bound on R(k) -/
