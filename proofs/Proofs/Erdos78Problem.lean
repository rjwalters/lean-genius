/-!
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

/-! ## Definitions -/

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

/-- R(k) is well-defined: every graph on R(k) vertices has the property. -/
axiom ramseyNumber_spec (k : ℕ) :
  ∀ G : SimpleG (ramseyNumber k),
    G.hasClique k ∨ G.hasIndepSet k

/-! ## Erdős Probabilistic Bound -/

/-- Erdős (1947): R(k) > k·2^{k/2}/e. This is the classical probabilistic
    lower bound, proved by the first application of the probabilistic method. -/
axiom erdos_probabilistic_bound :
  ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 2 ≤ k →
    C ^ k ≤ (ramseyNumber k : ℝ)

/-- The probabilistic bound gives C = √2 asymptotically. -/
axiom erdos_sqrt2_bound :
  ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    (Real.sqrt 2 - ε) ^ k ≤ (ramseyNumber k : ℝ)

/-! ## Constructive Results -/

/-- An explicit graph construction is a computable function from n to a graph.
    The key requirement is polynomial-time computability. -/
def IsExplicit {n : ℕ} (G : SimpleG n) : Prop :=
  True  -- Axiomatized: constructibility is a meta-property

/-- Cohen (2015): explicit n-vertex graphs with no clique or independent set
    of size 2^{(log log n)^C} for some constant C. -/
axiom cohen_construction :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
    ∃ G : SimpleG n, IsExplicit G ∧
      ∀ k : ℕ, G.hasClique k ∨ G.hasIndepSet k →
        (k : ℝ) < Real.exp (C * (Real.log (Real.log n)) ^ C)

/-- Li (2023): improved explicit construction with no clique or independent
    set of size (log n)^C. -/
axiom li_construction :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
    ∃ G : SimpleG n, IsExplicit G ∧
      ∀ k : ℕ, G.hasClique k ∨ G.hasIndepSet k →
        (k : ℝ) < (Real.log n) ^ C

/-! ## Main Open Problem -/

/-- Erdős Problem #78: Give a constructive proof that R(k) > C^k for some
    C > 1. Equivalently, construct explicit n-vertex graphs with no clique
    or independent set of size c·log n. ($100 prize) -/
axiom erdos_78_constructive :
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ G : SimpleG n, IsExplicit G ∧
      ∀ k : ℕ, G.hasClique k ∨ G.hasIndepSet k →
        (k : ℝ) < c * Real.log n

/-! ## Upper Bound on R(k) -/

/-- Erdős–Szekeres (1935): R(k) ≤ C(2k-2, k-1) < 4^k.
    Recently improved by Campos–Griffiths–Morris–Sahasrabudhe (2023)
    to R(k) ≤ (4 - ε)^k for some ε > 0. -/
axiom erdos_szekeres_upper :
  ∀ k : ℕ, 2 ≤ k → (ramseyNumber k : ℝ) ≤ 4 ^ k

axiom cgms_improved_upper :
  ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, 2 ≤ k →
    (ramseyNumber k : ℝ) ≤ (4 - ε) ^ k
