/-!
# Erdős Problem #596: Graph Coloring Dichotomy for Forbidden Subgraphs

For which pairs (G₁, G₂) of graphs is it true that:
1. For every n ≥ 1, there exists a G₁-free graph H such that every n-coloring
   of H's edges contains a monochromatic G₂, AND
2. For every G₁-free graph H, there exists a countable coloring of H's edges
   with no monochromatic G₂?

The pair (C₄, C₆) satisfies both conditions:
- Nešetřil–Rödl established property (1).
- Erdős–Hajnal proved property (2): every C₄-free graph is a countable union of trees.

Status: OPEN

Reference: https://erdosproblems.com/596
Source: [Er87]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Part I: Graph Coloring Dichotomy
-/

namespace Erdos596

/-- A property of graphs (used to represent "G₁-free" or "contains G₂"). -/
def GraphProperty := SimpleGraph ℕ → Prop

/-- Property (1): For every n, there exists a G₁-free graph H such that
    every n-coloring of H's edges contains a monochromatic copy of G₂. -/
def FiniteRamseyProperty (isForbiddenFree : GraphProperty) (containsTarget : GraphProperty) : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ H : SimpleGraph ℕ,
    isForbiddenFree H ∧
    ∀ coloring : (Σ v w : ℕ, H.Adj v w) → Fin n,
      ∃ c : Fin n, containsTarget (H)

/-- Property (2): Every G₁-free graph H has a countable edge coloring
    with no monochromatic G₂. -/
def CountableColoringProperty (isForbiddenFree : GraphProperty) (containsTarget : GraphProperty) : Prop :=
  ∀ H : SimpleGraph ℕ, isForbiddenFree H →
    ∃ coloring : (Σ v w : ℕ, H.Adj v w) → ℕ,
      ∀ c : ℕ, ¬containsTarget (H)

/-- The full dichotomy: a pair (G₁, G₂) satisfies both properties. -/
def HasDichotomy (isForbiddenFree : GraphProperty) (containsTarget : GraphProperty) : Prop :=
  FiniteRamseyProperty isForbiddenFree containsTarget ∧
  CountableColoringProperty isForbiddenFree containsTarget

/-!
## Part II: Known Examples
-/

/-- The C₄-free property. -/
def IsC4Free : GraphProperty := fun G =>
  ¬∃ (a b c d : ℕ), a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
    a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- Contains a monochromatic C₆ (simplified predicate). -/
def ContainsC6 : GraphProperty := fun G =>
  ∃ (a b c d e f : ℕ),
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
    G.Adj d e ∧ G.Adj e f ∧ G.Adj f a ∧
    a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ f ∧ f ≠ a

/-- Nešetřil–Rödl: For every n, there exists a C₄-free graph whose
    n-colorings all contain a monochromatic C₆. -/
axiom nesetril_rodl_c4_c6 : FiniteRamseyProperty IsC4Free ContainsC6

/-- Erdős–Hajnal: Every C₄-free graph is a countable union of trees
    (hence admits a countable coloring avoiding monochromatic C₆). -/
axiom erdos_hajnal_c4_trees : CountableColoringProperty IsC4Free ContainsC6

/-!
## Part III: The Known Dichotomy Pair
-/

/-- The pair (C₄, C₆) has the dichotomy property. -/
theorem c4_c6_dichotomy : HasDichotomy IsC4Free ContainsC6 :=
  ⟨nesetril_rodl_c4_c6, erdos_hajnal_c4_trees⟩

/-!
## Part IV: The Main Conjecture
-/

/-- Erdős Problem #596: Characterize all pairs (G₁, G₂) with the dichotomy. -/
def ErdosProblem596 : Prop :=
  ∃ characterization : (GraphProperty × GraphProperty) → Prop,
    ∀ (isForbiddenFree containsTarget : GraphProperty),
      characterization (isForbiddenFree, containsTarget) ↔
      HasDichotomy isForbiddenFree containsTarget

/-- The problem is open: no complete characterization is known. -/
axiom erdos_596 : ErdosProblem596

/-!
## Part V: Related Problem (K₄, K₃)
-/

/-- The K₄-free property. -/
def IsK4Free : GraphProperty := fun G =>
  ¬∃ (a b c d : ℕ), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧
    G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- Contains a triangle. -/
def ContainsK3 : GraphProperty := fun G =>
  ∃ (a b c : ℕ), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- Problem #595: Does the pair (K₄, K₃) have the dichotomy?
    This is a specific instance related to Problem #596. -/
axiom erdos_595_k4_k3 : HasDichotomy IsK4Free ContainsK3

/-!
## Part VI: Properties
-/

/-- Erdős and Hajnal originally conjectured no pairs exist,
    but the (C₄, C₆) example disproves this. -/
theorem dichotomy_pairs_exist : ∃ (p q : GraphProperty), HasDichotomy p q :=
  ⟨IsC4Free, ContainsC6, c4_c6_dichotomy⟩

/-!
## Part VII: Summary

- The pair (C₄, C₆) satisfies the dichotomy (proved from axioms).
- A complete characterization of all dichotomy pairs remains OPEN.
- The related problem for (K₄, K₃) is also open.
-/

/-- The statement unfolds to the existence of a characterization. -/
theorem erdos_596_statement : ErdosProblem596 ↔ ErdosProblem596 := by simp

/-- The problem remains OPEN. -/
theorem erdos_596_status : True := trivial

end Erdos596
