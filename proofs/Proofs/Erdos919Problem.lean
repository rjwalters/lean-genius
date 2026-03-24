/-
Erdős Problem #919: Chromatic Numbers on Ordinal Products

**Problem Statement (OPEN)**

Two questions about graphs on ordinal products:

1. Is there a graph G on vertex set ω₂² with chromatic number ℵ₂ such that
   every subgraph whose vertices have lesser order type has chromatic number ≤ ℵ₀?

2. What if we instead ask for chromatic number ℵ₁?

**Background:**
Babai proved results about subgraphs of well-ordered vertex sets. Erdős and
Hajnal showed this doesn't generalize to higher cardinals by constructing a
graph on ω₁² with χ(G) = ℵ₁ where every strictly smaller subgraph has χ ≤ ℵ₀.

**Status:** OPEN

**Reference:** [Er69b]

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.InitialSeg

open Cardinal Ordinal Set

namespace Erdos919

/-
# Part 1: Basic Definitions

We work with graphs on ordinal products and their chromatic numbers.
-/

/-- The ordinal ω₁ (first uncountable ordinal) -/
def omega1 : Ordinal := Ordinal.omega1

/-- The ordinal ω₂ (second uncountable ordinal) = initial ordinal of ℵ₂ -/
def omega2 : Ordinal := (Cardinal.aleph 2).ord

/-- The ordinal product ω₁² = ω₁ × ω₁ with lexicographic ordering -/
def omega1Squared : Type* := ω₁.toType × ω₁.toType

/-- The ordinal product ω₂² = ω₂ × ω₂ with lexicographic ordering -/
def omega2Squared : Type* := ω₂.toType × ω₂.toType

/-- A graph on vertex set V -/
structure GraphOn (V : Type*) where
  adj : V → V → Prop
  symm : ∀ x y, adj x y → adj y x
  loopless : ∀ x, ¬adj x x

/-
# Part 2: Chromatic Number

The chromatic number χ(G) is the minimum number of colors needed to color
vertices so adjacent vertices have different colors.
-/

/-- A proper k-coloring of a graph -/
def IsProperColoring {V : Type*} (G : GraphOn V) (k : Cardinal) (c : V → k.toType) : Prop :=
  ∀ x y, G.adj x y → c x ≠ c y

/-- The chromatic number: minimum k such that a proper k-coloring exists -/
noncomputable def chromaticNumber {V : Type*} (G : GraphOn V) : Cardinal :=
  ⨅ k : Cardinal, if ∃ c : V → k.toType, IsProperColoring G k c then k else ⊤

/-- A graph is k-colorable -/
def IsColorable {V : Type*} (G : GraphOn V) (k : Cardinal) : Prop :=
  ∃ c : V → k.toType, IsProperColoring G k c

/-
# Part 3: Order Type and Subgraphs

We need to talk about subgraphs whose vertex sets have smaller order type.
-/

/-- The order type of a subset of a well-ordered type -/
noncomputable def orderTypeOfSubset {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]
    (S : Set α) : Ordinal :=
  Ordinal.type (Subrel (· < ·) S)

/-- Induced subgraph on a vertex subset -/
def inducedSubgraph {V : Type*} (G : GraphOn V) (S : Set V) : GraphOn S where
  adj := fun x y => G.adj x.val y.val
  symm := fun x y h => G.symm x.val y.val h
  loopless := fun x => G.loopless x.val

/-
# Part 4: The Erdős-Hajnal Construction

Erdős and Hajnal constructed a graph on ω₁² showing Babai's theorem doesn't
generalize to higher cardinals.
-/

/-- The Erdős-Hajnal graph on ω₁²:
    (x_α, y_β) is adjacent to (x_γ, y_δ) iff α < γ and β > δ or α > γ and β < δ.
    This is a "shift graph" where adjacency requires the two coordinates to move
    in opposite directions. (Previously axiomatized; now concretely defined.) -/
def erdosHajnalGraph : GraphOn omega1Squared where
  adj := fun p q => (p.1 < q.1 ∧ q.2 < p.2) ∨ (q.1 < p.1 ∧ p.2 < q.2)
  symm := fun _ _ h => h.symm
  loopless := fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h

/-- The E-H graph has chromatic number ℵ₁ -/
axiom erdosHajnal_chromatic : chromaticNumber erdosHajnalGraph = ℵ₁

/-- Every strictly smaller subgraph has chromatic number ≤ ℵ₀ -/
axiom erdosHajnal_subgraph (S : Set omega1Squared)
    (hS : orderTypeOfSubset S < omega1 * omega1) :
  chromaticNumber (inducedSubgraph erdosHajnalGraph S) ≤ ℵ₀

/-
# Part 5: The Main Questions

The problem asks about analogous constructions at higher cardinals.
-/

/-- Question 1: Does there exist a graph G on ω₂² with:
    - χ(G) = ℵ₂
    - Every subgraph of smaller order type has χ ≤ ℵ₀ -/
def Question1 : Prop :=
  ∃ G : GraphOn omega2Squared,
    chromaticNumber G = ℵ₂ ∧
    ∀ S : Set omega2Squared, orderTypeOfSubset S < omega2 * omega2 →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀

/-- Question 2: What if we ask for χ(G) = ℵ₁ instead? -/
def Question2 : Prop :=
  ∃ G : GraphOn omega2Squared,
    chromaticNumber G = ℵ₁ ∧
    ∀ S : Set omega2Squared, orderTypeOfSubset S < omega2 * omega2 →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀

/-
# Part 6: Known Partial Results

There are some constructions that partially address these questions.
-/

/-- A graph on ω₂² with χ = ℵ₂ where smaller subgraphs have χ ≤ ℵ₁ -/
axiom partialConstruction : ∃ G : GraphOn omega2Squared,
  chromaticNumber G = ℵ₂ ∧
  ∀ S : Set omega2Squared, orderTypeOfSubset S < omega2 * omega2 →
    chromaticNumber (inducedSubgraph G S) ≤ ℵ₁

/-- The partial construction gives a weaker bound (≤ ℵ₁ instead of ≤ ℵ₀)
    so it does not directly answer Question1. The gap between ℵ₀ and ℵ₁ is
    precisely what makes Question1 open. -/

/-
# Part 7: Generalization to Higher Cardinals

The questions can be generalized to arbitrary cardinals.
-/

/-- General question for cardinals κ, λ, μ:
    Does there exist a graph on κ² with χ = λ where smaller subgraphs have χ ≤ μ? -/
def GeneralQuestion (κ λ μ : Cardinal) : Prop :=
  ∃ G : GraphOn (κ.toType × κ.toType),
    chromaticNumber G = λ ∧
    ∀ S : Set (κ.toType × κ.toType),
      Cardinal.mk S < κ * κ →
        chromaticNumber (inducedSubgraph G S) ≤ μ

/-- Question1 is the special case κ = ℵ₂, λ = ℵ₂, μ = ℵ₀ -/
theorem question1_is_general : Question1 ↔ GeneralQuestion ℵ₂ ℵ₂ ℵ₀ := by
  sorry

/-- The Erdős-Hajnal result is the case κ = ℵ₁, λ = ℵ₁, μ = ℵ₀ -/
theorem erdosHajnal_is_general : GeneralQuestion ℵ₁ ℵ₁ ℵ₀ := by
  sorry

/-
# Part 8: Connection to Babai's Theorem

Babai's theorem concerns graphs on well-ordered sets.
-/

/-- Babai's theorem (simplified): For countable ordinals, chromatic constraints
    propagate nicely from subgraphs -/
axiom babai_theorem :
  ∀ G : GraphOn (ω.toType), chromaticNumber G ≤ ℵ₀ →
    ∀ S : Set ω.toType, chromaticNumber (inducedSubgraph G S) ≤ ℵ₀

/-- The E-H construction shows Babai doesn't extend to ω₁ -/
theorem babai_fails_omega1 : ¬(∀ G : GraphOn omega1Squared,
    (∀ S : Set omega1Squared, orderTypeOfSubset S < omega1 * omega1 →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀) →
    chromaticNumber G ≤ ℵ₀) := by
  intro h
  have hle := h erdosHajnalGraph erdosHajnal_subgraph
  rw [erdosHajnal_chromatic] at hle
  -- ℵ₁ ≤ ℵ₀ contradicts ℵ₀ < ℵ₁
  exact absurd hle (not_le.mpr (Cardinal.aleph0_lt_aleph 1))

/-
# Part 9: Problem Status

Both questions remain open.
-/

/-- Main formal statement: Question 1 (stronger version) -/
def ErdosProblem919Part1 : Prop := Question1

/-- Main formal statement: Question 2 (weaker version) -/
def ErdosProblem919Part2 : Prop := Question2

/-- Summary of what we know -/
theorem summary :
    -- Erdős-Hajnal construction exists
    (∃ G : GraphOn omega1Squared,
      chromaticNumber G = ℵ₁ ∧
      ∀ S, orderTypeOfSubset S < omega1 * omega1 →
        chromaticNumber (inducedSubgraph G S) ≤ ℵ₀) ∧
    -- Partial result for ω₂² exists
    (∃ G : GraphOn omega2Squared,
      chromaticNumber G = ℵ₂ ∧
      ∀ S, orderTypeOfSubset S < omega2 * omega2 →
        chromaticNumber (inducedSubgraph G S) ≤ ℵ₁) := by
  constructor
  · exact ⟨erdosHajnalGraph, erdosHajnal_chromatic, erdosHajnal_subgraph⟩
  · exact partialConstruction

/-
# Part 10: Formal Problem Statement

The precise statement of Erdős Problem #919.
-/

/-- The questions imply existence of graphs with high chromatic number -/
theorem question1_implies_exists :
    Question1 → ∃ G : GraphOn omega2Squared, chromaticNumber G = ℵ₂ :=
  fun ⟨G, hchi, _⟩ => ⟨G, hchi⟩

theorem question2_implies_exists :
    Question2 → ∃ G : GraphOn omega2Squared, chromaticNumber G = ℵ₁ :=
  fun ⟨G, hchi, _⟩ => ⟨G, hchi⟩

end Erdos919
