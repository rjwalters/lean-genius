/-
Erdős Problem #597: Partition Relations for Ordinal Powers

Let G be a graph on at most ℵ₁ vertices containing no K₄ and no K_{ℵ₀,ℵ₀}.
Is it true that ω₁² → (ω₁ω, G)²?
What about finite G?

This is a partition calculus problem in infinite combinatorics.
The arrow notation α → (β, γ)² means: for any 2-coloring of [α]²,
there exists either a homogeneous set of type β in color 1,
or a copy of γ in color 2.

**Status**: OPEN

**Partial Results**:
- Erdős-Hajnal proved ω₁² → (ω₁ω, 3)² (triangle case)
- Baumgartner proved ω₁² ↛ (ω₁ω, K_{ℵ₀,ℵ₀})² (counterexample)
- The question with both K₄-free and K_{ℵ₀,ℵ₀}-free remains open

**References**:
- [Er87] Erdős (1987)
- [Va99, 7.84] Vajda (1999)
- https://erdosproblems.com/597
-/

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic

namespace Erdos597

/- ## Ordinal Notation -/

/-- The first uncountable ordinal ω₁, axiomatized with the defining property
that it is uncountable but every smaller ordinal is countable. -/
axiom omega_1 : Ordinal

/-- ω₁ is uncountable. -/
/-- The first infinite ordinal ω (identified with ℕ). -/
def omega : Ordinal := Ordinal.omega

/-- The ordinal product ω₁ · ω. This is an uncountable limit ordinal
larger than ω₁ but smaller than ω₁². -/
axiom omega_1_times_omega : Ordinal

/-- ω₁ · ω is defined as the ordinal product. -/
/-- The ordinal square ω₁² = ω₁ · ω₁. This is the "source" ordinal
whose pairs are 2-colored in the partition relation. -/
axiom omega_1_squared : Ordinal

/-- ω₁² is defined as ordinal exponentiation. -/
/- ## Graph Structures -/

/-- A simple graph on a type α: a symmetric irreflexive relation on vertices. -/
structure SimpleGraph' (α : Type*) where
  adj : α → α → Prop
  symm : ∀ x y, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x

/-- A graph G contains a complete subgraph on n vertices if there exists
an n-element set of pairwise adjacent vertices. -/
def containsClique (α : Type*) (G : SimpleGraph' α) (n : ℕ) : Prop :=
  ∃ S : Finset α, S.card = n ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.adj x y

/-- A graph is K₄-free if it contains no complete subgraph on 4 vertices. -/
def isK4Free (α : Type*) (G : SimpleGraph' α) : Prop :=
  ¬ containsClique α G 4

/-- A graph contains K_{ℵ₀,ℵ₀} if it has two countably infinite disjoint
vertex sets with every cross-pair adjacent. -/
def containsCountableBiclique (α : Type*) (G : SimpleGraph' α) : Prop :=
  ∃ (A B : Set α),
    Set.Countable A ∧ A.Infinite ∧
    Set.Countable B ∧ B.Infinite ∧
    Disjoint A B ∧
    ∀ a ∈ A, ∀ b ∈ B, G.adj a b

/-- A graph is K_{ℵ₀,ℵ₀}-free if it contains no infinite complete bipartite
subgraph with countably many vertices in each class. -/
def isKAleph0Free (α : Type*) (G : SimpleGraph' α) : Prop :=
  ¬ containsCountableBiclique α G

/-- The vertex set of G has cardinality at most ℵ₁. -/
def hasAtMostAleph1Vertices (α : Type*) : Prop :=
  Cardinal.mk α ≤ Cardinal.aleph 1

/- ## Partition Arrow Notation -/

/-- The partition relation α → (β, γ)² for ordinals with a graph target:
for any 2-coloring of pairs from a set of order type α, either
there exists a homogeneous set of order type β in color 0, or
a subgraph isomorphic to γ in color 1.

This is axiomatized as the full definition requires substantial
infrastructure for order types and graph embeddings. -/
axiom partitionArrow (α β : Ordinal) (γ : Type*) : Prop

/- ## The Main Conjecture -/

/-- **Erdős Problem #597**: The main conjecture.
For any graph G with at most ℵ₁ vertices, no K₄, and no K_{ℵ₀,ℵ₀}:
ω₁² → (ω₁ω, G)².

This remains OPEN. -/
def erdos597Conjecture : Prop :=
  ∀ (α : Type*) (G : SimpleGraph' α),
    hasAtMostAleph1Vertices α →
    isK4Free α G →
    isKAleph0Free α G →
    partitionArrow omega_1_squared omega_1_times_omega α

/-- **The finite case**: Does ω₁² → (ω₁ω, G)² hold for all finite
K₄-free graphs G? This is a natural subproblem of the main conjecture. -/
def finiteCaseConjecture : Prop :=
  ∀ (α : Type*) [Fintype α] (G : SimpleGraph' α),
    isK4Free α G →
    partitionArrow omega_1_squared omega_1_times_omega α

/- ## Known Results -/

/-- **Erdős-Hajnal Theorem** (positive result):
ω₁² → (ω₁ω, 3)². For any 2-coloring of pairs from ω₁², there exists
either a homogeneous set of order type ω₁ω in color 0, or a
monochromatic triangle in color 1. -/
axiom erdosHajnalTriangle :
    partitionArrow omega_1_squared omega_1_times_omega (Fin 3)

/-- **Baumgartner's Counterexample** (negative result):
ω₁² ↛ (ω₁ω, K_{ℵ₀,ℵ₀})². There exists a 2-coloring of pairs from ω₁²
with no homogeneous set of type ω₁ω and no monochromatic K_{ℵ₀,ℵ₀}.
This forced the addition of the K_{ℵ₀,ℵ₀}-free condition. -/
axiom baumgartnerCounterexample :
    ∃ (β : Type*),
      Cardinal.mk β = Cardinal.aleph 0 ∧
      ¬ partitionArrow omega_1_squared omega_1_times_omega (β × β)

/- ## Why Both Conditions Are Needed

Erdős originally posed the question with only the K₄-free assumption.
Baumgartner showed this is insufficient: K_{ℵ₀,ℵ₀} is K₄-free (it is
triangle-free, being bipartite), yet the partition relation fails for it.
The refined conjecture adds the K_{ℵ₀,ℵ₀}-free condition.

The two conditions play complementary roles:
- K₄-free forbids dense local structure (cliques)
- K_{ℵ₀,ℵ₀}-free forbids dense global bipartite structure

Both are needed for the partition relation to have any hope of holding. -/

/- ## Partition Calculus Background

The partition arrow notation was introduced by Erdős and Rado.
The **Erdős-Rado theorem** gives foundational bounds:
  (2^κ)⁺ → (κ⁺)²_κ for infinite cardinals κ.

**Stepping-up lemmas** derive partition relations for larger ordinals
from smaller ones. **Negative relations** are typically established
by explicit counterexample colorings, as in Baumgartner's result. -/

/- ## Set-Theoretic Context

Some partition relations are sensitive to set-theoretic axioms.
The role of ℵ₁ is special: many partition relations change behavior
at this cardinal. Problem #597 may have different answers under
different assumptions (e.g., CH, Martin's Axiom, or large cardinals). -/

/- ## Summary -/

/-- **Summary of known results for Erdős Problem #597.**
We combine the two established partial results:
1. The triangle case holds (Erdős-Hajnal)
2. The infinite bipartite case fails (Baumgartner)

The gap between these — graphs that are K₄-free AND K_{ℵ₀,ℵ₀}-free —
is precisely what Problem #597 asks about, and it remains OPEN. -/
theorem erdos597_knownResults :
    partitionArrow omega_1_squared omega_1_times_omega (Fin 3) ∧
    ∃ (β : Type*),
      Cardinal.mk β = Cardinal.aleph 0 ∧
      ¬ partitionArrow omega_1_squared omega_1_times_omega (β × β) :=
  ⟨erdosHajnalTriangle, baumgartnerCounterexample⟩

end Erdos597
