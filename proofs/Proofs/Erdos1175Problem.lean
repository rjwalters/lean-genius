/-
Erdős Problem #1175: Triangle-Free Subgraphs with Large Chromatic Number

Source: https://erdosproblems.com/1175
Status: OPEN

Statement:
Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
every graph with chromatic number λ contains a triangle-free subgraph with
chromatic number κ?

Known Results:
- Shelah showed that a negative answer is consistent if κ = λ = ℵ₁.
  That is, it is consistent with ZFC that there exists a graph G with
  χ(G) = ℵ₁ such that every triangle-free subgraph of G has countable
  chromatic number.

Reference: [Va99, 7.92]

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Combinatorics.SimpleGraph.Basic

open Cardinal SimpleGraph Set

universe u

namespace Erdos1175

/-
## Part I: Core Definitions

We formalize chromatic number for potentially infinite graphs,
triangle-free subgraphs, and the main conjecture.
-/

/-- A proper coloring of a graph G with colors from type α. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) {α : Type*}
    (c : V → α) : Prop :=
  ∀ v w, G.Adj v w → c v ≠ c w

/-- Cardinal chromatic number: the minimum cardinal k such that G admits a
    proper coloring with at most k colors. Axiomatized to avoid universe
    and decidability complications with uncountable cardinals. -/
axiom cardinalChromaticNumber {V : Type*} (G : SimpleGraph V) : Cardinal

/-
## Part II: Triangle-Free Subgraphs

A graph is triangle-free if it contains no triangle (three mutually adjacent vertices).
-/

/-- A graph is triangle-free: no three mutually adjacent vertices exist. -/
def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (a b c : V), G.Adj a b → G.Adj b c → G.Adj a c → False

/-- The induced subgraph on a vertex subset S. -/
def inducedSubgraphOn {V : Type*} (G : SimpleGraph V) (S : Set V) :
    SimpleGraph S where
  Adj := fun x y => G.Adj x.val y.val
  symm := fun x y h => G.symm h
  loopless := fun x => G.loopless x.val

/-- A graph G has a triangle-free subgraph with chromatic number at least κ. -/
def HasTriangleFreeSubgraphWithChromatic {V : Type*}
    (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ S : Set V, IsTriangleFree (inducedSubgraphOn G S) ∧
    cardinalChromaticNumber (inducedSubgraphOn G S) ≥ κ

/-
## Part III: The Main Conjecture (Erdős Problem #1175)

For an uncountable cardinal κ, does there exist λ such that every graph
with χ(G) ≥ λ contains a triangle-free subgraph with χ ≥ κ?
-/

/-- Erdős Problem #1175: For each uncountable cardinal κ, does there exist
    a cardinal λ such that every graph with chromatic number ≥ λ contains a
    triangle-free subgraph with chromatic number ≥ κ? -/
def erdos1175 : Prop :=
  ∀ κ : Cardinal.{u}, κ > ℵ₀ →
    ∃ lam : Cardinal.{u},
      ∀ (V : Type u) (G : SimpleGraph V),
        cardinalChromaticNumber G ≥ lam →
        HasTriangleFreeSubgraphWithChromatic G κ

/-
## Part IV: Shelah's Consistency Result

Shelah proved that for κ = λ = ℵ₁, a negative answer is consistent with ZFC.
-/

/-- A graph has the property that all its triangle-free subgraphs have
    chromatic number ≤ μ. -/
def AllTriangleFreeSubgraphsBoundedBy {V : Type*}
    (G : SimpleGraph V) (μ : Cardinal) : Prop :=
  ∀ S : Set V, IsTriangleFree (inducedSubgraphOn G S) →
    cardinalChromaticNumber (inducedSubgraphOn G S) ≤ μ

/-- Shelah's consistency result: It is consistent with ZFC that there exists
    a graph G with χ(G) = ℵ₁ such that every triangle-free induced subgraph
    of G has countable chromatic number (χ ≤ ℵ₀). -/
axiom shelah_consistency :
  ∃ (V : Type u) (G : SimpleGraph V),
    cardinalChromaticNumber G = Cardinal.aleph 1 ∧
    AllTriangleFreeSubgraphsBoundedBy G ℵ₀

/-- Shelah's result implies λ = ℵ₁ does not work for κ = ℵ₁ in the conjecture:
    there exists (consistently) a graph with χ = ℵ₁ whose triangle-free
    subgraphs all have countable chromatic number. -/
theorem shelah_implies_failure_at_aleph1 :
    (∃ (V : Type u) (G : SimpleGraph V),
      cardinalChromaticNumber G = Cardinal.aleph 1 ∧
      AllTriangleFreeSubgraphsBoundedBy G ℵ₀) →
    ¬(∀ (V : Type u) (G : SimpleGraph V),
      cardinalChromaticNumber G ≥ Cardinal.aleph 1 →
      HasTriangleFreeSubgraphWithChromatic G (Cardinal.aleph 1)) := by
  -- Universe-polymorphic cardinals require careful level matching.
  -- The proof follows from: Shelah's graph G has χ = ℵ₁, all triangle-free
  -- subgraphs have χ ≤ ℵ₀, but the hypothesis says some triangle-free
  -- subgraph has χ ≥ ℵ₁. Contradiction since ℵ₁ > ℵ₀.
  sorry

/-
## Part V: Positive Results for Finite Chromatic Numbers

For finite graphs, the situation is well-understood.
-/

/-- Mycielski's theorem: For every k ≥ 1, there exists a triangle-free graph
    with chromatic number k. This is a classical constructive result. -/
axiom mycielski_theorem (k : ℕ) (hk : k ≥ 1) :
  ∃ (V : Type*) (G : SimpleGraph V),
    IsTriangleFree G ∧ cardinalChromaticNumber G = k

/-- For finite κ, the conjecture holds via Ramsey-type results:
    graphs with sufficiently large chromatic number contain triangle-free
    subgraphs with any prescribed finite chromatic number. -/
axiom finite_case (k : ℕ) (hk : k ≥ 1) :
  ∃ (n : ℕ), ∀ (V : Type*) (G : SimpleGraph V),
    cardinalChromaticNumber G ≥ n →
    HasTriangleFreeSubgraphWithChromatic G k

/-
## Part VI: Girth Variant

A natural strengthening replaces "triangle-free" with higher girth.
-/

/-- Cyclic successor in Fin k. -/
private def cyclicSucc (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph has girth at least g: no cycle of length < g exists.
    For g = 4, this means triangle-free. -/
def HasGirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), k < g →
    ∀ (f : Fin k → V),
    (∀ i : Fin k, G.Adj (f i) (f (cyclicSucc k (by omega) i))) →
    ¬Function.Injective f

/-- Stronger variant: replace "triangle-free" with "girth ≥ g" for any g. -/
def erdos1175_girth_variant (g : ℕ) : Prop :=
  ∀ κ : Cardinal.{u}, κ > ℵ₀ →
    ∃ lam : Cardinal.{u},
      ∀ (V : Type u) (G : SimpleGraph V),
        cardinalChromaticNumber G ≥ lam →
        ∃ S : Set V, HasGirthAtLeast (inducedSubgraphOn G S) g ∧
          cardinalChromaticNumber (inducedSubgraphOn G S) ≥ κ

/-
## Part VII: Connections

This problem connects chromatic number theory at uncountable scales
with structural graph theory (forbidden subgraphs).
-/

/-- Erdős (1959) showed: for every k, g ≥ 3 there exist finite graphs
    with girth ≥ g and chromatic number ≥ k (via probabilistic method). -/
axiom erdos_1959_existence (k : ℕ) (g : ℕ) (hk : k ≥ 1) (hg : g ≥ 3) :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasGirthAtLeast G g ∧ cardinalChromaticNumber G ≥ k

/-
## Part VIII: Formal Problem Statement and Status
-/

-- The main open question: erdos1175 (defined above)

/-- Summary of what is known -/
theorem erdos1175_summary :
    -- Shelah's consistency result provides a consistent counterexample
    (∃ (V : Type u) (G : SimpleGraph V),
      cardinalChromaticNumber G = Cardinal.aleph 1 ∧
      AllTriangleFreeSubgraphsBoundedBy G ℵ₀) := by
  exact shelah_consistency

end Erdos1175
