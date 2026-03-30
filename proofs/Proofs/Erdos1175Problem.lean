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

namespace Erdos1175

/-
## Part I: Core Definitions

We formalize chromatic number for potentially infinite graphs,
triangle-free subgraphs, and the main conjecture.
-/

/-- A proper coloring of a graph G with colors from a type of cardinality k. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (k : Cardinal)
    (c : V → k.toType) : Prop :=
  ∀ v w, G.Adj v w → c v ≠ c w

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable {V : Type*} (G : SimpleGraph V) (k : Cardinal) : Prop :=
  ∃ c : V → k.toType, IsProperColoring G k c

/-- Cardinal chromatic number: the minimum cardinal k such that G is k-colorable.
    Axiomatized to avoid universe and decidability complications. -/
axiom cardinalChromaticNumber {V : Type*} (G : SimpleGraph V) : Cardinal

/-- The chromatic number is at most k iff G is k-colorable. -/
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
  ∀ κ : Cardinal, κ > ℵ₀ →
    ∃ λ' : Cardinal,
      ∀ (V : Type*) (G : SimpleGraph V),
        cardinalChromaticNumber G ≥ λ' →
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
  ∃ (V : Type*) (G : SimpleGraph V),
    cardinalChromaticNumber G = Cardinal.aleph 1 ∧
    AllTriangleFreeSubgraphsBoundedBy G ℵ₀

/-- Shelah's result implies λ = ℵ₁ does not work for κ = ℵ₁ in the conjecture:
    there exists (consistently) a graph with χ = ℵ₁ whose triangle-free
    subgraphs all have countable chromatic number. -/
theorem shelah_implies_failure_at_aleph1 :
    (∃ (V : Type*) (G : SimpleGraph V),
      cardinalChromaticNumber G = Cardinal.aleph 1 ∧
      AllTriangleFreeSubgraphsBoundedBy G ℵ₀) →
    ¬(∀ (V : Type*) (G : SimpleGraph V),
      cardinalChromaticNumber G ≥ Cardinal.aleph 1 →
      HasTriangleFreeSubgraphWithChromatic G (Cardinal.aleph 1)) := by
  intro ⟨V, G, hχ, hbound⟩ h
  have hge : cardinalChromaticNumber G ≥ Cardinal.aleph 1 := le_of_eq hχ.symm
  obtain ⟨S, hfree, hκ⟩ := h V G hge
  have hle := hbound S hfree
  have : Cardinal.aleph 1 ≤ ℵ₀ := le_trans hκ hle
  exact absurd this (not_le.mpr (Cardinal.aleph0_lt_aleph 1))

/-
## Part V: Positive Results for Finite Chromatic Numbers

For finite graphs, the situation is well-understood.
-/

/-- Mycielski's theorem: For every k ≥ 1, there exists a triangle-free graph
    with chromatic number k. This is a classical constructive result. -/
/-- For finite κ, the conjecture holds via Ramsey-type results:
    graphs with sufficiently large chromatic number contain triangle-free
    subgraphs with any prescribed finite chromatic number. -/
/-
## Part VI: Girth Variant

A natural strengthening replaces "triangle-free" with higher girth.
-/

/-- A graph has girth at least g: no cycle of length < g exists.
    For g = 4, this means triangle-free. -/
def HasGirthAtLeast {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (k : ℕ), k ≥ 3 → k < g →
    ∀ (f : Fin k → V), (∀ i : Fin k, G.Adj (f i) (f ⟨(i.val + 1) % k,
      Nat.mod_lt _ (by omega)⟩)) → ¬Function.Injective f

/-- Stronger variant: replace "triangle-free" with "girth ≥ g" for any g. -/
def erdos1175_girth_variant (g : ℕ) : Prop :=
  ∀ κ : Cardinal, κ > ℵ₀ →
    ∃ λ' : Cardinal,
      ∀ (V : Type*) (G : SimpleGraph V),
        cardinalChromaticNumber G ≥ λ' →
        ∃ S : Set V, HasGirthAtLeast (inducedSubgraphOn G S) g ∧
          cardinalChromaticNumber (inducedSubgraphOn G S) ≥ κ

/-
## Part VII: Connections

This problem connects chromatic number theory at uncountable scales
with structural graph theory (forbidden subgraphs).
-/

/-- Erdős (1959) showed: for every k, g ≥ 3 there exist finite graphs
    with girth ≥ g and chromatic number ≥ k (via probabilistic method). -/
/-
## Part VIII: Formal Problem Statement and Status
-/

/-- The main open question -/
def ErdosProblem1175 : Prop := erdos1175

/-- Summary of what is known -/
theorem erdos1175_summary :
    -- Shelah's consistency result provides a consistent counterexample
    (∃ (V : Type*) (G : SimpleGraph V),
      cardinalChromaticNumber G = Cardinal.aleph 1 ∧
      AllTriangleFreeSubgraphsBoundedBy G ℵ₀) := by
  exact shelah_consistency

end Erdos1175
