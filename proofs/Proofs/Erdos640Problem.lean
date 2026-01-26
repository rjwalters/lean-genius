/-!
# Erdős Problem #640: Chromatic Number of Odd Cycle Spans

**Source:** [erdosproblems.com/640](https://erdosproblems.com/640)
**Status:** OPEN (Erdős–Hajnal)

## Statement

Let k ≥ 3. Does there exist some f(k) such that if a graph G has
chromatic number χ(G) ≥ f(k), then G must contain some odd cycle
whose vertices span a subgraph of chromatic number ≥ k?

## Background

- Trivially true for k = 3: any graph with χ ≥ 3 is non-bipartite,
  so it contains an odd cycle, and all odd cycles have χ = 3.
- Raphael Steiner observed this is equivalent to replacing "odd cycle"
  with "path."
- The problem appears in [Er97d, p.84].

## Approach

We formalize the conjecture using Mathlib's `SimpleGraph` API.
The key definitions capture:
1. Chromatic number (via graph coloring)
2. Odd cycles in a graph
3. Induced subgraph on cycle vertices
4. The conjectured threshold function f(k)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open SimpleGraph

namespace Erdos640

/-! ## Part I: Chromatic Number -/

/--
A graph G on vertex type V is k-colorable if there exists a proper
coloring using at most k colors (modeled as `Fin k`).
-/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ v w : V, G.Adj v w → c v ≠ c w

/--
The chromatic number of G: the smallest k such that G is k-colorable.
For formalization we define it as an `ℕ` using `Nat.find`.
-/
noncomputable def chromaticNumber [Fintype V] [DecidableEq V]
    [DecidableRel (SimpleGraph.Adj (G : SimpleGraph V))]
    (G : SimpleGraph V) : ℕ :=
  if h : ∃ k : ℕ, IsKColorable G k then Nat.find h else 0

/-! ## Part II: Odd Cycles -/

/--
An odd cycle of length 2m + 1 in G is a closed walk of odd length
that visits distinct vertices. We represent it by its vertex set.
-/
def HasOddCycleWithVertices (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.card ≥ 3 ∧
  Odd S.card ∧
  -- All vertices in S are pairwise reachable in G
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w → G.Adj v w ∨ G.Reachable v w) ∧
  -- S forms a cycle: there exists a cyclic ordering
  ∃ (σ : Fin S.card → V),
    Function.Injective σ ∧
    (∀ i : Fin S.card, σ i ∈ S) ∧
    (∀ i : Fin S.card, G.Adj (σ i) (σ ⟨(i.val + 1) % S.card, Nat.mod_lt _ (by omega)⟩))

/-! ## Part III: Induced Subgraph Chromatic Number -/

/--
The induced subgraph of G on a vertex set S.
-/
def inducedSubgraph (G : SimpleGraph V) (S : Set V) : SimpleGraph S where
  Adj v w := G.Adj v.val w.val
  symm v w h := G.symm h
  loopless v h := G.loopless v.val h

/--
The span chromatic number: the chromatic number of the subgraph
induced on the vertex set S.
We state this as a predicate: the induced subgraph on S has χ ≥ k.
-/
def InducedChromaticAtLeast (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ¬IsKColorable (inducedSubgraph G (↑S : Set V)) (k - 1)

/-! ## Part IV: The Erdős–Hajnal Conjecture -/

/--
**Erdős Problem #640 (Erdős–Hajnal):**
For every k ≥ 3, there exists f(k) such that every graph G with
χ(G) ≥ f(k) contains an odd cycle whose vertices span a subgraph
of chromatic number ≥ k.
-/
def ErdosHajnalConjecture640 : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ fk : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        chromaticNumber G ≥ fk →
        ∃ S : Finset V,
          HasOddCycleWithVertices G S ∧
          InducedChromaticAtLeast G S k

/--
**Steiner's equivalence:**
The conjecture is equivalent when "odd cycle" is replaced by "path."
-/
def SteinerPathVariant : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ fk : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        chromaticNumber G ≥ fk →
        ∃ S : Finset V,
          -- S is the vertex set of a path in G
          (∃ (σ : Fin S.card → V),
            Function.Injective σ ∧
            (∀ i : Fin S.card, σ i ∈ S) ∧
            (∀ i : Fin (S.card - 1),
              G.Adj (σ ⟨i.val, by omega⟩) (σ ⟨i.val + 1, by omega⟩))) ∧
          InducedChromaticAtLeast G S k

axiom steiner_equivalence :
  ErdosHajnalConjecture640 ↔ SteinerPathVariant

/-! ## Part V: The Trivial Case k = 3 -/

/--
**Trivial case:** For k = 3, f(3) = 3 works.
Any graph with χ ≥ 3 is non-bipartite, hence contains an odd cycle.
Every odd cycle has chromatic number exactly 3.
-/
axiom trivial_case_k3 :
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    chromaticNumber G ≥ 3 →
    ∃ S : Finset V,
      HasOddCycleWithVertices G S ∧
      InducedChromaticAtLeast G S 3

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #640 asks whether high chromatic number forces odd cycles
with high-chromatic spans. The k=3 case is trivial; the general case
remains open. Steiner showed the path variant is equivalent.
-/
theorem erdos_640_summary :
    (ErdosHajnalConjecture640 ↔ SteinerPathVariant) :=
  steiner_equivalence

end Erdos640
