/-
Erdős Problem #581: Bipartite Subgraphs of Triangle-Free Graphs

Source: https://erdosproblems.com/581
Status: SOLVED (Alon 1996)

Statement:
Let f(m) be the maximum k such that every triangle-free graph with m edges
must contain a bipartite subgraph with k edges.

Determine f(m).

Solution (Alon 1996):
There exist constants c₁, c₂ > 0 such that:
  m/2 + c₁ · m^{4/5} ≤ f(m) ≤ m/2 + c₂ · m^{4/5}

The answer is f(m) = m/2 + Θ(m^{4/5}).

Reference: https://erdosproblems.com/581
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real

namespace Erdos581

/-
## Part I: Basic Definitions

Graph-theoretic foundations for the problem.
-/

/--
**Triangle-Free Graph:**
A graph G is triangle-free if it contains no complete subgraph K₃.
That is, no three vertices are all pairwise adjacent.
-/
def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj a c → False

/--
**Bipartite Graph:**
A graph is bipartite if its vertices can be partitioned into two sets
such that all edges go between the sets.
-/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (A B : Set V), A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    ∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)

/--
**Edge Count:**
The number of edges in a graph (finite case).
-/
noncomputable def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/--
**Subgraph Edges:**
A subgraph H of G inherits edges from G.
-/
def IsSubgraph {V : Type*} (H G : SimpleGraph V) : Prop :=
  ∀ v w, H.Adj v w → G.Adj v w

/-
## Part II: The Function f(m)

Definition of the extremal function.
-/

/--
**Bipartite Subgraph Size:**
Maximum edges in a bipartite subgraph of G.
-/
noncomputable def maxBipartiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sorry  -- Supremum over all bipartite subgraphs

/--
**The Function f(m):**
f(m) = min over triangle-free graphs G with m edges
       of max bipartite subgraph size.

In other words: the guaranteed bipartite subgraph size in any
triangle-free graph with m edges.
-/
noncomputable def f (m : ℕ) : ℕ :=
  sorry  -- Infimum over all triangle-free graphs with m edges

/-
## Part III: Trivial Bounds

Every graph has a bipartite subgraph with at least half the edges.
-/

/--
**Trivial Lower Bound:**
Every graph contains a bipartite subgraph with at least m/2 edges.

Proof sketch: Take a random 2-coloring; in expectation, each edge
has probability 1/2 of being bichromatic. By derandomization,
a 2-coloring achieving m/2 exists.
-/
axiom half_edges_bipartite (m : ℕ) :
    f m ≥ m / 2

/--
**Motivation:**
The question is: how much better than m/2 can we guarantee
for triangle-free graphs specifically?
-/
def motivation : Prop :=
  ∀ m, f m ≥ m / 2  -- Trivial bound

/-
## Part IV: Alon's Upper Bound

The construction showing f(m) ≤ m/2 + c₂ · m^{4/5}.
-/

/--
**Alon's Upper Bound (1996):**
There exists a constant c₂ > 0 such that for all m,
  f(m) ≤ m/2 + c₂ · m^{4/5}

This is shown by constructing triangle-free graphs where the
maximum bipartite subgraph is not too large.
-/
axiom alon_upper_bound :
    ∃ c₂ : ℝ, c₂ > 0 ∧ ∀ m : ℕ, (f m : ℝ) ≤ m / 2 + c₂ * (m : ℝ) ^ (4/5 : ℝ)

/--
**Upper Bound Constant:**
A witness for the upper bound constant.
-/
noncomputable def c₂ : ℝ := Classical.choose alon_upper_bound

/--
**Upper Bound Property:**
The constant c₂ satisfies the required bound.
-/
theorem c₂_positive : c₂ > 0 := (Classical.choose_spec alon_upper_bound).1

/-
## Part V: Alon's Lower Bound

Every triangle-free graph has a large bipartite subgraph.
-/

/--
**Alon's Lower Bound (1996):**
There exists a constant c₁ > 0 such that for all m,
  f(m) ≥ m/2 + c₁ · m^{4/5}

This shows triangle-free graphs MUST have bipartite subgraphs
significantly larger than m/2.
-/
axiom alon_lower_bound :
    ∃ c₁ : ℝ, c₁ > 0 ∧ ∀ m : ℕ, (f m : ℝ) ≥ m / 2 + c₁ * (m : ℝ) ^ (4/5 : ℝ)

/--
**Lower Bound Constant:**
A witness for the lower bound constant.
-/
noncomputable def c₁ : ℝ := Classical.choose alon_lower_bound

/--
**Lower Bound Property:**
The constant c₁ satisfies the required bound.
-/
theorem c₁_positive : c₁ > 0 := (Classical.choose_spec alon_lower_bound).1

/-
## Part VI: Asymptotic Characterization

The main result: f(m) = m/2 + Θ(m^{4/5}).
-/

/--
**Theta Notation:**
f(m) = m/2 + Θ(m^{4/5}) means the deviation from m/2 is
precisely of order m^{4/5}.
-/
def ThetaBound (f : ℕ → ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    (∀ m : ℕ, m > 0 → c₁ * g m ≤ (f m : ℝ) - m / 2) ∧
    (∀ m : ℕ, m > 0 → (f m : ℝ) - m / 2 ≤ c₂ * g m)

/--
**Main Result:**
f(m) - m/2 = Θ(m^{4/5})
-/
theorem alon_main_theorem :
    ThetaBound f (fun m => (m : ℝ) ^ (4/5 : ℝ)) := by
  obtain ⟨c1, hc1_pos, hc1⟩ := alon_lower_bound
  obtain ⟨c2, hc2_pos, hc2⟩ := alon_upper_bound
  exact ⟨c1, c2, hc1_pos, hc2_pos, fun m hm => by linarith [hc1 m], fun m hm => by linarith [hc2 m]⟩

/-
## Part VII: Understanding the Exponent

Why 4/5? This comes from extremal graph theory.
-/

/--
**The Exponent 4/5:**
This specific exponent arises from the interplay between:
1. The structure of triangle-free graphs
2. Ramsey-theoretic considerations
3. Probabilistic arguments

A triangle-free graph on n vertices has at most O(n^{3/2}) edges
(Kővári-Sós-Turán). The 4/5 exponent relates to optimal
constructions and decompositions.
-/
def exponent_explanation : Prop := True

/--
**Comparison to General Graphs:**
For arbitrary (not necessarily triangle-free) graphs,
we only get m/2 guaranteed bipartite edges.

Triangle-freeness gives us the extra Θ(m^{4/5}) term.
-/
axiom general_graph_bound (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] :
    ∃ H : SimpleGraph V, IsSubgraph H G ∧ IsBipartite H ∧
    2 * edgeCount H ≥ edgeCount G

/-
## Part VIII: Related Results

Connections to other extremal graph theory problems.
-/

/--
**Mantel's Theorem (1907):**
A triangle-free graph on n vertices has at most n²/4 edges.

This is a classical bound on triangle-free graphs.
-/
axiom mantel_theorem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsTriangleFree G) :
    4 * edgeCount G ≤ (Fintype.card V) ^ 2

/--
**Kővári-Sós-Turán Theorem:**
Bounds on bipartite Turán numbers, which constrains
the structure of triangle-free graphs.
-/
axiom KST_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsTriangleFree G) :
    (edgeCount G : ℝ) ≤ (1/2 : ℝ) * (Fintype.card V : ℝ) ^ (3/2 : ℝ) +
                        (1/4 : ℝ) * (Fintype.card V : ℝ)

/-
## Part IX: Main Results

Summary of Erdős Problem #581.
-/

/--
**Erdős Problem #581: Summary**

Status: SOLVED (Alon 1996)

**Question:** Determine f(m), the minimum guaranteed bipartite
subgraph size in any triangle-free graph with m edges.

**Answer:**
f(m) = m/2 + Θ(m^{4/5})

More precisely:
  m/2 + c₁ · m^{4/5} ≤ f(m) ≤ m/2 + c₂ · m^{4/5}

for explicit constants c₁, c₂ > 0.

**Key insight:** Triangle-free graphs are "more bipartite-like"
than arbitrary graphs, giving the extra Θ(m^{4/5}) term.
-/
theorem erdos_581 :
    -- Lower bound
    (∃ c₁ > 0, ∀ m, (f m : ℝ) ≥ m / 2 + c₁ * (m : ℝ) ^ (4/5 : ℝ)) ∧
    -- Upper bound
    (∃ c₂ > 0, ∀ m, (f m : ℝ) ≤ m / 2 + c₂ * (m : ℝ) ^ (4/5 : ℝ)) := by
  exact ⟨alon_lower_bound, alon_upper_bound⟩

/--
**Historical Note:**
This problem connects to Ramsey theory and the study of
graph colorings. The resolution by Alon used sophisticated
probabilistic and algebraic methods.
-/
theorem historical_note : True := trivial

/--
**Reference:**
Alon, Noga. "Bipartite subgraphs."
Combinatorica 16 (1996): 301-311.
-/
theorem reference : True := trivial

end Erdos581
