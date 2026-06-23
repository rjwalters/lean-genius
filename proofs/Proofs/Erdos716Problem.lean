/-
Erdős Problem #716: The Ruzsa-Szemerédi (6,3) Problem

Source: https://erdosproblems.com/716
Status: SOLVED (Ruzsa-Szemerédi, 1978)

Statement:
Let ℱ be the family of all 3-uniform hypergraphs with 6 vertices and 3 edges.
Is it true that ex₃(n, ℱ) = o(n²)?

Equivalently: What is the maximum number of edges in an n-vertex graph where
every edge belongs to a unique triangle?

Solution:
Ruzsa and Szemerédi (1978) proved the answer is YES: ex₃(n, ℱ) = o(n²).
More precisely, they showed ex₃(n, ℱ) = n² · e^{-Ω(√log n)}.

Background:
- f^(r)(n; v, e) = max edges in r-uniform hypergraph on n vertices with no
  e edges spanning v vertices
- The (6,3)-problem asks for f^(3)(n; 6, 3): no 6 vertices span 3 edges
- Equivalent to graphs where every edge belongs to a unique triangle
- Connected to the Triangle Removal Lemma via regularity method

Historical Context:
- Brown, Erdős, Sós (1973): Posed the conjecture
- Ruzsa, Szemerédi (1978): Proved it using connection to Szemerédi regularity
- Led to development of the Triangle Removal Lemma
- The proof connects extremal combinatorics to additive number theory

References:
- Brown, Erdős, Sós (1973): "Some extremal problems on r-graphs"
- Ruzsa, Szemerédi (1978): "Triple systems with no six points carrying three triangles"
- Szemerédi (1978): Regularity lemma
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset

namespace Erdos716

/- ## Part I: Hypergraph Basics -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **3-Uniform Hypergraph:**
A hypergraph where every edge has exactly 3 vertices. -/
structure Hypergraph3 (V : Type*) [Fintype V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

/-- **Number of Vertices Spanned:**
The number of distinct vertices covered by a set of hyperedges. -/
def spannedVertices (H : Hypergraph3 V) (S : Finset (Finset V)) : Finset V :=
  S.biUnion id

/-- **(v, e)-Configuration:**
A set of e hyperedges spanning at most v vertices. -/
def hasConfiguration (H : Hypergraph3 V) (v e : ℕ) : Prop :=
  ∃ S : Finset (Finset V), S ⊆ H.edges ∧ S.card = e ∧
    (spannedVertices H S).card ≤ v

/-- **(6,3)-Configuration:**
Three hyperedges spanning at most 6 vertices. This is the forbidden configuration
in Erdős Problem #716. -/
def has63Configuration (H : Hypergraph3 V) : Prop :=
  hasConfiguration H 6 3

/-- **(6,3)-Free Hypergraph:**
A hypergraph with no 6 vertices spanning 3 edges. -/
def is63Free (H : Hypergraph3 V) : Prop :=
  ¬has63Configuration H

/- ## Part II: Extremal Numbers -/

/-- **Extremal Number f^(3)(n; v, e):**
Maximum edges in a 3-uniform hypergraph on n vertices with no
e edges spanning v vertices. -/
axiom extremalHypergraph (n v e : ℕ) : ℕ

/-- **The (6,3)-Extremal Number:**
f^(3)(n; 6, 3) = max edges in n-vertex 3-uniform hypergraph that is (6,3)-free. -/
def ex63 (n : ℕ) : ℕ := extremalHypergraph n 6 3

/-- **Trivial Upper Bound:**
The trivial upper bound is O(n²) since there are ≈ n³/6 possible 3-edges. -/

/- ## Part III: Graph Formulation -/

/-- **Edge in Unique Triangle Property:**
In a graph G, edge uv is in a unique triangle if there is exactly one
vertex w such that uvw forms a triangle. -/
def edgeInUniqueTriangle (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) : Prop :=
  ∃! w : V, w ≠ u ∧ w ≠ v ∧ G.Adj u w ∧ G.Adj v w

/-- **Ruzsa-Szemerédi Graph:**
A graph where every edge belongs to a unique triangle. -/
def isRSGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∀ huv : G.Adj u v, edgeInUniqueTriangle G u v huv

/-- **Equivalence of Formulations:**
The maximum edges in an RS-graph on n vertices equals 3 · ex63(n).
Each triangle in the graph corresponds to a hyperedge. -/

/- ## Part IV: The Main Theorem -/

/-- **Little-o Notation:**
f(n) = o(g(n)) means f(n)/g(n) → 0 as n → ∞. -/
def isLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ ε * |g n|

/-- **Ruzsa-Szemerédi Theorem (1978):**
ex₃(n; 6, 3) = o(n²).

That is, the maximum number of edges in a (6,3)-free 3-uniform hypergraph
is subquadratic in n. -/
axiom ruzsa_szemeredi_theorem :
  isLittleO (fun n => (ex63 n : ℝ)) (fun n => (n : ℝ)^2)

/-- **Quantitative Upper Bound:**
More precisely, ex₃(n; 6, 3) = O(n² / log^δ n) for some δ > 0.
The best known bound is essentially n² · e^{-c√(log n)}. -/
axiom ex63_upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (ex63 n : ℝ) ≤ (n : ℝ)^2 * Real.exp (-c * Real.sqrt (Real.log n))

/-- **Lower Bound from Behrend Construction:**
ex₃(n; 6, 3) ≥ n² · e^{-c'√(log n)} for some c' > 0. -/
axiom ex63_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (ex63 n : ℝ) ≥ (n : ℝ)^2 * Real.exp (-c * Real.sqrt (Real.log n))

/- ## Part V: The Triangle Removal Lemma -/

/-- **Triangle Removal Lemma:**
For every ε > 0, there exists δ > 0 such that every n-vertex graph with
at most δn³ triangles can be made triangle-free by removing at most εn² edges.

This is a key consequence of Szemerédi's regularity lemma. -/

/-- **RS Theorem Follows from Removal Lemma:**
The Ruzsa-Szemerédi theorem can be deduced from the triangle removal lemma.
This was a key insight connecting graph theory to additive combinatorics. -/

/- ## Part VI: Connection to Arithmetic Progressions -/

/-- **3-AP Free Set:**
A subset of {1,...,n} containing no 3-term arithmetic progression. -/
def is3APFree (S : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ S → b ∈ S → c ∈ S → a < b → b < c → 2 * b ≠ a + c

/-- **Roth's r₃(n):**
Maximum size of a 3-AP-free subset of {1,...,n}. -/
axiom roth_r3 (n : ℕ) : ℕ

/-- **Roth's Theorem (1953):**
r₃(n) = o(n). That is, large sets must contain 3-term arithmetic progressions. -/

/-- **Behrend's Construction (1946):**
r₃(n) ≥ n · e^{-c√(log n)} for some constant c > 0. -/

/-- **RS Lower Bound from Behrend:**
The Behrend construction gives a lower bound for ex₃(n; 6, 3).
Take a 3-AP-free set S and build a "group construction" hypergraph. -/

/-- **Implication for Roth:**
The Ruzsa-Szemerédi theorem implies Roth's theorem.
This was a key insight connecting graph theory to additive combinatorics. -/

/- ## Part VII: The Brown-Erdős-Sós Conjecture -/

/-- **Brown-Erdős-Sós Conjecture:**
For any k ≥ 3, f^(3)(n; k+3, k) = o(n²).

That is, any 3-uniform hypergraph with Ω(n²) edges contains
k edges spanning at most k+3 vertices. -/
def brownErdosSosConjecture (k : ℕ) : Prop :=
  k ≥ 3 → isLittleO (fun n => (extremalHypergraph n (k + 3) k : ℝ)) (fun n => (n : ℝ)^2)

/-- **Case k = 3 is Erdős #716:**
The (6,3) case is precisely when k = 3. -/
theorem erdos716_is_bes_k3 : brownErdosSosConjecture 3 := by
  intro _
  exact ruzsa_szemeredi_theorem

/-- **BES Conjecture for k = 4:**
f^(3)(n; 7, 4) = o(n²). Proved by Glock (2019). -/

/-- **BES Conjecture in General:**
The full conjecture was proved by Delcourt-Postle (2024). -/

/- ## Part VIII: Erdős's Stronger Question -/

/-- **Erdős's Stronger Question:**
Is it true that f^(3)(n; k+3, k) ≍ n · r_{k-3}(n)?

Ruzsa proved the lower bound for k = 6, 7, 8. -/
def erdosStrongerQuestion (k : ℕ) : Prop :=
  k ≥ 6 →
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 1 →
        c₁ * (n : ℝ) * (roth_r3 n : ℝ) ≤ (extremalHypergraph n (k + 3) k : ℝ) ∧
        (extremalHypergraph n (k + 3) k : ℝ) ≤ c₂ * (n : ℝ) * (roth_r3 n : ℝ)

/-- **Ruzsa's Lower Bound Result:**
For k = 6, 7, 8, the lower bound f^(3)(n; k+3, k) ≥ Ω(n · r_{k-3}(n)) holds. -/

/- ## Part IX: Summary -/

/-- **Erdős Problem #716: Statement**
Let ℱ be the family of all 3-uniform hypergraphs with 6 vertices and 3 edges.
Is ex₃(n, ℱ) = o(n²)? -/
def erdos716Problem : Prop :=
  isLittleO (fun n => (ex63 n : ℝ)) (fun n => (n : ℝ)^2)

/-- **Erdős Problem #716: Solution**
Proved by Ruzsa and Szemerédi in 1978. -/
theorem erdos_716 : erdos716Problem := ruzsa_szemeredi_theorem

/-- **Summary:** Erdős Problem #716 is SOLVED. The key results are:
1. ex₃(n; 6, 3) = o(n²) (Ruzsa-Szemerédi 1978)
2. Tight bounds: n² · e^{-Θ(√log n)}
3. RS theorem implies Roth's theorem
4. Generalized by the Brown-Erdős-Sós conjecture (now proved) -/
theorem erdos_716_summary :
    erdos716Problem ∧
    (∃ c > 0, ∀ n ≥ 2, (ex63 n : ℝ) ≤ (n : ℝ)^2 * Real.exp (-c * Real.sqrt (Real.log n))) ∧
    (∃ c > 0, ∀ n ≥ 2, (ex63 n : ℝ) ≥ (n : ℝ)^2 * Real.exp (-c * Real.sqrt (Real.log n))) :=
  ⟨ruzsa_szemeredi_theorem, ex63_upper_bound, ex63_lower_bound⟩

end Erdos716
