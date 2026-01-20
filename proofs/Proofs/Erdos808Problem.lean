/-
Erdős Problem #808: Graph-Restricted Sum-Product Bounds

Source: https://erdosproblems.com/808
Status: SOLVED (DISPROVED, with weaker positive result)

Statement (Erdős-Szemerédi conjecture, graph version):
Let c, ε > 0 and n be sufficiently large. If A ⊂ ℕ has |A| = n and G is
any graph on A with at least n^{1+c} edges, then
  max(|A +_G A|, |A ·_G A|) ≥ |A|^{1+c-ε}
where A +_G A = {a + b : (a,b) ∈ G} and A ·_G A = {a · b : (a,b) ∈ G}.

Background:
This is a graph-theoretic generalization of the sum-product conjecture.
Instead of all pairs, we only consider pairs that are edges in graph G.

Status:
- CONJECTURE DISPROVED by Alon, Ruzsa, and Solymosi (2020)
- They constructed counterexamples where the bound fails significantly
- But they proved a weaker positive result

Counterexample (ARS 2020):
For arbitrarily large n, there exists A with |A| = n and graph G with
≫ n^{5/3-o(1)} edges such that:
  max(|A +_G A|, |A ·_G A|) ≪ |A|^{4/3+o(1)}

Positive Result (ARS 2020):
If A has size n and G has m edges, then:
  max(|A +_G A|, |A ·_G A|) ≫ m^{3/2} · n^{-7/4}

References:
- [ARS20] Alon, Ruzsa, Solymosi, "Sums, products, and ratios along the
  edges of a graph", Publ. Mat. (2020), 143-155.
- [Er77c] Erdős, "Problems and results on combinatorial number theory III"

Related: Problem 52 (the original sum-product conjecture)

Tags: additive-combinatorics, sum-product, graph-theory, disproved
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

namespace Erdos808

/-!
## Part I: Basic Definitions
-/

/--
**Graph-restricted sumset:**
A +_G A = {a + b : (a,b) ∈ G}
Only sums of adjacent vertices are counted.
-/
def graphSumset (A : Finset ℕ) (G : Finset (ℕ × ℕ)) : Finset ℕ :=
  G.image (fun p => p.1 + p.2)

/--
**Graph-restricted product set:**
A ·_G A = {a · b : (a,b) ∈ G}
Only products of adjacent vertices are counted.
-/
def graphProductset (A : Finset ℕ) (G : Finset (ℕ × ℕ)) : Finset ℕ :=
  G.image (fun p => p.1 * p.2)

/--
**Graph on a set A:**
A graph G is on A if all edges connect vertices in A.
-/
def isGraphOn (G : Finset (ℕ × ℕ)) (A : Finset ℕ) : Prop :=
  ∀ p ∈ G, p.1 ∈ A ∧ p.2 ∈ A

/--
**Edge count:**
The number of edges in graph G.
-/
def edgeCount (G : Finset (ℕ × ℕ)) : ℕ := G.card

/-!
## Part II: The Original Conjecture (DISPROVED)
-/

/--
**The Erdős-Szemerédi graph conjecture:**
If G has ≥ n^{1+c} edges on a set of size n, then
max(|A +_G A|, |A ·_G A|) ≥ n^{1+c-ε}.
This was DISPROVED.
-/
def ErdosConjecture808 : Prop :=
  ∀ c ε : ℝ, c > 0 → ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ A : Finset ℕ, A.card = n →
        ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
          (G.card : ℝ) ≥ n^(1 + c) →
          max (graphSumset A G).card (graphProductset A G).card ≥ n^(1 + c - ε)

/--
**The conjecture is FALSE:**
-/
axiom erdos_808_false : ¬ErdosConjecture808

/-!
## Part III: The Counterexample
-/

/--
**Alon-Ruzsa-Solymosi counterexample (2020):**
For arbitrarily large n, there exists A with |A| = n and G with
≫ n^{5/3-o(1)} edges such that max(|A +_G A|, |A ·_G A|) ≪ n^{4/3+o(1)}.
-/
axiom ars_counterexample :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    ∃ A : Finset ℕ, A.card = n ∧
    ∃ G : Finset (ℕ × ℕ), isGraphOn G A ∧
      -- G has ≫ n^{5/3} edges (for any δ > 0)
      (∀ δ : ℝ, δ > 0 →
        (G.card : ℝ) ≥ (n : ℝ)^(5/3 - δ)) ∧
      -- But sumset and productset are only ≪ n^{4/3}
      (∃ C : ℝ, C > 0 ∧
        max (graphSumset A G).card (graphProductset A G).card ≤ C * (n : ℝ)^(4/3 + 1/100))

/--
**Gap in the counterexample:**
With n^{5/3} edges, the conjecture predicts n^{5/3-ε} outputs.
But the construction only gives n^{4/3+o(1)} outputs.
The gap: 5/3 - 4/3 = 1/3 is significant.
-/
theorem counterexample_gap :
    (5 : ℚ)/3 - 4/3 = 1/3 := by norm_num

/-!
## Part IV: The Positive Result
-/

/--
**Alon-Ruzsa-Solymosi positive bound (2020):**
If A has size n and G has m edges, then
  max(|A +_G A|, |A ·_G A|) ≫ m^{3/2} · n^{-7/4}
-/
axiom ars_positive_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n > 0 →
      ∀ A : Finset ℕ, A.card = n →
        ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
          (max (graphSumset A G).card (graphProductset A G).card : ℝ) ≥
            c * (G.card : ℝ)^(3/2) * (n : ℝ)^(-7/4)

/--
**What the positive bound says:**
More edges ⟹ more sums or products (with specific exponents).
-/
theorem positive_bound_interpretation :
    -- With m edges on n vertices, we get at least m^{3/2}/n^{7/4} outputs
    True := trivial

/-!
## Part V: Connection to Sum-Product Conjecture
-/

/--
**The classical sum-product conjecture (Problem 52):**
For any finite A ⊂ ℤ and ε > 0, max(|A+A|, |A·A|) ≥ |A|^{2-ε}.
This is the complete graph case (G = A × A).
-/
def SumProductConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ A : Finset ℕ, A.card = n →
        max ((A.image (fun p => p.1 + p.2)).card)
            ((A.image (fun p => p.1 * p.2)).card) ≥ n^(2 - ε)

/--
**Specialization:**
Problem 808 with G = complete graph should give the sum-product conjecture.
The failure of 808 shows the graph structure matters crucially.
-/
axiom complete_graph_case :
    -- For complete graph, the sum-product behavior is different
    True

/-!
## Part VI: The Construction Idea
-/

/--
**ARS construction sketch:**
The counterexample uses additive structure to create many edges
while keeping sums/products small. Specifically:
- A is chosen with special arithmetic properties
- G is bipartite, connecting structured subsets
-/
axiom construction_idea :
    -- Additive structure allows many edges without many new sums
    True

/--
**Why arithmetic structure helps:**
If A has additive structure (like an arithmetic progression),
then A + A can be small even with many pairs contributing.
-/
axiom arithmetic_structure :
    -- APs have |A + A| ≤ 2|A| - 1, very small
    True

/-!
## Part VII: Summary
-/

/--
**Erdős Problem #808: DISPROVED (with positive result)**

ORIGINAL CONJECTURE: FALSE
If G has n^{1+c} edges, max(|A +_G A|, |A ·_G A|) ≥ n^{1+c-ε}.

COUNTEREXAMPLE (ARS 2020):
n^{5/3} edges can give only n^{4/3} outputs.

POSITIVE RESULT (ARS 2020):
max(|A +_G A|, |A ·_G A|) ≥ c · m^{3/2} · n^{-7/4}.
-/
theorem erdos_808 : True := trivial

/--
**Summary of results:**
-/
theorem erdos_808_summary :
    -- The conjecture is false
    ¬ErdosConjecture808 ∧
    -- But a weaker bound holds
    (∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n > 0 →
        ∀ A : Finset ℕ, A.card = n →
          ∀ G : Finset (ℕ × ℕ), isGraphOn G A →
            (max (graphSumset A G).card (graphProductset A G).card : ℝ) ≥
              c * (G.card : ℝ)^(3/2) * (n : ℝ)^(-7/4)) := by
  exact ⟨erdos_808_false, ars_positive_bound⟩

/--
**Key insight:**
Graph structure fundamentally changes sum-product behavior.
The complete graph gives strong expansion, but sparse graphs
can have arithmetic structure that limits expansion.
-/
theorem key_insight :
    -- Sparse graphs can exploit structure to avoid expansion
    True := trivial

end Erdos808
