/-
Erdős Problem #814: Dense Graphs Contain Smaller Min-Degree-k Subgraphs

Source: https://erdosproblems.com/814
Status: SOLVED (Sauermann, 2019)

Statement:
Let k ≥ 2 and G be a graph with n ≥ k-1 vertices and
  (k-1)(n-k+2) + C(k-2, 2) + 1
edges. Does there exist some cₖ > 0 such that G must contain an induced
subgraph on at most (1-cₖ)n vertices with minimum degree at least k?

Answer: YES

This is a conjecture of Erdős, Faudree, Rousseau, and Schelp from 1990.

Historical Progress:
- Erdős and Hajnal [Er91]: Studied the case k=3
- Erdős, Faudree, Rousseau, Schelp (1990): Proved subgraph exists with ≤ n - cₖ√n vertices
- Mousset, Noever, Skorić (2017): Improved to n - cₖ·n/log(n) vertices
- Sauermann (2019): Proved the full conjecture with cₖ ≫ 1/k³

Key Insight:
The edge threshold (k-1)(n-k+2) + C(k-2,2) + 1 is significant because graphs
with exactly (k-1)(n-k+2) + C(k-2,2) edges can be constructed to avoid
minimum-degree-k subgraphs on fewer than (1-ε)n vertices.

References:
- Erdős, P. and Faudree, R.J. and Rousseau, C.C. and Schelp, R.H.,
  "Subgraphs of minimal degree k", Discrete Math. (1990), 53-58
- Sauermann, Lisa, "A proof of a conjecture of Erdős, Faudree, Rousseau and
  Schelp on subgraphs of minimum degree k", J. Combin. Theory Ser. B (2019), 36-75
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators SimpleGraph

namespace Erdos814

/-
## Part I: Basic Definitions

Graph-theoretic concepts for minimum degree subgraphs.
-/

/--
**Edge Count Threshold:**
The critical number of edges (k-1)(n-k+2) + C(k-2,2) + 1.
Graphs with at least this many edges must contain the desired subgraph.
-/
def edgeThreshold (k n : ℕ) : ℕ :=
  (k - 1) * (n - k + 2) + Nat.choose (k - 2) 2 + 1

/--
**Minimum Degree of a Graph:**
The minimum degree over all vertices.
-/
def minDegree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' (by simp) (fun v => G.degree v)

/--
**Subgraph Size Fraction:**
The fraction (1 - cₖ) representing the maximum size of the subgraph.
For Sauermann's result, cₖ ≫ 1/k³.
-/
def subgraphFraction (k : ℕ) (c : ℚ) : ℚ := 1 - c

/--
**Sauermann's Constant:**
The constant cₖ from Sauermann's proof, satisfying cₖ ≫ 1/k³.
-/
axiom sauermann_constant (k : ℕ) (hk : k ≥ 2) :
  ∃ c : ℚ, c > 0 ∧ c * (k : ℚ)^3 ≥ 1

/-
## Part II: The EFRS Conjecture and Prior Bounds

Historical progression of results.
-/

/--
**Original EFRS Bound (1990):**
Erdős, Faudree, Rousseau, and Schelp proved that a subgraph exists
with at most n - cₖ√n vertices.

This was the first quantitative result.
-/
axiom efrs_original_bound (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k - 1)
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = n)
    (hedges : G.edgeFinset.card ≥ edgeThreshold k n) :
    ∃ (c : ℚ) (S : Finset V),
      c > 0 ∧
      (S.card : ℚ) ≤ n - c * (n : ℚ).sqrt ∧
      S.card ≥ k ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ k

/--
**Mousset-Noever-Skorić Improvement (2017):**
Improved the bound to n - cₖ·n/log(n) vertices.

This was a significant improvement over the √n bound.
-/
axiom mns_bound (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k - 1)
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = n)
    (hedges : G.edgeFinset.card ≥ edgeThreshold k n) :
    ∃ (c : ℚ) (S : Finset V),
      c > 0 ∧
      (S.card : ℚ) ≤ n - c * (n : ℚ) / (n : ℚ).log ∧
      S.card ≥ k ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ k

/-
## Part III: Sauermann's Theorem

The full solution to the conjecture.
-/

/--
**Sauermann's Theorem (2019):**
Let k ≥ 2 and G be a graph on n ≥ k-1 vertices with at least
  (k-1)(n-k+2) + C(k-2,2) + 1
edges. Then G contains an induced subgraph on at most (1-cₖ)n vertices
with minimum degree at least k, where cₖ ≫ 1/k³.

This fully resolves the EFRS conjecture.
-/
axiom sauermann_theorem (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k - 1)
    (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = n)
    (hedges : G.edgeFinset.card ≥ edgeThreshold k n) :
    ∃ (c : ℚ) (S : Finset V),
      c > 0 ∧
      c * (k : ℚ)^3 ≥ 1 ∧
      (S.card : ℚ) ≤ (1 - c) * n ∧
      S.card ≥ k ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ k

/--
**Erdős Problem #814: SOLVED**
The main theorem restated in the form of the original question.
-/
theorem erdos_814 (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℚ, c > 0 ∧
    ∀ n : ℕ, n ≥ k - 1 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    G.edgeFinset.card ≥ edgeThreshold k n →
    ∃ S : Finset V,
      (S.card : ℚ) ≤ (1 - c) * n ∧
      S.card ≥ k ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ k := by
  obtain ⟨c, hc_pos, hc_bound⟩ := sauermann_constant k hk
  use c
  constructor
  · exact hc_pos
  · intro n hn V _ _ G _ hcard hedges
    obtain ⟨c', S, _, _, hsize, hcard_ge, hdeg⟩ := sauermann_theorem k n hk hn V G hcard hedges
    exact ⟨S, hsize, hcard_ge, hdeg⟩

/-
## Part IV: Edge Threshold Analysis

Understanding the critical edge count.
-/

/--
The edge threshold for k=3.
-/
theorem edgeThreshold_three (n : ℕ) (hn : n ≥ 2) :
    edgeThreshold 3 n = 2 * (n - 1) + 1 := by
  simp only [edgeThreshold, Nat.choose]
  ring_nf
  omega

/--
The edge threshold for k=2.
-/
theorem edgeThreshold_two (n : ℕ) (hn : n ≥ 1) :
    edgeThreshold 2 n = n + 1 := by
  simp only [edgeThreshold, Nat.choose]
  omega

/--
**Extremal Graph:**
The EFRS paper constructs graphs with exactly the threshold minus one edges
that avoid minimum-degree-k subgraphs on (1-ε)n vertices.

This shows the bound is tight.
-/
axiom extremal_construction (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    G.edgeFinset.card = edgeThreshold k n - 1 ∧
    ∀ S : Finset V, (S.card : ℚ) ≤ (1 - 1/(2 * k : ℚ)) * n →
      ∃ v ∈ S, (G.neighborFinset v ∩ S).card < k

/-
## Part V: The k=3 Case (Erdős-Hajnal)

The original case studied.
-/

/--
**Erdős-Hajnal k=3 Case:**
The case k=3 was originally posed by Erdős and Hajnal.
This asks: does every graph with 2n-1 edges contain a small subgraph
with minimum degree 3?
-/
theorem erdos_hajnal_case :
    ∃ c : ℚ, c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    G.edgeFinset.card ≥ 2 * (n - 1) + 1 →
    ∃ S : Finset V,
      (S.card : ℚ) ≤ (1 - c) * n ∧
      S.card ≥ 3 ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ 3 := by
  have h : (3 : ℕ) ≥ 2 := by omega
  obtain ⟨c, hc_pos, hc_main⟩ := erdos_814 3 h
  use c
  constructor
  · exact hc_pos
  · intro n hn V _ _ G _ hcard hedges
    have hn' : n ≥ 3 - 1 := by omega
    have hedges' : G.edgeFinset.card ≥ edgeThreshold 3 n := by
      rw [edgeThreshold_three n (by omega)]
      omega
    exact hc_main n hn' V G hcard hedges'

/-
## Part VI: Degree Bounds and Density

Auxiliary results on degree sums.
-/

/--
**Handshaking Lemma:**
The sum of degrees equals twice the number of edges.
-/
axiom handshaking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, G.degree v = 2 * G.edgeFinset.card

/--
**High Degree Vertices Exist:**
In a dense graph, some vertices have high degree.
-/
theorem high_degree_exists {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V = n) (hn : n > 0)
    (k : ℕ) (hedges : G.edgeFinset.card ≥ k * n / 2) :
    ∃ v : V, G.degree v ≥ k := by
  by_contra h
  push_neg at h
  have hsum : ∑ v : V, G.degree v < k * n := by
    calc ∑ v : V, G.degree v
        = ∑ v : V, G.degree v := rfl
      _ < ∑ _ : V, k := Finset.sum_lt_sum (fun v _ => Nat.le_of_lt (h v)) ⟨Classical.arbitrary V, Finset.mem_univ _, h _⟩
      _ = k * Fintype.card V := by simp [Finset.sum_const, Finset.card_univ]
      _ = k * n := by rw [hcard]
  have hhand := handshaking G
  omega

/-
## Part VII: The Main Result Summary
-/

/--
**Erdős Problem #814: Summary**

The conjecture of Erdős, Faudree, Rousseau, and Schelp is true:

For each k ≥ 2, there exists cₖ > 0 such that any graph G on n vertices
with at least (k-1)(n-k+2) + C(k-2,2) + 1 edges contains an induced
subgraph on at most (1-cₖ)n vertices with minimum degree at least k.

The constant satisfies cₖ ≫ 1/k³.
-/
theorem erdos_814_summary :
    ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℚ, c > 0 ∧ c * (k : ℚ)^3 ≥ 1 ∧
    ∀ n : ℕ, n ≥ k - 1 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    G.edgeFinset.card ≥ edgeThreshold k n →
    ∃ S : Finset V,
      (S.card : ℚ) ≤ (1 - c) * n ∧
      S.card ≥ k ∧
      ∀ v ∈ S, (G.neighborFinset v ∩ S).card ≥ k := by
  intro k hk
  obtain ⟨c, hc_pos, hc_bound⟩ := sauermann_constant k hk
  use c
  refine ⟨hc_pos, hc_bound, ?_⟩
  intro n hn V _ _ G _ hcard hedges
  obtain ⟨c', S, _, _, hsize, hcard_ge, hdeg⟩ := sauermann_theorem k n hk hn V G hcard hedges
  exact ⟨S, hsize, hcard_ge, hdeg⟩

/--
**Answer to Erdős #814:**
YES, such a constant cₖ exists for all k ≥ 2.
-/
theorem erdos_814_answer : ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℚ, c > 0 := fun k hk =>
  let ⟨c, hc_pos, _⟩ := erdos_814 k hk
  ⟨c, hc_pos⟩

end Erdos814
