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
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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
def minDegree {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun v => G.degree v)

/--
**Subgraph Size Fraction:**
The fraction (1 - cₖ) representing the maximum size of the subgraph.
For Sauermann's result, cₖ ≫ 1/k³.
-/
def subgraphFraction (k : ℕ) (c : ℚ) : ℚ := 1 - c

/-
## Part II: The EFRS Conjecture and Prior Bounds

Historical progression of results.
-/

/- 
**Original EFRS Bound (1990):**
Erdős, Faudree, Rousseau, and Schelp proved that a subgraph exists
with at most n - cₖ√n vertices.

This was the first quantitative result.
-/
/- 
**Mousset-Noever-Skorić Improvement (2017):**
Improved the bound to n - cₖ·n/log(n) vertices.

This was a significant improvement over the √n bound.
-/
/-
## Part III: Sauermann's Theorem

The full solution to the conjecture.
-/

/--
**Sauermann's Theorem (2019):**
Let k ≥ 2. There is a single constant cₖ > 0 with cₖ ≫ 1/k³ such that for every
n ≥ k-1 and every graph G on n vertices with at least
  (k-1)(n-k+2) + C(k-2,2) + 1
edges, G contains an induced subgraph on at most (1-cₖ)n vertices
with minimum degree at least k.

This fully resolves the EFRS conjecture. Note the constant cₖ depends only on
k, not on n or G — this is essential for `erdos_814` below, which asserts a
single c working uniformly across all valid n.
-/
axiom sauermann_theorem (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℚ, c > 0 ∧ c * (k : ℚ)^3 ≥ 1 ∧
    ∀ (n : ℕ), n ≥ k - 1 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    G.edgeFinset.card ≥ edgeThreshold k n →
    ∃ (S : Finset V),
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
  obtain ⟨c, hc_pos, _, h⟩ := sauermann_theorem k hk
  exact ⟨c, hc_pos, h⟩

/-
## Part IV: Edge Threshold Analysis

Understanding the critical edge count.
-/

/--
The edge threshold for k=3.
-/
-- Note: `n ≥ 3` (not merely `n ≥ 2`) is required. At the boundary `n = 2`
-- (`n < k`), the truncated `Nat` subtraction `n - k + 2` in `edgeThreshold`
-- overestimates the true value, so the closed form below is genuinely false
-- at `n = 2` (`edgeThreshold 3 2 = 5 ≠ 2 * (2 - 1) + 1 = 3`).
theorem edgeThreshold_three (n : ℕ) (hn : n ≥ 3) :
    edgeThreshold 3 n = 2 * (n - 1) + 1 := by
  have : Nat.choose (3 - 2) 2 = 0 := by decide
  simp only [edgeThreshold, this]
  omega

/--
The edge threshold for k=2.
-/
-- Same boundary issue as `edgeThreshold_three`: `n ≥ 2` (not `n ≥ 1`) is
-- required, since at `n = 1` (`n < k`) the closed form is false
-- (`edgeThreshold 2 1 = 3 ≠ 1 + 1 = 2`).
theorem edgeThreshold_two (n : ℕ) (hn : n ≥ 2) :
    edgeThreshold 2 n = n + 1 := by
  have : Nat.choose (2 - 2) 2 = 0 := by decide
  simp only [edgeThreshold, this]
  omega

/- 
**Extremal Graph:**
The EFRS paper constructs graphs with exactly the threshold minus one edges
that avoid minimum-degree-k subgraphs on (1-ε)n vertices.

This shows the bound is tight.
-/
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
    rcases Nat.lt_or_ge n 3 with hlt | hn3
    · -- 2 ≤ n < 3, so n = 2: the edge-count hypothesis is unsatisfiable
      -- (a 2-vertex simple graph has at most 1 edge, but `hedges` demands ≥ 3).
      have hn2 : n = 2 := by omega
      exfalso
      have hmax : G.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two
      rw [hcard, hn2] at hmax
      have hchoose : Nat.choose 2 2 = 1 := by decide
      rw [hchoose] at hmax
      omega
    · -- n ≥ 3: translate via the closed form for edgeThreshold 3 n
      have hn' : n ≥ 3 - 1 := by omega
      have hedges' : G.edgeFinset.card ≥ edgeThreshold 3 n := by
        rw [edgeThreshold_three n hn3]
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

Note: the hypothesis is stated as `2 * G.edgeFinset.card ≥ k * n` (i.e. the sum of
degrees is at least `k * n`) rather than `G.edgeFinset.card ≥ k * n / 2` (nat floor
division). The floor-division form is genuinely false at the boundary — e.g.
`n = k = 1` gives `k * n / 2 = 0 ≤ G.edgeFinset.card` vacuously while the single
vertex has degree `0 < k`. The `2 * card ≥ k * n` form is the correct,
division-free statement of the averaging/pigeonhole argument.
-/
theorem high_degree_exists {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V = n) (hn : n > 0)
    (k : ℕ) (hedges : 2 * G.edgeFinset.card ≥ k * n) :
    ∃ v : V, G.degree v ≥ k := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; exact hn)
  by_contra h
  push_neg at h
  have hsum : ∑ v : V, G.degree v < k * n := by
    calc ∑ v : V, G.degree v
        < ∑ _ : V, k := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => h v)
      _ = k * Fintype.card V := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
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
  obtain ⟨c, hc_pos, hc_bound, h⟩ := sauermann_theorem k hk
  exact ⟨c, hc_pos, hc_bound, h⟩

/--
**Answer to Erdős #814:**
YES, such a constant cₖ exists for all k ≥ 2.
-/
theorem erdos_814_answer : ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℚ, c > 0 := by
  intro k hk
  have h := erdos_814.{0} k hk
  exact ⟨h.choose, h.choose_spec.1⟩

end Erdos814
