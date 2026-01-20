/-
Erdős Problem #150: Minimal Cuts in Graphs

Source: https://erdosproblems.com/150
Status: SOLVED (Bradač, 2024)

Statement:
A minimal cut of a graph is a minimal set of vertices whose removal
disconnects the graph. Let c(n) be the maximum number of minimal cuts
a graph on n vertices can have.

Does c(n)^{1/n} → α for some α < 2?

Answer: YES

Bradač (2024) proved:
1. The limit α = lim c(n)^{1/n} exists
2. α ≤ 2^{H(1/3)} = 1.8899..., where H is the binary entropy function
3. Seymour's construction shows α ≥ 3^{1/3} = 1.442...

Bradač conjectures that the lower bound 3^{1/3} is the true value of α.

Historical Context:
- Asked by Erdős and Nešetřil
- Seymour observed c(3m+2) ≥ 3^m via m independent paths of length 4

References:
- [Br24] Bradač, On a question of Erdős and Nešetřil about minimal cuts in a graph.
         arXiv:2409.02974 (2024).
-/

import Mathlib

open Set Real SimpleGraph

namespace Erdos150

/-
## Part I: Graph Definitions

Basic graph theory definitions for minimal cuts.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Vertex Cut:**
A set S of vertices in graph G is a vertex cut if removing S
disconnects G (makes G[V \ S] not connected).
-/
def isVertexCut (G : SimpleGraph V) (S : Set V) : Prop :=
  ¬(G.induce (Sᶜ)).Connected

/--
**Minimal Vertex Cut:**
A vertex cut S is minimal if no proper subset of S is also a cut.
In other words, S is inclusion-minimal among all cuts.
-/
def isMinimalCut (G : SimpleGraph V) (S : Set V) : Prop :=
  isVertexCut G S ∧ ∀ T : Set V, T ⊂ S → ¬isVertexCut G T

/--
**The set of all minimal cuts of a graph.**
-/
def minimalCuts (G : SimpleGraph V) : Set (Set V) :=
  {S : Set V | isMinimalCut G S}

/-
## Part II: The Maximum Minimal Cuts Function

c(n) = maximum number of minimal cuts over all graphs on n vertices.
-/

/--
**c(n):** Maximum number of minimal cuts a graph on n vertices can have.

This is the central function of Erdős Problem #150.
-/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  if h : n ≥ 1 then
    sSup {k : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
      Fintype.card V = n ∧ ∃ G : SimpleGraph V, (minimalCuts G).ncard = k}
  else 0

/--
For convenience, we use c(n) notation.
-/
notation "c(" n ")" => maxMinimalCuts n

/-
## Part III: Seymour's Construction

Seymour observed that c(3m+2) ≥ 3^m using m independent paths of length 4.

The construction: Take two vertices u and v, and connect them
by m independent paths, each of length 4 (so each path has 3 internal vertices).
-/

/--
**Seymour's Lower Bound:**
c(3m+2) ≥ 3^m

The graph consists of m disjoint paths of length 4 between two vertices u and v.
Each path has 3 internal vertices. To disconnect u from v, we must
remove at least one vertex from each path, giving 3^m minimal cuts.
-/
axiom seymour_construction (m : ℕ) : c(3*m + 2) ≥ 3^m

/--
**Corollary:** α ≥ 3^{1/3} ≈ 1.442

Taking the mth root of c(3m+2) ≥ 3^m and letting m → ∞.
-/
axiom seymour_lower_bound :
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (c(n) : ℝ) ^ (1 / n : ℝ) ≥ 3 ^ (1/3 : ℝ) - ε

/-
## Part IV: Binary Entropy Function

H(p) = -p log₂ p - (1-p) log₂ (1-p)
-/

/--
**Binary Entropy Function:**
H(p) = -p log₂(p) - (1-p) log₂(1-p) for p ∈ (0,1).
-/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 then
    -(p * Real.log p / Real.log 2 + (1 - p) * Real.log (1 - p) / Real.log 2)
  else 0

/--
H(1/3) ≈ 0.9183
-/
axiom binaryEntropy_one_third : binaryEntropy (1/3) = Real.log 3 / Real.log 2 - 2/3

/--
2^{H(1/3)} ≈ 1.8899
-/
axiom two_pow_entropy_one_third :
  (2 : ℝ) ^ binaryEntropy (1/3) = 3 / (2 : ℝ) ^ (2/3 : ℝ)

/-
## Part V: Bradač's Theorem

The main result: the limit exists and α < 2.
-/

/--
**The Limit Exists:**
lim_{n→∞} c(n)^{1/n} exists.

This is the first part of Bradač's theorem.
-/
axiom limit_exists :
  ∃ α : ℝ, Filter.Tendsto
    (fun n : ℕ => (c(n) : ℝ) ^ (1 / n : ℝ))
    Filter.atTop
    (nhds α)

/--
**The Limit Value α:**
The value to which c(n)^{1/n} converges.
-/
noncomputable def α : ℝ := limit_exists.choose

/--
**Bradač's Upper Bound:**
α ≤ 2^{H(1/3)} = 1.8899...

This is the key result showing α < 2.
-/
axiom bradac_upper_bound : α ≤ (2 : ℝ) ^ binaryEntropy (1/3)

/--
**Binary entropy H(1/3) < 1:**
Since H(p) ≤ 1 for all p ∈ (0,1) with equality only at p = 1/2.
H(1/3) = log₂(3) - 2/3 ≈ 0.9183 < 1.
-/
axiom binaryEntropy_one_third_lt_one : binaryEntropy (1/3) < 1

/--
**Main Result: α < 2**
The answer to Erdős's question is YES.
-/
theorem alpha_less_than_two : α < 2 := by
  have h1 : α ≤ (2 : ℝ) ^ binaryEntropy (1/3) := bradac_upper_bound
  have h2 : (2 : ℝ) ^ binaryEntropy (1/3) < 2 := by
    -- Since H(1/3) < 1, we have 2^{H(1/3)} < 2^1 = 2
    have hH : binaryEntropy (1/3) < 1 := binaryEntropy_one_third_lt_one
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have h2_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h2_gt_one : (1 : ℝ) < 2 := by norm_num
    calc (2 : ℝ) ^ binaryEntropy (1/3) < (2 : ℝ) ^ (1 : ℝ) := by
           exact Real.rpow_lt_rpow_of_exponent_lt h2_gt_one hH
      _ = 2 := Real.rpow_one 2
  exact lt_of_le_of_lt h1 h2

/-
## Part VI: The Main Theorem

Erdős Problem #150: SOLVED
-/

/--
**Erdős Problem #150: SOLVED**

The limit c(n)^{1/n} → α exists with α < 2.

Specifically:
- α exists (Bradač, 2024)
- 3^{1/3} ≤ α ≤ 2^{H(1/3)} (bounds)
- α ≈ 1.442 to 1.890

Bradač conjectures α = 3^{1/3}.
-/
theorem erdos_150 :
  ∃ α : ℝ, α < 2 ∧
    Filter.Tendsto (fun n : ℕ => (c(n) : ℝ) ^ (1 / n : ℝ)) Filter.atTop (nhds α) :=
  ⟨α, alpha_less_than_two, limit_exists.choose_spec⟩

/-
## Part VII: Bounds Summary

The known bounds on α.
-/

/--
**Lower Bound:** α ≥ 3^{1/3} ≈ 1.442...

From Seymour's construction.
-/
axiom alpha_lower_bound : α ≥ 3 ^ (1/3 : ℝ)

/--
**Upper Bound:** α ≤ 2^{H(1/3)} ≈ 1.890...

From Bradač's proof.
-/
theorem alpha_upper_bound : α ≤ 2 ^ binaryEntropy (1/3) := bradac_upper_bound

/--
**Complete Bounds:**
3^{1/3} ≤ α ≤ 2^{H(1/3)}
-/
theorem alpha_bounds : 3 ^ (1/3 : ℝ) ≤ α ∧ α ≤ 2 ^ binaryEntropy (1/3) :=
  ⟨alpha_lower_bound, alpha_upper_bound⟩

/-
## Part VIII: Bradač's Conjecture

The conjectured true value of α.
-/

/--
**Bradač's Conjecture:**
The true value of α is exactly 3^{1/3}.

This would mean Seymour's construction is optimal.
-/
def bradac_conjecture : Prop := α = 3 ^ (1/3 : ℝ)

/-
## Part IX: Special Values

The function c(n) for small values of n.
-/

/--
c(3m+2) ≥ 3^m: The Seymour lower bound.
-/
theorem c_seymour_bound (m : ℕ) : c(3*m + 2) ≥ 3^m := seymour_construction m

/--
**Example:** c(5) ≥ 3

When m=1: c(3·1+2) = c(5) ≥ 3^1 = 3.
-/
theorem c_5_ge_3 : c(5) ≥ 3 := by
  have h := seymour_construction 1
  simp only [Nat.mul_one, Nat.pow_one] at h
  exact h

/--
**Example:** c(8) ≥ 9

When m=2: c(3·2+2) = c(8) ≥ 3^2 = 9.
-/
theorem c_8_ge_9 : c(8) ≥ 9 := by
  have h := seymour_construction 2
  norm_num at h
  exact h

/--
**Example:** c(11) ≥ 27

When m=3: c(3·3+2) = c(11) ≥ 3^3 = 27.
-/
theorem c_11_ge_27 : c(11) ≥ 27 := by
  have h := seymour_construction 3
  norm_num at h
  exact h

/-
## Part X: Main Results Summary
-/

/--
**Complete Solution to Erdős Problem #150:**

1. The limit α = lim c(n)^{1/n} exists
2. α < 2 (answering Erdős's question affirmatively)
3. 3^{1/3} ≤ α ≤ 2^{H(1/3)} (approximately 1.442 to 1.890)
4. Bradač conjectures α = 3^{1/3}
-/
theorem erdos_150_summary :
  ∃ α : ℝ,
    α < 2 ∧
    3 ^ (1/3 : ℝ) ≤ α ∧
    α ≤ 2 ^ binaryEntropy (1/3) ∧
    Filter.Tendsto (fun n : ℕ => (c(n) : ℝ) ^ (1/n : ℝ)) Filter.atTop (nhds α) :=
  ⟨α, alpha_less_than_two, alpha_lower_bound, alpha_upper_bound, limit_exists.choose_spec⟩

/--
**Answer to Erdős's Question:**
YES, c(n)^{1/n} converges to some α < 2.
-/
theorem erdos_150_answer : ∃ α : ℝ, α < 2 ∧
    Filter.Tendsto (fun n : ℕ => (c(n) : ℝ) ^ (1/n : ℝ)) Filter.atTop (nhds α) :=
  erdos_150

end Erdos150
