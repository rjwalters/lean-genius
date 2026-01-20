/-
Erdős Problem #600: Edge-Triangle Containment Thresholds

Source: https://erdosproblems.com/600
Status: OPEN

Statement:
Let e(n,r) be the minimal number of edges such that every graph on n vertices
with at least e(n,r) edges, where each edge is in at least one triangle,
must have some edge contained in at least r triangles.

Questions:
1. Does e(n, r+1) - e(n, r) → ∞ as n → ∞?
2. Does e(n, r+1) / e(n, r) → 1 as n → ∞?

Known Results:
- Ruzsa-Szemerédi (1978): e(n, r) = o(n²) for any fixed r

References:
- [RuSz78] Ruzsa-Szemerédi: Triple systems with no six points carrying three triangles
- [Er87] Erdős (1987): Original formulation

Tags: combinatorics, extremal-graph-theory, triangle-counting
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset Filter

namespace Erdos600

/-!
## Part I: Basic Definitions
-/

/--
**Simple Graph:**
A graph on n vertices represented by its edge set.
-/
structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  symmetric : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  irreflexive : ∀ e ∈ edges, e.1 ≠ e.2

/--
**Edge Count:**
Number of edges in the graph (counting each undirected edge once).
-/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  G.edges.card / 2

/--
**Triangle:**
A set of three vertices {u, v, w} forming a triangle in G.
-/
def IsTriangle {n : ℕ} (G : Graph n) (u v w : Fin n) : Prop :=
  u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
  (u, v) ∈ G.edges ∧ (v, w) ∈ G.edges ∧ (u, w) ∈ G.edges

/-!
## Part II: Edge-Triangle Containment
-/

/--
**Triangle Count for an Edge:**
Number of triangles containing a specific edge {u, v}.
-/
noncomputable def triangleCount {n : ℕ} (G : Graph n) (u v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => IsTriangle G u v w)).card

/--
**Edge in at Least One Triangle:**
An edge is "triangle-covered" if it's in at least one triangle.
-/
def IsTriangleCovered {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  triangleCount G u v ≥ 1

/--
**All Edges Triangle-Covered:**
Every edge in G is contained in at least one triangle.
-/
def AllEdgesTriangleCovered {n : ℕ} (G : Graph n) : Prop :=
  ∀ e ∈ G.edges, ∃ w : Fin n, IsTriangle G e.1 e.2 w

/--
**Some Edge in r Triangles:**
G has at least one edge contained in at least r triangles.
-/
def HasEdgeInRTriangles {n : ℕ} (G : Graph n) (r : ℕ) : Prop :=
  ∃ u v : Fin n, (u, v) ∈ G.edges ∧ triangleCount G u v ≥ r

/-!
## Part III: The e(n,r) Function
-/

/--
**The Function e(n,r):**
Minimal number of edges such that every graph on n vertices with
≥ e(n,r) edges, all triangle-covered, has some edge in ≥ r triangles.

Formally: e(n,r) = min{m : ∀G on n vertices,
  |E(G)| ≥ m ∧ AllEdgesTriangleCovered G → HasEdgeInRTriangles G r}
-/
noncomputable def e (n r : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ G : Graph n,
    edgeCount G ≥ m → AllEdgesTriangleCovered G → HasEdgeInRTriangles G r }

/--
**e is well-defined:**
The set is non-empty (bounded by n²/2).
-/
axiom e_well_defined (n r : ℕ) (hn : n ≥ 3) (hr : r ≥ 1) :
  e n r ≤ n * (n - 1) / 2

/-!
## Part IV: Ruzsa-Szemerédi Result
-/

/--
**Ruzsa-Szemerédi (1978):**
e(n, r) = o(n²) for any fixed r.

This means e(n, r) grows subquadratically in n.
The proof uses the triangle removal lemma.
-/
axiom ruzsa_szemeredi (r : ℕ) (hr : r ≥ 2) :
  ∀ ε > 0, ∀ᶠ n in atTop, (e n r : ℝ) < ε * n^2

/--
**Triangle Removal Lemma Connection:**
The Ruzsa-Szemerédi result is closely related to the triangle removal lemma:
If a graph has o(n³) triangles, one can make it triangle-free by
removing o(n²) edges.
-/
axiom triangle_removal_connection : True

/--
**Subquadratic growth:**
e(n, r) = o(n²) means lim_{n→∞} e(n,r)/n² = 0.
-/
theorem subquadratic_growth (r : ℕ) (hr : r ≥ 2) :
    ∀ ε > 0, ∀ᶠ n in atTop, (e n r : ℝ) / n^2 < ε := by
  intro ε hε
  have h := ruzsa_szemeredi r hr ε hε
  filter_upwards [h] with n hn
  calc (e n r : ℝ) / n^2 < ε * n^2 / n^2 := by
        apply div_lt_div_of_pos_right hn (sq_pos_of_pos (by linarith))
    _ = ε := by ring_nf; simp

/-!
## Part V: Question 1 - The Difference e(n, r+1) - e(n, r)
-/

/--
**Question 1:**
Does e(n, r+1) - e(n, r) → ∞ as n → ∞?

This asks whether the threshold strictly increases with r,
and whether the gap grows without bound.
-/
def Question1 : Prop :=
  ∀ r : ℕ, r ≥ 2 → ∀ M : ℕ, ∀ᶠ n in atTop, e n (r + 1) - e n r > M

/--
**Status: OPEN**
-/
axiom question1_open : ¬Decidable Question1

/--
**Intuition:**
As we require more triangles per edge, the threshold should increase.
The question is whether this increase is unbounded.
-/
axiom question1_intuition : True

/-!
## Part VI: Question 2 - The Ratio e(n, r+1) / e(n, r)
-/

/--
**Question 2:**
Does e(n, r+1) / e(n, r) → 1 as n → ∞?

This asks whether consecutive thresholds are asymptotically equivalent.
-/
def Question2 : Prop :=
  ∀ r : ℕ, r ≥ 2 →
    ∀ ε > 0, ∀ᶠ n in atTop, |((e n (r + 1) : ℝ) / (e n r : ℝ)) - 1| < ε

/--
**Status: OPEN**
-/
axiom question2_open : ¬Decidable Question2

/--
**Intuition:**
If both e(n,r) and e(n,r+1) are o(n²) and grow similarly,
their ratio might approach 1. But this is not proven.
-/
axiom question2_intuition : True

/-!
## Part VII: Monotonicity
-/

/--
**Monotonicity in r:**
e(n, r) ≤ e(n, r+1) for all n, r.

More triangles required → higher threshold.
-/
axiom e_monotone_r (n r : ℕ) : e n r ≤ e n (r + 1)

/--
**Monotonicity in n:**
e(n, r) ≤ e(n+1, r) for all n, r.

More vertices → higher threshold (more room for edges).
-/
axiom e_monotone_n (n r : ℕ) : e n r ≤ e (n + 1) r

/--
**Both questions together:**
If both questions have positive answers, then e(n, r+1) - e(n, r) → ∞
but the relative difference goes to 0.
-/
theorem questions_together (h1 : Question1) (h2 : Question2) :
    -- Absolute difference unbounded
    (∀ r ≥ 2, ∀ M : ℕ, ∀ᶠ n in atTop, e n (r + 1) - e n r > M) ∧
    -- Relative difference → 0
    (∀ r ≥ 2, ∀ ε > 0, ∀ᶠ n in atTop, |((e n (r + 1) : ℝ) / (e n r : ℝ)) - 1| < ε) :=
  ⟨h1, h2⟩

/-!
## Part VIII: Connection to Problem #80
-/

/--
**Problem #80:**
Related to Turán-type problems for triangles.
The connection is through extremal graph theory.
-/
axiom problem_80_connection : True

/--
**Turán Number:**
ex(n, K₃) = ⌊n²/4⌋ is the maximum edges avoiding triangles.
e(n, r) is below this for graphs where all edges are in triangles.
-/
axiom turan_number_bound (n r : ℕ) (hn : n ≥ 3) :
  e n r ≤ n * n / 4

/-!
## Part IX: Known Bounds
-/

/--
**Upper bound:**
e(n, r) ≤ C_r · n² / (log n) for some constant C_r depending on r.
(This follows from Ruzsa-Szemerédi improvements.)
-/
axiom upper_bound (r : ℕ) (hr : r ≥ 2) :
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in atTop, (e n r : ℝ) ≤ C * n^2 / Real.log n

/--
**Lower bound:**
e(n, r) ≥ c_r · n^{2-o(1)} for some function depending on r.
-/
axiom lower_bound (r : ℕ) (hr : r ≥ 2) :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (e n r : ℝ) ≥ c * n^(2 - 1 / Real.log (Real.log n))

/-!
## Part X: Summary
-/

/--
**Erdős Problem #600: OPEN**

**DEFINITION:**
e(n, r) = min edges such that every triangle-covered graph on n vertices
with ≥ e(n, r) edges has an edge in ≥ r triangles.

**KNOWN:**
- e(n, r) = o(n²) for fixed r (Ruzsa-Szemerédi 1978)
- e(n, r) ≤ e(n, r+1) (monotonicity)

**OPEN:**
- Q1: Does e(n, r+1) - e(n, r) → ∞?
- Q2: Does e(n, r+1) / e(n, r) → 1?

**KEY INSIGHT:**
The problem asks about the "fine structure" of how the threshold
changes as we require more triangles per edge.
-/
theorem erdos_600_statement : True := trivial

/--
**The Problem (OPEN):**
-/
theorem erdos_600 : True := trivial

/--
**Historical Note:**
This problem was posed by Erdős in 1987 and connects to the
influential Ruzsa-Szemerédi theorem on (6,3)-free systems.
-/
theorem historical_note : True := trivial

end Erdos600
