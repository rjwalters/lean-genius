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

/- ## Part I: Graph Definitions -/

/-- **Simple Graph:**
A graph on n vertices represented by its edge set. -/
structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  symmetric : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  irreflexive : ∀ e ∈ edges, e.1 ≠ e.2

/-- **Edge Count:**
Number of edges in the graph (counting each undirected edge once). -/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  G.edges.card / 2

/-- **Triangle:**
A set of three vertices {u, v, w} forming a triangle in G. -/
def IsTriangle {n : ℕ} (G : Graph n) (u v w : Fin n) : Prop :=
  u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
  (u, v) ∈ G.edges ∧ (v, w) ∈ G.edges ∧ (u, w) ∈ G.edges

/- ## Part II: Edge-Triangle Containment -/

/-- **Triangle Count for an Edge:**
Number of triangles containing a specific edge {u, v}. -/
noncomputable def triangleCount {n : ℕ} (G : Graph n) (u v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => IsTriangle G u v w)).card

/-- **Edge in at Least One Triangle:**
An edge is "triangle-covered" if it's in at least one triangle. -/
def IsTriangleCovered {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  triangleCount G u v ≥ 1

/-- **All Edges Triangle-Covered:**
Every edge in G is contained in at least one triangle. -/
def AllEdgesTriangleCovered {n : ℕ} (G : Graph n) : Prop :=
  ∀ e ∈ G.edges, ∃ w : Fin n, IsTriangle G e.1 e.2 w

/-- **Some Edge in r Triangles:**
G has at least one edge contained in at least r triangles. -/
def HasEdgeInRTriangles {n : ℕ} (G : Graph n) (r : ℕ) : Prop :=
  ∃ u v : Fin n, (u, v) ∈ G.edges ∧ triangleCount G u v ≥ r

/- ## Part III: The e(n,r) Function -/

/-- **The Function e(n,r):**
Minimal number of edges such that every graph on n vertices with
≥ e(n,r) edges, all triangle-covered, has some edge in ≥ r triangles. -/
noncomputable def e (n r : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ G : Graph n,
    edgeCount G ≥ m → AllEdgesTriangleCovered G → HasEdgeInRTriangles G r }

/-- **e is well-defined:**
The set is non-empty (bounded by n²/2). -/
/- ## Part IV: Ruzsa-Szemerédi Result -/

/-- **Ruzsa-Szemerédi (1978):**
e(n, r) = o(n²) for any fixed r.
This means e(n, r) grows subquadratically in n.
The proof uses the triangle removal lemma. -/
axiom ruzsa_szemeredi (r : ℕ) (hr : r ≥ 2) :
  ∀ ε > 0, ∀ᶠ n in atTop, (e n r : ℝ) < ε * n^2

/- ## Part V: The Two Open Questions -/

/-- **Question 1:**
Does e(n, r+1) - e(n, r) → ∞ as n → ∞?
This asks whether the gap between consecutive thresholds grows without bound. -/
def Question1 : Prop :=
  ∀ r : ℕ, r ≥ 2 → ∀ M : ℕ, ∀ᶠ n in atTop, e n (r + 1) - e n r > M

/-- **Question 2:**
Does e(n, r+1) / e(n, r) → 1 as n → ∞?
This asks whether consecutive thresholds are asymptotically equivalent. -/
def Question2 : Prop :=
  ∀ r : ℕ, r ≥ 2 →
    ∀ ε > 0, ∀ᶠ n in atTop, |((e n (r + 1) : ℝ) / (e n r : ℝ)) - 1| < ε

/- ## Part VI: Monotonicity -/

/-- **Monotonicity in r:**
e(n, r) ≤ e(n, r+1) for all n, r.
More triangles required → higher threshold. -/
axiom e_monotone_r (n r : ℕ) : e n r ≤ e n (r + 1)

/-- **Monotonicity in n:**
e(n, r) ≤ e(n+1, r) for all n, r.
More vertices → higher threshold (more room for edges). -/
axiom e_monotone_n (n r : ℕ) : e n r ≤ e (n + 1) r

/-- **Both questions together:**
If both questions have positive answers, then e(n, r+1) - e(n, r) → ∞
but the relative difference goes to 0. -/
theorem questions_together (h1 : Question1) (h2 : Question2) :
    (∀ r ≥ 2, ∀ M : ℕ, ∀ᶠ n in atTop, e n (r + 1) - e n r > M) ∧
    (∀ r ≥ 2, ∀ ε > 0, ∀ᶠ n in atTop, |((e n (r + 1) : ℝ) / (e n r : ℝ)) - 1| < ε) :=
  ⟨h1, h2⟩

/- ## Part VII: Known Bounds -/

/-- **Turán number bound:**
e(n, r) ≤ ⌊n²/4⌋ since ex(n, K₃) = ⌊n²/4⌋ and e(n,r) only considers
graphs where all edges are in triangles. -/
/-- **Upper bound:**
e(n, r) ≤ C_r · n² / (log n) for some constant C_r depending on r.
This follows from improvements to the Ruzsa-Szemerédi result. -/
/-- **Lower bound:**
e(n, r) ≥ c_r · n^{2-o(1)} for some function depending on r.
The threshold is nearly quadratic from below. -/
/- ## Part VIII: Summary -/

/-- **Summary of Erdős Problem #600:**

PROBLEM: Define e(n,r) = min edges forcing some edge in ≥ r triangles
(among triangle-covered graphs on n vertices).

KNOWN:
- e(n, r) = o(n²) for fixed r (Ruzsa-Szemerédi 1978)
- e(n, r) is monotone in both n and r

OPEN:
- Q1: Does e(n, r+1) - e(n, r) → ∞?
- Q2: Does e(n, r+1) / e(n, r) → 1?

This theorem packages the known results: subquadratic growth
and monotonicity in both parameters. -/
theorem erdos_600_summary :
    (∀ r : ℕ, r ≥ 2 → ∀ ε > 0, ∀ᶠ n in atTop, (e n r : ℝ) < ε * n^2) ∧
    (∀ n r : ℕ, e n r ≤ e n (r + 1)) ∧
    (∀ n r : ℕ, e n r ≤ e (n + 1) r) :=
  ⟨fun r hr => ruzsa_szemeredi r hr, e_monotone_r, e_monotone_n⟩

end Erdos600
