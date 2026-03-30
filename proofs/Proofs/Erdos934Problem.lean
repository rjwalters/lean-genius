/-
Erdős Problem #934: Edge Distance in Bounded-Degree Graphs

Source: https://erdosproblems.com/934
Status: SOLVED (for specific cases, general bounds known)

Statement:
Let h_t(d) be minimal such that every graph G with h_t(d) edges and maximum
degree ≤ d contains two edges whose shortest path between them has length ≥ t.

Estimate h_t(d).

Background:
This problem studies how many edges a graph can have before it must contain
two edges that are "far apart" in the graph metric. The distance between
edges is the minimum distance between their endpoints.

Known Results:
- h_1(d) = d + 1 (trivial)
- h_2(d) = ⌊5d²/4⌋ + 1 (Chung-Gyárfás-Tuza-Trotter 1990)
- h_3(3) = 23 (Cambie-Cames van Batenburg-de Joannis de Verclos-Kang 2022)
- General: (1-o(1))d^t ≤ h_t(d) ≤ (3/2)d^t + 1

References:
- [Er88] Erdős, "Problems and results in combinatorial analysis"
- [CGTT90] Chung-Gyárfás-Tuza-Trotter, "Maximum edges in 2K₂-free graphs"
- [CCJK22] Cambie et al., "Maximizing line subgraphs of diameter at most t"
- [BBPP83] Bermond-Bond-Paoli-Peyrat, "Graphs and interconnection networks"

Tags: graph-theory, extremal-combinatorics, edge-distance, bounded-degree
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace Erdos934

open SimpleGraph

/-
## Part 1: Edge Distance
-/

/-- An edge in a simple graph -/
structure Edge (V : Type*) where
  u : V
  v : V
  adj : u ≠ v

/-- Distance between two edges: minimum distance between any of their endpoints -/
noncomputable def edgeDist {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] (e₁ e₂ : Edge V) : ℕ :=
  min (min (G.dist e₁.u e₂.u) (G.dist e₁.u e₂.v))
      (min (G.dist e₁.v e₂.u) (G.dist e₁.v e₂.v))

/-- Two edges are t-separated if their distance is at least t -/
def AreTSeparated {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] (e₁ e₂ : Edge V) (t : ℕ) : Prop :=
  edgeDist G e₁ e₂ ≥ t

/-
## Part 2: The h_t(d) Function
-/

/-- Maximum degree of a graph -/
noncomputable def maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ (fun v => G.degree v)

/-- Number of edges in a graph -/
noncomputable def numEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- Property: Graph has max degree ≤ d and has t-separated edges -/
def HasTSeparatedEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ∃ e₁ e₂ : Edge V, G.Adj e₁.u e₁.v ∧ G.Adj e₂.u e₂.v ∧
    (e₁.u, e₁.v) ≠ (e₂.u, e₂.v) ∧ AreTSeparated G e₁ e₂ t

/-- h_t(d) is the minimum m such that any graph with m edges and max degree ≤ d
    has two t-separated edges -/
noncomputable def h (t d : ℕ) : ℕ :=
  Nat.find (⟨d^t + 1, sorry⟩ : ∃ m, ∀ V : Type*, ∀ _ : Fintype V,
    ∀ G : SimpleGraph V, [DecidableEq V] → [DecidableRel G.Adj] →
    maxDegree G ≤ d → numEdges G ≥ m → HasTSeparatedEdges G t)

/-
## Part 3: Trivial Case h_1(d)
-/

/-- h_1(d) = d + 1: One edge beyond a star forces distance ≥ 1 -/
axiom h_1_exact (d : ℕ) (hd : d ≥ 1) : h 1 d = d + 1

/-- Upper bound for h_1: a star with d edges has no 1-separated edges -/
theorem h_1_upper_bound (d : ℕ) : h 1 d ≤ d + 1 := by
  sorry

/-- Lower bound for h_1: d edges can avoid 1-separation -/
theorem h_1_lower_bound (d : ℕ) : h 1 d > d := by
  sorry

/-
## Part 4: The h_2(d) Case (2K₂-free graphs)
-/

/-- Two edges are 2-separated means they form an induced 2K₂ -/
theorem two_separated_is_2K2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : Edge V) :
    AreTSeparated G e₁ e₂ 2 ↔
    (¬G.Adj e₁.u e₂.u ∧ ¬G.Adj e₁.u e₂.v ∧ ¬G.Adj e₁.v e₂.u ∧ ¬G.Adj e₁.v e₂.v) := by
  sorry

/-- Chung-Gyárfás-Tuza-Trotter (1990): Exact value of h_2(d) -/
axiom cgtt_1990 (d : ℕ) (hd : d ≥ 1) : h 2 d = (5 * d^2) / 4 + 1

/-- For even d: h_2(d) = 5d²/4 + 1 exactly -/
/-- Erdős-Nešetřil and Bermond-Bond-Paoli-Peyrat conjecture (proved by CGTT) -/
theorem erdos_nesetril_conjecture_proved :
    ∀ d : ℕ, d ≥ 1 → h 2 d ≤ 5 * d^2 / 4 + 1 := by
  intro d _
  sorry

/-
## Part 5: The h_3(d) Case
-/

/-- h_3(3) = 23 (Cambie et al. 2022) -/
axiom h_3_3 : h 3 3 = 23

/-- Conjecture: h_3(d) ≤ d³ - d² + d + 2 -/
def H3Conjecture : Prop :=
  ∀ d : ℕ, d ≥ 1 → h 3 d ≤ d^3 - d^2 + d + 2

/-- Equality in h_3 conjecture iff d = p^k + 1 for prime power p^k -/
def H3EqualityCondition (d : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ d = p^k + 1

/-
## Part 6: General Bounds
-/

/-- Upper bound: h_t(d) ≤ 2d^t (trivial) -/
/-- Improved upper bound: h_t(d) ≤ (3/2)d^t + 1 (Cambie et al. 2022) -/
axiom improved_upper_bound (t d : ℕ) (ht : t ≥ 1) (hd : d ≥ 1) :
    (h t d : ℝ) ≤ (3/2) * d^t + 1

/-- Lower bound for large t: h_t(d) ≥ 0.629^t · d^t for infinitely many d -/
/-- Asymptotic conjecture: (1-o(1))d^t ≤ h_t(d) ≤ (1+o(1))d^t -/
def AsymptoticConjecture : Prop :=
  ∀ t : ℕ, t ≥ 3 →
    -- Lower: for infinitely many d, h_t(d) ≥ (1-o(1))d^t
    (∀ ε > 0, ∃ᶠ d in Filter.atTop, (h t d : ℝ) ≥ (1 - ε) * d^t) ∧
    -- Upper: for all d, h_t(d) ≤ (1+o(1))d^t
    (∀ ε > 0, ∃ D : ℕ, ∀ d ≥ D, (h t d : ℝ) ≤ (1 + ε) * d^t)

/-
## Part 7: Monotonicity Properties
-/

/-- h_t(d) is non-decreasing in d -/
theorem h_mono_d (t d₁ d₂ : ℕ) (hd : d₁ ≤ d₂) :
    h t d₁ ≤ h t d₂ := by
  sorry

/-- h_t(d) is non-decreasing in t -/
theorem h_mono_t (t₁ t₂ d : ℕ) (ht : t₁ ≤ t₂) :
    h t₁ d ≤ h t₂ d := by
  sorry

/-- h_t(d) grows like d^t -/
theorem h_polynomial_growth (t d : ℕ) (ht : t ≥ 1) (hd : d ≥ 1) :
    (h t d : ℝ) ≤ 2 * d^t ∧ (h t d : ℝ) ≥ d^(t-1) := by
  sorry

/-
## Part 8: Connection to Line Graphs
-/

/-- Line graph connection: h_t(d) - 1 equals the maximum number of edges in a
    graph with max degree ≤ d whose line graph has diameter < t. The line graph
    L(G) has edges of G as vertices, with two vertices adjacent iff the
    corresponding edges share an endpoint in G. -/
/-
## Part 9: Extremal Constructions
-/

/-- Star graph achieves h_1(d) - 1: a star with d edges has max degree d
    and no pair of edges at distance ≥ 1 (all edges share the center). -/
/-- For h_2(d) with even d, there exist 2K₂-free graphs achieving 5d²/4 edges -/
/-- Projective plane constructions give extremal graphs for h_3.
    The incidence graph of PG(2,q) gives good lower bounds when q is prime. -/
/-
## Part 10: Erdős's Comment
-/

/-- Erdős [1988]: "This problem seems to be interesting only if there is
    a nice expression for h_t(d)." The t=1 and t=2 cases have clean formulas;
    t=3 has a conjectured formula. -/
theorem erdos_nice_formulas :
    (∀ d : ℕ, d ≥ 1 → h 1 d = d + 1) ∧
    (∀ d : ℕ, d ≥ 1 → h 2 d = 5 * d^2 / 4 + 1) := by
  exact ⟨h_1_exact, cgtt_1990⟩

/-
## Part 11: Summary
-/

/-- Main theorem: Status of Erdős Problem #934 -/
theorem erdos_934 :
    -- h_1(d) = d + 1 (solved, trivial)
    (∀ d : ℕ, d ≥ 1 → h 1 d = d + 1) ∧
    -- h_2(d) = ⌊5d²/4⌋ + 1 (solved, CGTT 1990)
    (∀ d : ℕ, d ≥ 1 → h 2 d = 5 * d^2 / 4 + 1) ∧
    -- h_3(3) = 23 (Cambie et al. 2022)
    h 3 3 = 23 ∧
    -- General bounds: (1-o(1))d^t to (3/2)d^t + 1
    (∀ t d : ℕ, t ≥ 1 → d ≥ 1 → (h t d : ℝ) ≤ (3/2) * d^t + 1) := by
  refine ⟨h_1_exact, ?_, h_3_3, ?_⟩
  · intro d hd; exact cgtt_1990 d hd
  · intro t d ht hd; exact improved_upper_bound t d ht hd

/-- Summary: h_t(d) is solved for t ≤ 2, with h_1(d) = d+1 and
    h_2(d) = ⌊5d²/4⌋+1. For t = 3 the value h_3(3) = 23 is known.
    General bounds: h_t(d) ≤ (3/2)d^t + 1 for all t,d ≥ 1. -/
theorem erdos_934_summary :
    (∀ d, d ≥ 1 → h 1 d = d + 1) ∧
    (∀ d, d ≥ 1 → h 2 d = 5 * d^2 / 4 + 1) ∧
    h 3 3 = 23 := by
  exact ⟨h_1_exact, cgtt_1990, h_3_3⟩

end Erdos934
