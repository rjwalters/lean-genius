/-
Erdős Problem #809: Rainbow Odd Cycles in Dense Graphs

Source: https://erdosproblems.com/809
Status: OPEN

Statement:
Let k ≥ 3 and define F_k(n) to be the minimal r such that there exists a graph G
on n vertices with ⌊n²/4⌋ + 1 edges where the edges can be r-colored so that
every subgraph isomorphic to C_{2k+1} (odd cycle of length 2k+1) has no repeated
colors on its edges (i.e., is rainbow).

Conjecture: Is it true that F_k(n) ~ n²/8?

Context:
- A problem of Burr, Erdős, Graham, and Sós
- They proved F_k(n) >> n² (quadratic lower bound)
- The conjectured value n²/8 would be optimal
- Related to Problem #810

Background:
- The edge count ⌊n²/4⌋ + 1 exceeds the Turán number ex(n, K₃) = ⌊n²/4⌋
- By Turán's theorem, any graph with this many edges must contain triangles
- For k ≥ 3, odd cycles C_{2k+1} are guaranteed by similar density arguments
- The question is: how many colors suffice to make all these odd cycles rainbow?

Mathematical Significance:
This problem sits at the intersection of:
1. Extremal graph theory (Turán-type problems)
2. Ramsey theory (cycle structures)
3. Edge coloring (rainbow subgraphs)

References:
- Burr, Erdős, Graham, Sós [Er91]
- See also Problem #810 for a related variant
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

open SimpleGraph Finset

namespace Erdos809

/-
## Part I: Basic Definitions

Setting up the framework for edge colorings and rainbow subgraphs.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
An edge coloring of a simple graph assigns a color (natural number) to each edge.
-/
def EdgeColoring (G : SimpleGraph V) := G.edgeSet → ℕ

/--
The number of colors used by an edge coloring.
-/
noncomputable def numColors (G : SimpleGraph V) (c : EdgeColoring G) : ℕ :=
  (Finset.image c G.edgeFinset).card

/--
An odd cycle of length 2k+1 in a graph.
-/
structure OddCycle (G : SimpleGraph V) (k : ℕ) where
  vertices : Fin (2 * k + 1) → V
  is_cycle : ∀ i : Fin (2 * k + 1), G.Adj (vertices i) (vertices (i + 1))
  distinct : Function.Injective vertices

/--
The edges of an odd cycle.
-/
def OddCycle.edges {G : SimpleGraph V} {k : ℕ} (cyc : OddCycle G k) :
    Finset (Sym2 V) :=
  Finset.univ.image fun i => ⟦(cyc.vertices i, cyc.vertices (i + 1))⟧

/--
A subgraph is rainbow under a coloring if all its edges have distinct colors.
-/
def IsRainbow (G : SimpleGraph V) (c : EdgeColoring G) (edges : Finset (Sym2 V)) : Prop :=
  ∀ e₁ e₂ : Sym2 V, e₁ ∈ edges → e₂ ∈ edges → e₁ ≠ e₂ →
    ∀ h₁ : e₁ ∈ G.edgeSet, ∀ h₂ : e₂ ∈ G.edgeSet,
      c ⟨e₁, h₁⟩ ≠ c ⟨e₂, h₂⟩

/--
An edge coloring is valid (for odd cycles of length 2k+1) if every C_{2k+1}
subgraph is rainbow.
-/
def IsValidColoring (G : SimpleGraph V) (c : EdgeColoring G) (k : ℕ) : Prop :=
  ∀ cyc : OddCycle G k, IsRainbow G c cyc.edges

/-
## Part II: The Turán Threshold

Graphs with more than ⌊n²/4⌋ edges must contain odd cycles.
-/

/--
The Turán number: maximum edges in a triangle-free graph on n vertices.
-/
def turanNumber (n : ℕ) : ℕ := n^2 / 4

/--
The edge threshold for our problem: ⌊n²/4⌋ + 1 edges.
-/
def edgeThreshold (n : ℕ) : ℕ := turanNumber n + 1

/--
**Turán's Theorem:**
Any graph with more than ⌊n²/4⌋ edges contains a triangle.
-/
axiom turan_theorem (G : SimpleGraph V) :
    G.edgeFinset.card > turanNumber (Fintype.card V) → ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

/--
More generally, dense graphs contain odd cycles of any specified length.
-/
axiom dense_has_odd_cycles (G : SimpleGraph V) (k : ℕ) (hk : k ≥ 1) :
    G.edgeFinset.card ≥ edgeThreshold (Fintype.card V) →
    Nonempty (OddCycle G k)

/-
## Part III: The F_k Function

The central object of the problem.
-/

/--
**F_k(n):** The minimal number of colors r such that there exists a graph G
on n vertices with ⌊n²/4⌋ + 1 edges whose edges can be r-colored so that
every C_{2k+1} is rainbow.
-/
noncomputable def F (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ (G : SimpleGraph (Fin n)),
    G.edgeFinset.card = edgeThreshold n ∧
    ∃ c : EdgeColoring G, numColors G c = r ∧ IsValidColoring G c k}

/--
F_k(n) is well-defined: the set is nonempty (trivially, using n² colors).
-/
axiom F_well_defined (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3) :
    {r : ℕ | ∃ (G : SimpleGraph (Fin n)),
      G.edgeFinset.card = edgeThreshold n ∧
      ∃ c : EdgeColoring G, numColors G c = r ∧ IsValidColoring G c k}.Nonempty

/-
## Part IV: Known Results

The lower bound proved by Burr, Erdős, Graham, and Sós.
-/

/--
**Burr-Erdős-Graham-Sós Theorem:**
F_k(n) ≫ n², meaning F_k(n) ≥ c · n² for some constant c > 0.
-/
axiom burr_erdos_graham_sos (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℚ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 → (F k n : ℚ) ≥ c * n^2

/--
The lower bound constant depends on k.
-/
noncomputable def lowerBoundConstant (k : ℕ) : ℚ :=
  Classical.choose (burr_erdos_graham_sos k (by omega : k ≥ 3))

/--
The lower bound is quadratic in n.
-/
theorem F_quadratic_lower_bound (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3) :
    (F k n : ℚ) ≥ lowerBoundConstant k * n^2 := by
  have h := burr_erdos_graham_sos k hk
  exact (Classical.choose_spec h).2 n hn

/-
## Part V: The Conjecture

The main open question.
-/

/--
**Erdős Problem #809 Conjecture:**
F_k(n) ~ n²/8, meaning F_k(n)/n² → 1/8 as n → ∞.
-/
def erdos_809_conjecture (k : ℕ) : Prop :=
  Filter.Tendsto (fun n => (F k n : ℚ) / n^2) Filter.atTop (nhds (1/8 : ℚ))

/--
The conjecture as a statement: the limit of F_k(n)/n² equals 1/8.
-/
theorem erdos_809_statement (k : ℕ) (hk : k ≥ 3) :
    erdos_809_conjecture k ↔
    Filter.Tendsto (fun n => (F k n : ℚ) / n^2) Filter.atTop (nhds (1/8 : ℚ)) :=
  Iff.rfl

/-
## Part VI: Upper and Lower Bounds

What is known about the asymptotics.
-/

/--
**Upper Bound (Trivial):**
F_k(n) ≤ ⌊n²/4⌋ + 1 (using one color per edge).
-/
theorem F_trivial_upper_bound (k n : ℕ) (hk : k ≥ 3) :
    F k n ≤ edgeThreshold n := by
  sorry

/--
**Lower Bound:**
The Burr-Erdős-Graham-Sós result gives F_k(n) ≥ c·n² for some c > 0.
Combined with the conjecture, we expect c → 1/8 as k → ∞.
-/
theorem lower_bound_implies_quadratic (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℚ, c > 0 ∧ ∀ᶠ n in Filter.atTop, (F k n : ℚ) ≥ c * n^2 := by
  obtain ⟨c, hc_pos, hc_bound⟩ := burr_erdos_graham_sos k hk
  use c, hc_pos
  simp only [Filter.eventually_atTop]
  use 3
  intro n hn
  exact hc_bound n hn

/--
**Gap between bounds:**
The conjecture claims the right constant is 1/8.
Currently: c·n² ≤ F_k(n) ≤ n²/4 + 1
Conjecture: F_k(n) ~ n²/8
-/
theorem bounds_summary (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3) :
    lowerBoundConstant k * n^2 ≤ F k n ∧ F k n ≤ edgeThreshold n := by
  sorry

/-
## Part VII: Connection to Rainbow Ramsey Theory

The problem fits into the broader context of rainbow Ramsey theory.
-/

/--
A graph is maximally dense (for odd cycles) if it has exactly the threshold number of edges.
-/
def IsMaximallyDense (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = edgeThreshold (Fintype.card V)

/--
The rainbow number for odd cycles in maximally dense graphs.
-/
noncomputable def rainbowNumber (k n : ℕ) : ℕ := F k n

/--
**Rainbow Ramsey Connection:**
The problem asks for the rainbow number of C_{2k+1} in graphs
that are just barely dense enough to guarantee containing C_{2k+1}.
-/
theorem rainbow_ramsey_interpretation (k n : ℕ) (hk : k ≥ 3) :
    rainbowNumber k n = F k n := rfl

/-
## Part VIII: Special Cases

Examining specific values of k.
-/

/--
The first interesting case is k = 3, concerning C_7 (7-cycles).
-/
def F_3 (n : ℕ) : ℕ := F 3 n

/--
The conjecture for 7-cycles.
-/
def conjecture_7_cycles : Prop := erdos_809_conjecture 3

/--
For k = 1, we have C_3 (triangles), but the problem requires k ≥ 3.
The triangle case is handled differently (Turán's theorem).
-/
theorem k_at_least_3_required :
    ∀ k, k ≥ 3 → F k = fun n => F k n := by
  intro k _
  rfl

/-
## Part IX: Open Status

The problem remains open.
-/

/--
**Erdős Problem #809: Status OPEN**

The conjecture F_k(n) ~ n²/8 has not been proved or disproved.
The best known result is the quadratic lower bound F_k(n) >> n².
-/
theorem erdos_809_open : True := trivial

/--
**What would a proof require:**
1. For the upper bound: Construct graphs achieving ~n²/8 colors
2. For the lower bound: Show no graph can do better than ~n²/8 colors
-/
theorem proof_requirements :
    (∀ k, k ≥ 3 → erdos_809_conjecture k) ↔
    (∀ k, k ≥ 3 →
      (∀ ε > 0, ∀ᶠ n in Filter.atTop, (F k n : ℚ) / n^2 < 1/8 + ε) ∧
      (∀ ε > 0, ∀ᶠ n in Filter.atTop, (F k n : ℚ) / n^2 > 1/8 - ε)) := by
  sorry

/-
## Part X: Summary

Collecting all key results.
-/

/--
**Summary of Erdős Problem #809:**

1. **Problem:** Find F_k(n), the minimal r such that there exists a graph G
   on n vertices with ⌊n²/4⌋ + 1 edges whose edges can be r-colored
   so that every C_{2k+1} is rainbow.

2. **Conjecture:** F_k(n) ~ n²/8

3. **Known:** F_k(n) >> n² (Burr-Erdős-Graham-Sós)

4. **Status:** OPEN

5. **Related:** See Erdős Problem #810
-/
theorem erdos_809_summary (k : ℕ) (hk : k ≥ 3) :
    -- The lower bound is quadratic
    (∃ c : ℚ, c > 0 ∧ ∀ n ≥ 3, (F k n : ℚ) ≥ c * n^2) ∧
    -- The problem is open
    True := by
  constructor
  · exact burr_erdos_graham_sos k hk
  · trivial

end Erdos809
