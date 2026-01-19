/-
Erdős Problem #80: Book Size in Triangle-Saturated Graphs

Source: https://erdosproblems.com/80
Status: OPEN

Statement:
Let c > 0 and define f_c(n) as the maximum m such that every graph G with:
- n vertices
- at least cn² edges
- every edge contained in at least one triangle

must contain a book of size m (an edge shared by at least m triangles).

Questions:
1. Estimate f_c(n)
2. Is f_c(n) > n^ε for some ε > 0? (DISPROVED by Fox-Loh 2012)
3. Is f_c(n) ≫ log n? (OPEN)

Known Results:
- For c < 1/4: f_c(n) ≪ n^{1/2} (Alon-Trotter)
- For c < 1/4: f_c(n) ≤ n^{O(1/log log n)} (Fox-Loh 2012)
- For c > 1/4: f_c(n) ≥ n/6 (Edwards, Khadziivanov-Nikiforov 1979)
- For all c: f_c(n) → ∞ (Szemerédi regularity)

The problem remains OPEN: the precise growth rate for c < 1/4 is unknown.

References:
- Erdős & Rothschild: Original problem
- Alon-Trotter: n^{1/2} upper bound construction
- Fox-Loh (2012): Disproved polynomial growth
- Edwards, Khadziivanov-Nikiforov (1979): Linear bound for c > 1/4
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset Real

namespace Erdos80

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: Basic Definitions

Definitions for triangles and books in graphs.
-/

/--
**Triangle in a Graph:**
A triangle is a set of three vertices {a, b, c} that are pairwise adjacent.
-/
def isTriangle (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/--
**Edge in a Triangle:**
An edge (u, v) is in a triangle if there exists a third vertex w
such that {u, v, w} forms a triangle.
-/
def edgeInTriangle (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∃ w : V, isTriangle G u v w

/--
**Triangle-Saturated Graph:**
A graph where every edge is contained in at least one triangle.
-/
def isTriangleSaturated (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v → edgeInTriangle G u v

/--
**Book of Size m:**
A book of size m is an edge (u, v) that is shared by at least m triangles.
The edge is the "spine" and the triangles are the "pages".
-/
def bookSize (G : SimpleGraph V) (u v : V) : ℕ :=
  (Finset.univ.filter fun w => isTriangle G u v w).card

/--
**Has Book of Size m:**
A graph has a book of size m if some edge achieves book size at least m.
-/
def hasBook (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, G.Adj u v ∧ bookSize G u v ≥ m

/--
**Maximum Book Size:**
The largest book in the graph.
-/
noncomputable def maxBookSize (G : SimpleGraph V) : ℕ :=
  Finset.sup' (Finset.univ ×ˢ Finset.univ).attach
    (by simp [Finset.attach_nonempty_iff])
    (fun ⟨⟨u, v⟩, _⟩ => if G.Adj u v then bookSize G u v else 0)

/-
## Part II: The f_c(n) Function

The central object of Erdős Problem #80.
-/

/--
**Dense Graph:**
A graph on n vertices with at least cn² edges.
-/
def isDense (G : SimpleGraph V) (c : ℝ) : Prop :=
  (G.edgeFinset.card : ℝ) ≥ c * (Fintype.card V : ℝ)^2

/--
**f_c(n):** The Erdős-Rothschild Function

The maximum m such that every n-vertex graph with:
- At least cn² edges
- Every edge in a triangle

must contain a book of size at least m.
-/
noncomputable def f (c : ℝ) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    Fintype.card V = n →
    ∀ G : SimpleGraph V, isDense G c → isTriangleSaturated G →
    hasBook G m}

/-
## Part III: Known Upper Bounds

The phase transition at c = 1/4.
-/

/--
**Alon-Trotter Upper Bound:**
For c < 1/4: f_c(n) ≪ n^{1/2}

There exist triangle-saturated graphs with cn² edges
where the maximum book size is O(√n).
-/
axiom alon_trotter_bound (c : ℝ) (hc : c < 1/4) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (f c n : ℝ) ≤ C * Real.sqrt n

/--
**Fox-Loh Upper Bound (2012):**
For c < 1/4: f_c(n) ≤ n^{O(1/log log n)}

This disproves Erdős's conjecture that f_c(n) > n^ε for some ε > 0.
-/
axiom fox_loh_bound (c : ℝ) (hc : c < 1/4) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    (f c n : ℝ) ≤ n ^ (C / Real.log (Real.log n))

/--
**Erdős's Polynomial Conjecture: DISPROVED**
f_c(n) > n^ε for some ε > 0 is FALSE for c < 1/4.
-/
theorem erdos_polynomial_conjecture_false (c : ℝ) (hc : c < 1/4) :
    ¬∃ ε : ℝ, ε > 0 ∧ ∀ n : ℕ, n ≥ 2 → (f c n : ℝ) > n ^ ε := by
  intro ⟨ε, hε, hbound⟩
  obtain ⟨C, hC, hfox⟩ := fox_loh_bound c hc
  -- For large n, n^ε > n^{C/log log n}, contradiction
  sorry

/-
## Part IV: Known Lower Bounds
-/

/--
**Edwards-Khadziivanov-Nikiforov Bound:**
For c > 1/4: f_c(n) ≥ n/6

Above the threshold 1/4, books of linear size are guaranteed.
-/
axiom linear_bound_above_threshold (c : ℝ) (hc : c > 1/4) :
  ∀ n : ℕ, n ≥ 1 → f c n ≥ n / 6

/--
**Szemerédi Regularity Bound:**
For all c > 0: f_c(n) → ∞ as n → ∞.

The regularity lemma implies book size tends to infinity,
but with very weak (tower-type) bounds.
-/
axiom regularity_lower_bound (c : ℝ) (hc : c > 0) :
  Filter.Tendsto (fun n => (f c n : ℝ)) Filter.atTop Filter.atTop

/--
**Regularity gives f_c(n) ≥ some function tending to ∞:**
This is a weak lower bound.
-/
theorem f_tends_to_infinity (c : ℝ) (hc : c > 0) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f c n > M := by
  intro M
  have h := regularity_lower_bound c hc
  -- Tendsto implies eventually > M
  sorry

/-
## Part V: The Phase Transition
-/

/--
**Phase Transition at c = 1/4:**
The threshold c = 1/4 separates two regimes:
- c > 1/4: Linear books (f_c(n) ≥ n/6)
- c < 1/4: Subpolynomial books (f_c(n) ≤ n^{o(1)})
-/
def critical_threshold : ℝ := 1/4

/--
**Above threshold: Linear growth**
-/
theorem above_threshold_linear (c : ℝ) (hc : c > critical_threshold) :
    ∃ δ : ℝ, δ > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f c n : ℝ) ≥ δ * n := by
  use 1/6
  constructor
  · norm_num
  · intro n hn
    have h := linear_bound_above_threshold c hc n hn
    simp only [ge_iff_le, Nat.one_le_cast]
    calc (f c n : ℝ) ≥ (n / 6 : ℕ) := by exact_mod_cast h
      _ ≥ (1/6) * n := by
        rw [Nat.cast_div_le]
        ring_nf
        sorry

/--
**Below threshold: Subpolynomial growth**
-/
theorem below_threshold_subpolynomial (c : ℝ) (hc : c < critical_threshold) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f c n : ℝ) ≤ n ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hfox⟩ := fox_loh_bound c hc
  -- For large n, C/log log n < ε
  sorry

/-
## Part VI: Open Questions
-/

/--
**Erdős's Weaker Conjecture: OPEN**
Is f_c(n) ≫ log n for c < 1/4?
-/
def erdos_log_conjecture (c : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → (f c n : ℝ) ≥ C * Real.log n

/--
**This conjecture remains OPEN for c < 1/4.**
-/
axiom erdos_log_conjecture_open (c : ℝ) (hc : 0 < c ∧ c < 1/4) :
  True  -- The status is unknown: neither proved nor disproved

/-
## Part VII: Main Results Summary
-/

/--
**Erdős Problem #80: OPEN**

Summary of known results:
1. f_c(n) → ∞ for all c > 0 (regularity lemma)
2. f_c(n) ≥ n/6 for c > 1/4 (linear threshold)
3. f_c(n) ≤ n^{O(1/log log n)} for c < 1/4 (Fox-Loh)
4. f_c(n) > n^ε conjecture DISPROVED for c < 1/4
5. f_c(n) ≫ log n conjecture OPEN

The gap between lower bounds (regularity) and upper bounds (Fox-Loh)
for c < 1/4 is enormous and constitutes the main open problem.
-/
theorem erdos_80_summary (c : ℝ) (hc : c > 0) :
    -- f_c(n) → ∞
    (Filter.Tendsto (fun n => (f c n : ℝ)) Filter.atTop Filter.atTop) ∧
    -- For c > 1/4: linear bound
    (c > 1/4 → ∃ δ : ℝ, δ > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f c n : ℝ) ≥ δ * n) ∧
    -- For c < 1/4: subpolynomial upper bound exists
    (c < 1/4 → ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f c n : ℝ) ≤ n ^ ε) :=
  ⟨regularity_lower_bound c hc,
   fun h => above_threshold_linear c h,
   fun h => below_threshold_subpolynomial c h⟩

/--
**Problem Status: OPEN**
The precise growth rate of f_c(n) for c < 1/4 remains unknown.
-/
theorem erdos_80_is_open : True := trivial

end Erdos80
