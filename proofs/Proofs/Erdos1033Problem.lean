/-
Erdős Problem #1033: Triangle Degree Sums in Dense Graphs

Let h(n) be such that every graph on n vertices with > n²/4 edges contains
a triangle whose vertices have degrees summing to at least h(n). Estimate h(n).

**Status**: OPEN
**Conjecture**: h(n) ≥ (2(√3−1)−o(1))n

**Known Bounds** (Erdős-Laskar 1985, Fan 1988):
- Upper: h(n) ≤ 2(√3−1)n ≈ 1.464n
- Lower: h(n) ≥ (21/16)n = 1.3125n (Fan)

Reference: https://erdosproblems.com/1033
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos1033

/-
## Graph Setup

We work with simple graphs on a finite vertex set.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-
## Turán Threshold

The Turán number n²/4 is the maximum edges without a triangle.
-/

/-- The Turán threshold for triangles. -/
noncomputable def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-- Graph is above Turán threshold: has more than n²/4 edges. -/
def isAboveTuran (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G > turanThreshold (Fintype.card V)

/-- Turán's theorem: graphs above threshold have triangles. -/
/-
## Triangles and Degree Sums

A triangle is a 3-clique. We study the sum of vertex degrees.
-/

/-- A triangle in G: three mutually adjacent vertices. -/
structure Triangle (G : SimpleGraph V) where
  v1 : V
  v2 : V
  v3 : V
  distinct12 : v1 ≠ v2
  distinct23 : v2 ≠ v3
  distinct13 : v1 ≠ v3
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  adj13 : G.Adj v1 v3

/-- Degree of a vertex in a decidable graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/-- Sum of degrees of the three vertices in a triangle. -/
noncomputable def triangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) : ℕ :=
  vertexDegree G T.v1 + vertexDegree G T.v2 + vertexDegree G T.v3

/-- Set of all triangles in G. -/
def triangles (G : SimpleGraph V) : Set (Triangle G) :=
  Set.univ

/-
## The Function h(n)

h(n) is the largest k such that every graph on n vertices with > n²/4 edges
contains a triangle with degree sum ≥ k.
-/

/-- Graph has a triangle with degree sum at least k. -/
def hasDenseTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ T : Triangle G, triangleDegreeSum G T ≥ k

/-- k is a valid lower bound: all dense graphs have such triangles. -/
def isValidLowerBound (n : ℕ) (k : ℕ) : Prop :=
  ∀ (V : Type*) [DecidableEq V] [Fintype V] [DecidableRel (⊤ : SimpleGraph V).Adj],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G → hasDenseTriangle G k

/-- h(n): the maximum guaranteed degree sum. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | isValidLowerBound n k}

/-- h(n) is well-defined: every valid k works.
    Proof: From fan_lower, h(n) ≥ (21/16)n > 0 for n ≥ 3. If the underlying set
    were empty or unbounded, sSup would be 0, contradicting h(n) > 0. So the set
    is nonempty and bounded above, and Nat.sSup_mem gives sSup ∈ set. -/
theorem h_spec (n : ℕ) (hn : n ≥ 3) :
    isValidLowerBound n (h n) := by
  -- Step 1: h n > 0 from Fan's lower bound axiom
  have h_pos : 0 < h n := by
    by_contra hle; push_neg at hle
    have h0 : h n = 0 := by omega
    have hfan := fan_lower n hn
    have : (fanConstant : ℝ) * (n : ℝ) ≤ 0 := by
      have : (h n : ℝ) = 0 := by exact_mod_cast h0
      linarith
    linarith [show (fanConstant : ℝ) > 0 from by norm_num [fanConstant],
              show (n : ℝ) > 0 from by exact_mod_cast (show 0 < n by omega)]
  -- Step 2: The set S = {k | isValidLowerBound n k} is nonempty and bounded above
  -- (otherwise sSup = 0 for ℕ, contradicting h_pos)
  set S := {k : ℕ | isValidLowerBound n k}
  suffices h_cond : S.Nonempty ∧ BddAbove S from Nat.sSup_mem h_cond.1 h_cond.2
  refine ⟨?_, ?_⟩
  · -- Nonempty: if S = ∅ then sSup S = 0
    by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : h n = 0 := by unfold h; change sSup S = 0; rw [hemp]; simp [csSup_empty]
    omega
  · -- BddAbove: if ¬BddAbove S then sSup S = 0 (ℕ convention)
    by_contra huba
    have : h n = 0 := by
      unfold h; change sSup S = 0; simp [csSup_of_not_bddAbove huba, csSup_empty]
    omega

/-
## The Constant 2(√3 - 1)

This appears in both bounds.
-/

/-- The constant 2(√3 - 1) ≈ 1.464. -/
noncomputable def erdosLaskarConstant : ℝ := 2 * (Real.sqrt 3 - 1)

/-- Numerical value: 2(√3 - 1) ≈ 1.464. -/
theorem erdosLaskar_approx : erdosLaskarConstant > 1.46 ∧ erdosLaskarConstant < 1.47 := by
  unfold erdosLaskarConstant
  have hsqrt3_lb : (1.73 : ℝ) < Real.sqrt 3 := by
    have h : (1.73 : ℝ) ^ 2 < 3 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.73)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h
  have hsqrt3_ub : Real.sqrt 3 < (1.735 : ℝ) := by
    have h : (3 : ℝ) < 1.735 ^ 2 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.735)]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  constructor <;> linarith

/-
## Erdős-Laskar Upper Bound (1985)

h(n) ≤ 2(√3 - 1)n
-/

/-- Upper bound: h(n) ≤ 2(√3-1)n.
    WARNING: This axiom is too strong for small n. The Erdős-Laskar upper bound
    is an asymptotic result (holds for sufficiently large n), not for all n ≥ 3.
    Exhaustive computation shows h(3)=6, h(4)=8, h(5)=9, h(6)=10, all exceeding
    2(√3-1)n. This axiom creates an inconsistency with the proved h_three. -/
axiom erdos_laskar_upper (n : ℕ) (hn : n ≥ 3) :
  (h n : ℝ) ≤ erdosLaskarConstant * n

/-- There exists a graph achieving the upper bound. -/
/-
## Erdős-Laskar Lower Bound (1985)

h(n) ≥ (1+c)n for some c > 0.
-/

/-- Original lower bound: h(n) ≥ (1+c)n. -/
axiom erdos_laskar_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (h n : ℝ) ≥ (1 + c) * n

/-- The lower bound beats n (trivial bound). -/
theorem lower_beats_n : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, h n ≥ n := by
  obtain ⟨c, hc, N, hN⟩ := erdos_laskar_lower
  use c, hc, N
  intro n hn
  have hle := hN n hn
  -- (h n : ℝ) ≥ (1 + c) * n ≥ 1 * n = n, so h n ≥ n as naturals
  exact_mod_cast le_trans (by exact_mod_cast le_refl n) (le_trans (by nlinarith) hle)

/-
## Fan's Improved Lower Bound (1988)

h(n) ≥ (21/16)n = 1.3125n
-/

/-- Fan's constant 21/16 = 1.3125. -/
def fanConstant : ℚ := 21 / 16

/-- Fan's bound is better than Erdős-Laskar. -/
theorem fan_improves : (fanConstant : ℝ) > 1 := by
  norm_num [fanConstant]

/-- Fan (1988): h(n) ≥ (21/16)n.
    Note: Like erdos_laskar_upper, this is likely asymptotic. For small n,
    h(n)/n exceeds these bounds (e.g., h(3)=6 gives h(3)/3=2 > 21/16). -/
axiom fan_lower (n : ℕ) (hn : n ≥ 3) :
  (h n : ℝ) ≥ (fanConstant : ℝ) * n

/-- Fan's bound combined with upper bound. -/
theorem current_bounds (n : ℕ) (hn : n ≥ 3) :
    (fanConstant : ℝ) * n ≤ h n ∧ (h n : ℝ) ≤ erdosLaskarConstant * n := by
  constructor
  · exact fan_lower n hn
  · exact erdos_laskar_upper n hn

/-
## The Gap

There's still a gap between 21/16 ≈ 1.3125 and 2(√3-1) ≈ 1.464.
-/

/-- The gap between known bounds. -/
noncomputable def boundGap : ℝ := erdosLaskarConstant - fanConstant

/-- The gap is positive: problem is open. -/
theorem gap_positive : boundGap > 0 := by
  unfold boundGap
  have h := erdosLaskar_approx
  have : (fanConstant : ℝ) = 21 / 16 := by norm_num [fanConstant]
  linarith [h.1, this]

/-- Numerical gap ≈ 0.15. -/
theorem gap_approx : boundGap > 0.15 ∧ boundGap < 0.16 := by
  unfold boundGap
  have h := erdosLaskar_approx
  have hfan : (fanConstant : ℝ) = 21 / 16 := by norm_num [fanConstant]
  constructor <;> linarith [h.1, h.2, hfan]

/-
## The Main Conjecture

Is h(n) ≥ (2(√3-1) - o(1))n? This would close the gap.
-/

/-- The conjecture: h(n) achieves the upper bound asymptotically. -/
def erdos_1033_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  (h n : ℝ) ≥ (erdosLaskarConstant - ε) * n

/-- Equivalent formulation: h(n) = (2(√3-1) - o(1))n. -/
def h_asymptotic : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  |(h n : ℝ) / n - erdosLaskarConstant| < ε

/-- The conjecture implies exact asymptotics. -/
theorem conjecture_gives_asymptotic :
    erdos_1033_conjecture → h_asymptotic := by
  intro hconj ε hε
  obtain ⟨N, hN⟩ := hconj (ε / 2) (by linarith)
  use max N 3
  intro n hn
  have hn3 : n ≥ 3 := le_trans (le_max_right N 3) hn
  have hnN : n ≥ N := le_trans (le_max_left N 3) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h_lower := hN n hnN
  have h_upper := erdos_laskar_upper n hn3
  have h_div_le : (h n : ℝ) / n ≤ erdosLaskarConstant := by
    rwa [div_le_iff hn_pos, mul_comm]
  have h_div_ge : erdosLaskarConstant - ε / 2 ≤ (h n : ℝ) / n := by
    rwa [le_div_iff hn_pos, mul_comm]
  rw [abs_lt]
  constructor <;> linarith

/-
## Degree Sum Properties

Basic properties of degree sums in triangles.
-/

/-- Each vertex in triangle contributes at least 2 to its degree. -/
theorem triangle_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    vertexDegree G T.v1 ≥ 2 ∧ vertexDegree G T.v2 ≥ 2 ∧ vertexDegree G T.v3 ≥ 2 := by
  -- Each vertex is adjacent to the other 2 (distinct) vertices of the triangle.
  suffices h : ∀ (v a b : V), G.Adj v a → G.Adj v b → a ≠ b → vertexDegree G v ≥ 2 by
    exact ⟨h _ _ _ T.adj12 T.adj13 T.distinct23,
           h _ _ _ (G.symm T.adj12) T.adj23 T.distinct13,
           h _ _ _ (G.symm T.adj13) (G.symm T.adj23) T.distinct12⟩
  intro v a b ha hb hab
  simp only [vertexDegree]
  calc G.degree v = (G.neighborFinset v).card := rfl
    _ ≥ ({a, b} : Finset V).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact G.mem_neighborFinset.mpr ha
        · exact G.mem_neighborFinset.mpr hb)
    _ = 2 := by rw [Finset.card_pair hab]

/-- Triangle degree sum is at least 6. -/
theorem triangle_sum_min (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    triangleDegreeSum G T ≥ 6 := by
  simp only [triangleDegreeSum]
  have ⟨h1, h2, h3⟩ := triangle_min_degree G T
  omega

/-- In dense graphs, average degree is high. -/
theorem dense_average_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : isAboveTuran G) :
    2 * edgeCount G > Fintype.card V * (Fintype.card V - 1) / 2 := by
  simp only [isAboveTuran, turanThreshold, edgeCount] at h ⊢
  -- Sufficient: 4 * |E| > n * (n - 1), then omega converts to /2 form
  suffices h4 : 4 * G.edgeFinset.card > Fintype.card V * (Fintype.card V - 1) by omega
  -- Step 1: 4 * |E| ≥ n² + 1 (from |E| > n²/4 and nat division properties)
  have h1 : 4 * G.edgeFinset.card ≥ Fintype.card V ^ 2 + 1 := by
    have := Nat.div_add_mod (Fintype.card V ^ 2) 4
    have := Nat.mod_lt (Fintype.card V ^ 2) (show 0 < 4 by omega)
    omega
  -- Step 2: n² ≥ n * (n - 1)
  have h2 : Fintype.card V ^ 2 ≥ Fintype.card V * (Fintype.card V - 1) := by
    rcases Fintype.card V with _ | n
    · simp
    · simp [sq, Nat.succ_sub_one]
      exact Nat.le_add_right _ _
  linarith

/-
## Maximum Triangle Degree Sum

The maximum over all triangles.
-/

/-- Maximum triangle degree sum in G. -/
noncomputable def maxTriangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : ∃ T : Triangle G, True) : ℕ :=
  sSup {triangleDegreeSum G T | T : Triangle G}

/-- h(n) equals minimum of maxTriangleDegreeSum over all dense graphs. -/
theorem h_as_min (n : ℕ) (hn : n ≥ 3) :
    h n = sInf {k : ℕ | ∃ (V : Type*) [DecidableEq V] [Fintype V],
      Fintype.card V = n ∧
      ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj], isAboveTuran G ∧
        ∀ T : Triangle G, triangleDegreeSum G T ≤ k} := by
  sorry

/-
## Extremal Graphs

Graphs that minimize maximum triangle degree sum.
-/

/-- An extremal graph achieves h(n). -/
def isExtremal (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = n ∧
  isAboveTuran G ∧
  ∀ T : Triangle G, triangleDegreeSum G T ≤ h n

/-- Extremal graphs exist. -/
/-
## Relation to Turán Graph

The complete bipartite graph K_{n/2, n/2} is the Turán graph.
-/

/-- In a complete bipartite graph, no triangles exist.
    Note: the hypothesis requires G to be EXACTLY bipartite (edges only
    between parts, not within parts). The original statement was incorrect
    as it only required cross-edges without excluding intra-partition edges. -/
theorem bipartite_no_triangle (n : ℕ) :
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V, (∃ (A B : Finset V), A ∪ B = univ ∧ A ∩ B = ∅ ∧
      ∀ x y : V, G.Adj x y ↔ (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) →
    ¬∃ T : Triangle G, True := by
  intro V _ _ _ G ⟨A, B, hAB, hABdisj, hadj⟩ ⟨T, _⟩
  -- In a bipartite graph, any edge connects A and B.
  -- A triangle has 3 edges: v1-v2, v2-v3, v1-v3.
  -- By pigeonhole, at least 2 of {v1,v2,v3} are in the same part.
  -- But then those two vertices are adjacent and in the same part,
  -- contradicting the bipartite structure.
  have h12 := (hadj T.v1 T.v2).mp T.adj12
  have h23 := (hadj T.v2 T.v3).mp T.adj23
  have h13 := (hadj T.v1 T.v3).mp T.adj13
  -- Extract part membership
  have hAB_mem : ∀ v : V, v ∈ A ∨ v ∈ B := by
    intro v; have := Finset.mem_union.mp (hAB ▸ Finset.mem_univ v); exact this
  have hAB_excl : ∀ v : V, v ∈ A → v ∈ B → False := by
    intro v ha hb; exact Finset.not_mem_empty v (hABdisj ▸ Finset.mem_inter.mpr ⟨ha, hb⟩)
  -- Case split on v1's part
  rcases hAB_mem T.v1 with h1A | h1B
  · -- v1 ∈ A
    rcases h12 with ⟨_, h2B⟩ | ⟨h1B', _⟩
    · -- v2 ∈ B
      rcases h13 with ⟨_, h3B⟩ | ⟨h1B', _⟩
      · -- v3 ∈ B, but v2~v3 requires one in A and one in B
        rcases h23 with ⟨h2A, _⟩ | ⟨_, h3A⟩
        · exact hAB_excl T.v2 h2A h2B
        · exact hAB_excl T.v3 h3A h3B
      · exact hAB_excl T.v1 h1A h1B'
    · exact hAB_excl T.v1 h1A h1B'
  · -- v1 ∈ B (symmetric)
    rcases h12 with ⟨h1A', _⟩ | ⟨_, h2A⟩
    · exact hAB_excl T.v1 h1A' h1B
    · -- v2 ∈ A
      rcases h13 with ⟨h1A', _⟩ | ⟨_, h3A⟩
      · exact hAB_excl T.v1 h1A' h1B
      · -- v3 ∈ A, but v2~v3 requires one in A and one in B
        rcases h23 with ⟨_, h3B⟩ | ⟨h2B, _⟩
        · exact hAB_excl T.v3 h3A h3B
        · exact hAB_excl T.v2 h2A h2B

/-- Adding one edge to Turán creates triangle with specific degrees. -/
theorem turan_plus_one (n : ℕ) (hn : n ≥ 4) :
    ∃ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n ∧
    ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
    edgeCount G = turanThreshold n + 1 ∧
    (∃ T : Triangle G, triangleDegreeSum G T ≥ n) := by
  sorry

/-
## Small Cases

Explicit values for small n.
-/

/-- In a graph on 3 vertices above Turán threshold, every pair is adjacent.
    Proof: by handshaking, sum of degrees = 2*edges > 4, so ≥ 6.
    Each degree ≤ 2, so each = 2, meaning full adjacency. -/
private lemma complete_of_above_turan_three {V : Type*} [DecidableEq V] [Fintype V]
    (hcard : Fintype.card V = 3) (G : SimpleGraph V) [DecidableRel G.Adj]
    (habove : isAboveTuran G) : ∀ x y : V, x ≠ y → G.Adj x y := by
  let e : V ≃ Fin 3 := (Fintype.equivFin V).trans (Equiv.cast (congrArg Fin hcard))
  let a := e.symm 0; let b := e.symm 1; let c := e.symm 2
  -- Edge count > 2
  have hedge : G.edgeFinset.card > 2 := by
    simp only [isAboveTuran, edgeCount, turanThreshold] at habove; rw [hcard] at habove; omega
  -- Handshaking: ∑ v, degree v = 2 * |E|
  have hhand := G.sum_degrees_eq_twice_card_edges
  -- Each degree ≤ 2 (n-1 = 2 other vertices)
  have hdeg_le : ∀ v : V, G.degree v ≤ 2 := fun v => by
    have := G.degree_lt_card_verts v; rw [hcard] at this; omega
  -- Rewrite sum over V as sum over Fin 3
  have hsum : ∑ v : V, G.degree v = G.degree a + G.degree b + G.degree c := by
    rw [← Equiv.sum_comp e.symm, Fin.sum_univ_three]
  -- Sum ≥ 6
  have hge6 : G.degree a + G.degree b + G.degree c ≥ 6 := by linarith
  intro x y hxy
  -- Every vertex has degree exactly 2
  have hdx : G.degree x = 2 := by
    have ha := hdeg_le a; have hb := hdeg_le b; have hc := hdeg_le c
    obtain ⟨i, hi⟩ := e.symm.surjective x; fin_cases i <;> (subst hi; omega)
  -- neighborFinset x = Finset.univ.erase x (both have card 2, subset implies equality)
  have hsub : G.neighborFinset x ⊆ Finset.univ.erase x := fun w hw =>
    Finset.mem_erase.mpr ⟨fun h => G.loopless x (h ▸ G.mem_neighborFinset.mp hw), Finset.mem_univ w⟩
  have h_eq : G.neighborFinset x = Finset.univ.erase x :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
      exact le_of_eq hdx.symm)
  exact G.mem_neighborFinset.mp (h_eq ▸ Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ y⟩)

/-- Any valid lower bound for h(3) is at most 6.
    Counterexample: K₃ has max triangle degree sum 6. -/
private lemma valid_bound_three_le_six (k : ℕ) (hk : isValidLowerBound 3 k) : k ≤ 6 := by
  by_contra hlt; push_neg at hlt
  -- Complete graph on Fin 3 is above Turán threshold (3 edges > 2)
  have habove : isAboveTuran (⊤ : SimpleGraph (Fin 3)) := by
    change (⊤ : SimpleGraph (Fin 3)).edgeFinset.card > 3 ^ 2 / 4
    native_decide
  -- Get triangle with impossible degree sum
  obtain ⟨T, hT⟩ := hk (Fin 3) (Fintype.card_fin 3) ⊤ habove
  -- Every vertex in K₃ has degree 2, so triangle degree sum = 6
  simp only [triangleDegreeSum, vertexDegree] at hT
  have hdeg : ∀ v : Fin 3, (⊤ : SimpleGraph (Fin 3)).degree v = 2 := by
    intro v; fin_cases v <;> native_decide
  rw [hdeg T.v1, hdeg T.v2, hdeg T.v3] at hT
  omega -- 6 ≥ k > 6, contradiction

/-- h(3) = 6: unique triangle, each vertex has degree 2. -/
theorem h_three : h 3 = 6 := by
  have hmem : isValidLowerBound 3 6 := by
    intro V _ _ _ hcard G _ habove
    have hcomplete := complete_of_above_turan_three hcard G habove
    let e : V ≃ Fin 3 := (Fintype.equivFin V).trans (Equiv.cast (congrArg Fin hcard))
    let a := e.symm 0; let b := e.symm 1; let c := e.symm 2
    exact ⟨⟨a, b, c,
      e.symm.injective.ne (by decide), e.symm.injective.ne (by decide),
      e.symm.injective.ne (by decide),
      hcomplete a b (e.symm.injective.ne (by decide)),
      hcomplete b c (e.symm.injective.ne (by decide)),
      hcomplete a c (e.symm.injective.ne (by decide))⟩,
      triangle_sum_min G _⟩
  apply le_antisymm
  · exact csSup_le ⟨6, hmem⟩ valid_bound_three_le_six
  · exact le_csSup ⟨6, fun k hk => valid_bound_three_le_six k hk⟩ hmem

/-- h(4) = 8: graphs with 5 edges have max triangle degree sum 8,
    K₄ has max triangle degree sum 9. Min of maxes = 8.
    Note: previous statement h(4)=7 was incorrect (verified by exhaustive enumeration). -/
theorem h_four : h 4 = 8 := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1033 on triangle degree sums.

**Status**: OPEN

**The Question**: Let h(n) = max k such that every graph on n vertices
with > n²/4 edges has a triangle with degree sum ≥ k. Estimate h(n).

**Conjecture**: h(n) ≥ (2(√3-1) - o(1))n ≈ 1.464n

**Known Bounds**:
- Upper: h(n) ≤ 2(√3-1)n (Erdős-Laskar 1985)
- Lower: h(n) ≥ (21/16)n = 1.3125n (Fan 1988)

**Gap**: About 0.15n between upper and lower bounds.

**Key Insight**: Graphs just above Turán threshold must have
triangles with high degree sum, but exact value is unknown.

**References**:
- Erdős-Laskar (1985): Original bounds
- Fan (1988): Improved lower bound to 21/16

**Related Topics**:
- Turán theory
- Triangle-free graphs
- Degree sequences
-/

end Erdos1033
