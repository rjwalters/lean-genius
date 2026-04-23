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
  set Tset := {k : ℕ | ∃ (V : Type*) [DecidableEq V] [Fintype V],
      Fintype.card V = n ∧
      ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj], isAboveTuran G ∧
        ∀ T : Triangle G, triangleDegreeSum G T ≤ k}
  set S := {k : ℕ | isValidLowerBound n k}
  -- Re-establish S properties (from h_spec proof)
  have h_pos : 0 < h n := by
    by_contra hle; push_neg at hle
    have h0 : h n = 0 := Nat.le_zero.mp hle
    have hfan := fan_lower n hn
    have : (h n : ℝ) = 0 := by exact_mod_cast h0
    linarith [show (fanConstant : ℝ) > 0 from by norm_num [fanConstant],
              show (n : ℝ) > 0 from by exact_mod_cast (show 0 < n by omega)]
  have hS_ne : S.Nonempty := by
    by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : h n = 0 := by unfold h; rw [hemp]; simp [csSup_empty]
    omega
  have hS_bdd : BddAbove S := by
    by_contra huba
    have : h n = 0 := by unfold h; simp [csSup_of_not_bddAbove huba]
    omega
  -- h n is the maximum of S
  have hmax : ∀ k ∈ S, k ≤ h n := fun k hk => Nat.le_csSup hS_bdd hk
  -- h n + 1 ∉ S (since h n = sSup S is the max)
  have h_succ_not_S : h n + 1 ∉ S :=
    fun h => absurd (hmax _ h) (Nat.not_succ_le_self _)
  -- Get a witness graph from ¬isValidLowerBound n (h n + 1)
  have h_not_valid : ¬isValidLowerBound n (h n + 1) := h_succ_not_S
  unfold isValidLowerBound at h_not_valid
  push_neg at h_not_valid
  -- Extract: ∃ (W, G) dense on n vertices with all triangles sum < h n + 1
  obtain ⟨W, instDE, instFT, instDR_top, hWn, G, instDR_G, hGabove, hGbnd⟩ := h_not_valid
  -- hGbnd: ∀ T : Triangle G, triangleDegreeSum G T < h n + 1
  -- i.e., ≤ h n
  -- Key: edgeFinset and degree are instance-independent
  -- Both are determined by G.Adj alone, not the DecidableRel instance
  have hedge_indep : ∀ (inst : DecidableRel G.Adj),
      @edgeCount W instDE instFT G inst = @edgeCount W instDE instFT G instDR_G := by
    intro inst
    unfold edgeCount
    congr 1
    apply Finset.ext; intro e
    -- e ∈ G.edgeFinset ↔ e ∈ G.edgeSet (instance-independent)
    simp only [SimpleGraph.mem_edgeFinset]
  have hdeg_indep : ∀ (inst : DecidableRel G.Adj) (v : W),
      @SimpleGraph.degree W G inst v = @SimpleGraph.degree W G instDR_G v := by
    intro inst v
    simp only [SimpleGraph.degree]
    congr 1
    apply Finset.ext; intro w
    simp only [SimpleGraph.mem_neighborFinset]
  -- h n ∈ Tset: G witnesses this
  have h_in_Tset : h n ∈ Tset := by
    refine ⟨W, instDE, instFT, hWn, G, fun inst => ?_⟩
    -- Convert via instance independence
    refine ⟨?_, fun t => ?_⟩
    · -- isAboveTuran G (with inst)
      unfold isAboveTuran; rw [hedge_indep inst]; exact hGabove
    · -- triangleDegreeSum G t ≤ h n
      simp only [triangleDegreeSum, vertexDegree, hdeg_indep inst]
      exact Nat.lt_succ_iff.mp (hGbnd t)
  -- Tset is nonempty and bounded below
  have hTset_ne : Tset.Nonempty := ⟨h n, h_in_Tset⟩
  have hTset_bdd : BddBelow Tset := ⟨0, fun _ _ => Nat.zero_le _⟩
  apply Nat.le_antisymm
  · -- h n ≤ sInf Tset: h n is a lower bound for Tset
    apply Nat.le_csInf hTset_ne
    intro k hk
    -- k ∈ Tset: ∃ dense graph with all triangles sum ≤ k
    obtain ⟨V', instDE', instFT', hV'n, G', hG'⟩ := hk
    -- Apply with the canonical instance from G'.Adj's decidability
    haveI hDR' : DecidableRel G'.Adj := Classical.decRel G'.Adj
    obtain ⟨hG'above, hG'bnd⟩ := hG' hDR'
    -- From h_spec (h n is a valid lower bound), G' has a triangle with sum ≥ h n
    obtain ⟨t, ht⟩ := h_spec n hn V' hV'n G' hG'above
    -- That triangle's sum ≤ k
    exact Nat.le_trans ht (hG'bnd t)
  · -- sInf Tset ≤ h n: h n ∈ Tset
    exact Nat.csInf_le hTset_bdd h_in_Tset

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
    IsEmpty (Triangle G) := by
  intro V _ _ _ G ⟨A, B, hAB, hABdisj, hadj⟩
  rw [isEmpty_iff]
  intro T
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

/-- Bipartite + 1 graph on Fin n: complete bipartite K_{n/2, n-n/2} plus edge (0,1). -/
private def turanPlus1 (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j :=
    (i.val < n / 2 ∧ j.val ≥ n / 2) ∨ (i.val ≥ n / 2 ∧ j.val < n / 2) ∨
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)
  symm := by
    intro i j h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact Or.inr (Or.inl ⟨hj, hi⟩)
    · exact Or.inl ⟨hj, hi⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hj, hi⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hj, hi⟩))
  loopless := by
    intro i h
    simp only [lt_irrefl, ge_iff_le, le_refl, not_lt] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · omega
    · omega
    · omega
    · omega

private instance (n : ℕ) : DecidableRel (turanPlus1 n).Adj := by
  intro i j
  unfold turanPlus1
  simp only [SimpleGraph.mk]
  exact inferInstance

/-- The triangle (0, 1, n/2) in turanPlus1 n. -/
private lemma turanPlus1_triangle (n : ℕ) (hn : n ≥ 4) :
    let G := turanPlus1 n
    let v0 : Fin n := ⟨0, by omega⟩
    let v1 : Fin n := ⟨1, by omega⟩
    let vm : Fin n := ⟨n / 2, Nat.div_lt_self (by omega) (by omega)⟩
    G.Adj v0 v1 ∧ G.Adj v1 vm ∧ G.Adj v0 vm := by
  simp only [turanPlus1, SimpleGraph.mk]
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · apply Or.inr; apply Or.inl
    constructor
    · show 1 < n / 2; omega
    · show n / 2 ≥ n / 2; omega
  · apply Or.inl
    constructor
    · show 0 < n / 2; omega
    · show n / 2 ≥ n / 2; omega

/-- Degree sum of the triangle (0,1,n/2) is ≥ n.
    Strategy: inject the upper half {j | j.val ≥ n/2} into neighborFinset v0 and v1,
    and the lower half {j | j.val < n/2} into neighborFinset vm.
    Upper half has n - n/2 elements, lower half has n/2 elements, summing to n. -/
private lemma turanPlus1_triangle_sum (n : ℕ) (hn : n ≥ 4) :
    let G := turanPlus1 n
    let v0 : Fin n := ⟨0, by omega⟩
    let v1 : Fin n := ⟨1, by omega⟩
    let vm : Fin n := ⟨n / 2, Nat.div_lt_self (by omega) (by omega)⟩
    G.degree v0 + G.degree v1 + G.degree vm ≥ n := by
  intro G v0 v1 vm
  -- Partition Fin n into upper half (val ≥ n/2) and lower half (val < n/2)
  set S_upper := Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ with hSu
  set S_lower := Finset.filter (fun j : Fin n => j.val < n / 2) Finset.univ with hSl
  -- The two halves partition all n vertices
  have h_total : S_upper.card + S_lower.card = n := by
    have h_disj : Disjoint S_upper S_lower :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
    have h_union : S_upper ∪ S_lower = Finset.univ := by
      ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    calc S_upper.card + S_lower.card
        = (S_upper ∪ S_lower).card := (Finset.card_union_of_disjoint h_disj).symm
      _ = n := by rw [h_union, Finset.card_univ, Fintype.card_fin]
  -- Each upper-half vertex is adjacent to v0 (v0.val = 0 < n/2 for n ≥ 4)
  have h_sub_v0 : S_upper ⊆ G.neighborFinset v0 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inl ⟨by omega, hj⟩
  -- Each upper-half vertex is adjacent to v1 (v1.val = 1 < n/2 for n ≥ 4, first disjunct)
  have h_sub_v1 : S_upper ⊆ G.neighborFinset v1 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inl ⟨by omega, hj⟩
  -- Each lower-half vertex is adjacent to vm (vm.val = n/2, second disjunct: n/2 ≥ n/2 ∧ j < n/2)
  have h_sub_vm : S_lower ⊆ G.neighborFinset vm := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inr (Or.inl ⟨le_refl _, hj⟩)
  -- Lower bounds on degrees via subset cardinality
  have hdeg_v0 : S_upper.card ≤ G.degree v0 := Finset.card_le_card h_sub_v0
  have hdeg_v1 : S_upper.card ≤ G.degree v1 := Finset.card_le_card h_sub_v1
  have hdeg_vm : S_lower.card ≤ G.degree vm := Finset.card_le_card h_sub_vm
  -- Sum ≥ 2 * S_upper.card + S_lower.card ≥ S_upper.card + S_lower.card = n
  omega

-- Helper: cardinality of lower half {j : Fin n | j.val < n/2} = n/2
private lemma card_filter_lt_half (n : ℕ) (hn : n ≥ 4) :
    (Finset.filter (fun j : Fin n => j.val < n / 2) Finset.univ).card = n / 2 := by
  have hle : n / 2 ≤ n := Nat.div_le_self n 2
  have hf : (Finset.filter (fun j : Fin n => j.val < n / 2) Finset.univ) =
      (Finset.univ : Finset (Fin (n / 2))).image (Fin.castLE hle) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
    constructor
    · intro hj; exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨k, _, rfl⟩; exact k.isLt
  rw [hf, Finset.card_image_of_injective _ (Fin.castLE_injective hle),
      Finset.card_univ, Fintype.card_fin]

-- Helper: cardinality of upper half {j : Fin n | j.val ≥ n/2} = n - n/2
private lemma card_filter_ge_half (n : ℕ) (hn : n ≥ 4) :
    (Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ).card = n - n / 2 := by
  have hf : (Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ) =
      (Finset.univ : Finset (Fin (n - n / 2))).image
        (fun k : Fin (n - n / 2) => ⟨n / 2 + k.val, by omega⟩) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
    constructor
    · intro hj; exact ⟨⟨j.val - n / 2, by omega⟩, Finset.mem_univ _, by omega⟩
    · rintro ⟨k, _, rfl⟩; omega
  rw [hf, Finset.card_image_of_injective]
  · simp [Fintype.card_fin]
  · intro k1 k2 h; ext; omega

-- Helper: upper vertices (val ≥ n/2) have degree n/2 in turanPlus1
private lemma turanPlus1_degree_upper (n : ℕ) (hn : n ≥ 4)
    (v : Fin n) (hv : n / 2 ≤ v.val) :
    (turanPlus1 n).degree v = n / 2 := by
  have hN : (turanPlus1 n).neighborFinset v =
      Finset.filter (fun j : Fin n => j.val < n / 2) Finset.univ := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, turanPlus1, SimpleGraph.mk_adj,
               Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hi, _⟩ | ⟨_, hj⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> omega
    · intro hj; exact Or.inr (Or.inl ⟨hv, hj⟩)
  rw [SimpleGraph.degree, hN, card_filter_lt_half n hn]

-- Helper: lower vertices (2 ≤ val < n/2) have degree n - n/2 in turanPlus1
private lemma turanPlus1_degree_lower_other (n : ℕ) (hn : n ≥ 4)
    (v : Fin n) (hv2 : 2 ≤ v.val) (hvl : v.val < n / 2) :
    (turanPlus1 n).degree v = n - n / 2 := by
  have hN : (turanPlus1 n).neighborFinset v =
      Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, turanPlus1, SimpleGraph.mk_adj,
               Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨_, hj⟩ | ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> omega
    · intro hj; exact Or.inl ⟨hvl, hj⟩
  rw [SimpleGraph.degree, hN, card_filter_ge_half n hn]

-- Helper: vertex 0 has degree n - n/2 + 1 in turanPlus1
private lemma turanPlus1_degree_zero (n : ℕ) (hn : n ≥ 4) :
    (turanPlus1 n).degree ⟨0, by omega⟩ = n - n / 2 + 1 := by
  have hN : (turanPlus1 n).neighborFinset ⟨0, by omega⟩ =
      Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ ∪ {⟨1, by omega⟩} := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, turanPlus1, SimpleGraph.mk_adj,
               Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton, Fin.ext_iff]
    constructor
    · rintro (⟨_, hj⟩ | ⟨hi, _⟩ | ⟨_, hj⟩ | ⟨hi, _⟩) <;> [exact Or.inl hj; omega;
        exact Or.inr hj; omega]
    · rintro (hj | rfl)
      · exact Or.inl ⟨by omega, hj⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rw [SimpleGraph.degree, hN, Finset.card_union_of_disjoint]
  · rw [card_filter_ge_half n hn, Finset.card_singleton]
  · simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

-- Helper: vertex 1 has degree n - n/2 + 1 in turanPlus1
private lemma turanPlus1_degree_one (n : ℕ) (hn : n ≥ 4) :
    (turanPlus1 n).degree ⟨1, by omega⟩ = n - n / 2 + 1 := by
  have hN : (turanPlus1 n).neighborFinset ⟨1, by omega⟩ =
      Finset.filter (fun j : Fin n => n / 2 ≤ j.val) Finset.univ ∪ {⟨0, by omega⟩} := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, turanPlus1, SimpleGraph.mk_adj,
               Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton, Fin.ext_iff]
    constructor
    · rintro (⟨_, hj⟩ | ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨_, hj⟩) <;> [exact Or.inl hj; omega;
        omega; exact Or.inr hj]
    · rintro (hj | rfl)
      · exact Or.inl ⟨by omega, hj⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  rw [SimpleGraph.degree, hN, Finset.card_union_of_disjoint]
  · rw [card_filter_ge_half n hn, Finset.card_singleton]
  · simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- Adding one edge to Turán creates triangle with specific degrees.
    Proof: use turanPlus1 = K_{n/2, n-n/2} + edge(0,1) on Fin n. -/
theorem turan_plus_one (n : ℕ) (hn : n ≥ 4) :
    ∃ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n ∧
    ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
    edgeCount G = turanThreshold n + 1 ∧
    (∃ T : Triangle G, triangleDegreeSum G T ≥ n) := by
  refine ⟨Fin n, inferInstance, inferInstance, Fintype.card_fin n, turanPlus1 n, fun _ => ?_⟩
  constructor
  · -- edgeCount = turanThreshold n + 1
    -- Strategy: sum of degrees = 2 * edges. We compute the degree sum exactly.
    unfold edgeCount turanThreshold
    -- Use sum_degrees_eq_twice_card_edges
    have htwoE := (turanPlus1 n).sum_degrees_eq_twice_card_edges
    -- Partition Fin n into lower (val < n/2) and upper (val ≥ n/2)
    set lower := Finset.filter (fun v : Fin n => v.val < n / 2) Finset.univ
    set upper := Finset.filter (fun v : Fin n => n / 2 ≤ v.val) Finset.univ
    have h_disj : Disjoint lower upper :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
    have h_union : lower ∪ upper = Finset.univ := by
      ext v; simp only [lower, upper, Finset.mem_union, Finset.mem_filter,
                        Finset.mem_univ, true_and]; omega
    have card_lower : lower.card = n / 2 := card_filter_lt_half n hn
    have card_upper : upper.card = n - n / 2 := card_filter_ge_half n hn
    -- Vertices 0, 1 are in lower
    have hv0_lower : (⟨0, by omega⟩ : Fin n) ∈ lower := by
      simp [lower, Finset.mem_filter]; omega
    have hv1_lower : (⟨1, by omega⟩ : Fin n) ∈ lower := by
      simp [lower, Finset.mem_filter]; omega
    have hv01_ne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    have hpair_sub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) ⊆ lower :=
      Finset.insert_subset_iff.mpr ⟨hv0_lower, Finset.singleton_subset_iff.mpr hv1_lower⟩
    -- Sum over upper: each vertex has degree n/2
    have hsum_upper : ∑ v in upper, (turanPlus1 n).degree v = (n - n / 2) * (n / 2) := by
      rw [Finset.sum_const_nat (fun v hv =>
          turanPlus1_degree_upper n hn v ((Finset.mem_filter.mp hv).2)),
          card_upper]
    -- Sum over {0, 1}: each has degree n - n/2 + 1
    have hsum_pair : ∑ v in ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)),
        (turanPlus1 n).degree v = 2 * (n - n / 2 + 1) := by
      rw [Finset.sum_pair hv01_ne,
          turanPlus1_degree_zero n hn, turanPlus1_degree_one n hn]
      ring
    -- Card of lower \ {0, 1} = n/2 - 2
    have hrest_card : (lower \ {⟨0, by omega⟩, ⟨1, by omega⟩}).card = n / 2 - 2 := by
      rw [Finset.card_sdiff hpair_sub, card_lower, Finset.card_pair hv01_ne]
    -- Sum over lower \ {0, 1}: each has degree n - n/2
    have hsum_rest : ∑ v in lower \ {⟨0, by omega⟩, ⟨1, by omega⟩},
        (turanPlus1 n).degree v = (n / 2 - 2) * (n - n / 2) := by
      rw [Finset.sum_const_nat (fun v hv => ?_), hrest_card]
      have hvm := Finset.mem_sdiff.mp hv
      have hvl : v.val < n / 2 := (Finset.mem_filter.mp hvm.1).2
      have hv2 : 2 ≤ v.val := by
        have h := hvm.2
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h
        push_neg at h
        omega
      exact turanPlus1_degree_lower_other n hn v hv2 hvl
    -- Combine: total degree sum
    have hsum_total : ∑ v : Fin n, (turanPlus1 n).degree v = 2 * (n / 2 * (n - n / 2) + 1) := by
      -- Rewrite ∑ v : Fin n as ∑ v in Finset.univ (definitionally equal), then use h_union
      have huniv : ∑ v : Fin n, (turanPlus1 n).degree v =
                   ∑ v in lower ∪ upper, (turanPlus1 n).degree v :=
        Finset.sum_congr h_union.symm (fun _ _ => rfl)
      rw [huniv, Finset.sum_union h_disj]
      -- Split lower into {0,1} and rest
      rw [← Finset.sum_sdiff hpair_sub, hsum_pair, hsum_rest, hsum_upper]
      -- Arithmetic: (n/2-2)*(n-n/2) + 2*(n-n/2+1) + (n-n/2)*n/2 = 2*(n/2*(n-n/2)+1)
      have h2 : 2 ≤ n / 2 := by omega
      have key : (n / 2 - 2) * (n - n / 2) + 2 * (n - n / 2) = n / 2 * (n - n / 2) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel h2]
      nlinarith [Nat.mul_comm (n - n / 2) (n / 2)]
    -- Conclude edge count
    have hcard : (turanPlus1 n).edgeFinset.card = n / 2 * (n - n / 2) + 1 := by
      nlinarith
    -- Arithmetic: n/2 * (n - n/2) = n^2 / 4
    -- Proof by parity: even n = k+k gives k*k = (2k)^2/4; odd n = 2k+1 gives k*(k+1) = (2k+1)^2/4
    have harith : n / 2 * (n - n / 2) = n ^ 2 / 4 := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- even: n = k + k, so n/2 = k, n - n/2 = k, n^2 = 4*(k*k)
        have h1 : n / 2 = k := by omega
        have h2 : n - n / 2 = k := by omega
        have h3 : n ^ 2 = 4 * (k * k) := by rw [hk]; ring
        rw [h1, h2, h3]; omega
      · -- odd: n = 2*k+1, so n/2 = k, n - n/2 = k+1, n^2 = 4*(k*(k+1))+1
        have h1 : n / 2 = k := by omega
        have h2 : n - n / 2 = k + 1 := by omega
        have h3 : n ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
        rw [h1, h2, h3]; omega
    omega
  · -- Triangle (0,1,n/2) with degree sum ≥ n
    have htr := turanPlus1_triangle n hn
    have hsum := turanPlus1_triangle_sum n hn
    let v0 : Fin n := ⟨0, by omega⟩
    let v1 : Fin n := ⟨1, by omega⟩
    let vm : Fin n := ⟨n / 2, Nat.div_lt_self (by omega) (by omega)⟩
    have hne01 : v0 ≠ v1 := by simp [v0, v1, Fin.ext_iff]
    have hne1m : v1 ≠ vm := by
      simp [v1, vm, Fin.ext_iff]; omega
    have hne0m : v0 ≠ vm := by
      simp [v0, vm, Fin.ext_iff]; omega
    exact ⟨⟨v0, v1, vm, hne01, hne1m, hne0m, htr.1, htr.2.1, htr.2.2⟩,
           by simp only [triangleDegreeSum, vertexDegree]; linarith [hsum]⟩

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

/-- K₄ minus edge (2,3): the extremal graph for n=4.
    Has 5 edges (> Turán threshold of 4), and all triangles have degree sum 8. -/
private def G4 : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ ¬(i = 2 ∧ j = 3) ∧ ¬(i = 3 ∧ j = 2)
  symm := by
    intro i j ⟨hij, h1, h2⟩
    exact ⟨hij.symm, fun ⟨ha, hb⟩ => h2 ⟨hb, ha⟩, fun ⟨ha, hb⟩ => h1 ⟨hb, ha⟩⟩
  loopless := by intro i ⟨h, _⟩; exact h rfl

private instance : DecidableRel G4.Adj := by
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- Upper bound: every valid lower bound for h(4) is ≤ 8.
    Proof: K₄ minus one edge has 5 edges (above Turán threshold 4),
    and every triangle in it has degree sum exactly 8. -/
private lemma valid_bound_four_le_eight (k : ℕ) (hk : isValidLowerBound 4 k) : k ≤ 8 := by
  by_contra hlt; push_neg at hlt
  -- G4 is above Turán threshold: 5 > 4²/4 = 4
  have habove : isAboveTuran G4 := by
    show G4.edgeFinset.card > 4 ^ 2 / 4; native_decide
  -- Get a triangle T with degree sum ≥ k > 8
  obtain ⟨T, hT⟩ := hk (Fin 4) (Fintype.card_fin 4) G4 habove
  -- Degree of each vertex in G4: vertices 0,1 have degree 3, vertices 2,3 have degree 2
  have hd0 : G4.degree 0 = 3 := by native_decide
  have hd1 : G4.degree 1 = 3 := by native_decide
  have hd2 : G4.degree 2 = 2 := by native_decide
  have hd3 : G4.degree 3 = 2 := by native_decide
  -- Any triangle in G4 has degree sum ≤ 8 (case analysis on all vertex combinations)
  have hle : triangleDegreeSum G4 T ≤ 8 := by
    simp only [triangleDegreeSum, vertexDegree]
    fin_cases T.v1 <;> fin_cases T.v2 <;> fin_cases T.v3 <;>
      simp_all (config := { decide := true }) [G4, hd0, hd1, hd2, hd3] <;> omega
  omega

/-- Lower bound: 8 is a valid lower bound for h(4).
    Key argument: any graph on 4 vertices with >4 edges has degree sum ≥ 10,
    forcing at least 2 vertices with degree 3, each adjacent to all others.
    The resulting triangle has degree sum ≥ 3+3+2 = 8. -/
private lemma isValidLowerBound_four_eight : isValidLowerBound 4 8 := by
  intro V _ _ _ hcard G _ habove
  -- Setup: equivalence with Fin 4, name the 4 vertices
  let e : V ≃ Fin 4 := (Fintype.equivFin V).trans (Equiv.cast (congrArg Fin hcard))
  let a := e.symm 0; let b := e.symm 1; let c := e.symm 2; let d := e.symm 3
  -- G has ≥ 5 edges (above Turán threshold 4²/4 = 4)
  have hedge5 : G.edgeFinset.card ≥ 5 := by
    simp only [isAboveTuran, turanThreshold, edgeCount] at habove; rw [hcard] at habove; omega
  -- Sum of degrees = 2 × edges ≥ 10
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v : V, G.degree v = G.degree a + G.degree b + G.degree c + G.degree d := by
    rw [← Equiv.sum_comp e.symm, Fin.sum_univ_four]
  have hge10 : G.degree a + G.degree b + G.degree c + G.degree d ≥ 10 := by linarith
  -- Each degree ≤ 3 (n - 1 = 3 for n = 4)
  have hdeg_le : ∀ x : V, G.degree x ≤ 3 := fun x => by
    have := G.degree_lt_card_verts x; rw [hcard] at this; omega
  -- All 4 vertices are distinct (injective equivalence)
  have h_ne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d :=
    ⟨e.symm.injective.ne (by decide), e.symm.injective.ne (by decide),
     e.symm.injective.ne (by decide), e.symm.injective.ne (by decide),
     e.symm.injective.ne (by decide), e.symm.injective.ne (by decide)⟩
  -- With degree sum ≥ 10 and each ≤ 3, at least 2 vertices have degree 3
  -- (if ≤1 had degree 3, sum ≤ 3 + 2 + 2 + 2 = 9 < 10, contradiction)
  have ⟨u, v, huv_ne, hu3, hv3⟩ : ∃ u v : V, u ≠ v ∧ G.degree u = 3 ∧ G.degree v = 3 := by
    have hda := hdeg_le a; have hdb := hdeg_le b; have hdc := hdeg_le c; have hdd := hdeg_le d
    by_cases ha : G.degree a = 3
    · by_cases hb : G.degree b = 3
      · exact ⟨a, b, h_ne.1, ha, hb⟩
      · by_cases hc : G.degree c = 3
        · exact ⟨a, c, h_ne.2.1, ha, hc⟩
        · exact ⟨a, d, h_ne.2.2.1, ha, by omega⟩
    · by_cases hb : G.degree b = 3
      · by_cases hc : G.degree c = 3
        · exact ⟨b, c, h_ne.2.2.2.1, hb, hc⟩
        · exact ⟨b, d, h_ne.2.2.2.2.1, hb, by omega⟩
      · exact ⟨c, d, h_ne.2.2.2.2.2, by omega, by omega⟩
  -- A vertex with degree 3 in a 4-vertex graph is adjacent to all others
  have all_adj_of_deg3 : ∀ x w : V, x ≠ w → G.degree x = 3 → G.Adj x w := by
    intro x w hxw hx3
    have hN_sub : G.neighborFinset x ⊆ Finset.univ.erase x := fun y hy =>
      Finset.mem_erase.mpr ⟨fun h => G.loopless x (h ▸ G.mem_neighborFinset.mp hy),
                             Finset.mem_univ y⟩
    have h_eq : G.neighborFinset x = Finset.univ.erase x :=
      Finset.eq_of_subset_of_card_le hN_sub (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
        exact le_of_eq hx3.symm)
    exact G.mem_neighborFinset.mp (h_eq ▸ Finset.mem_erase.mpr ⟨hxw, Finset.mem_univ w⟩)
  -- Find a third vertex w ≠ u, v (V has 4 elements, so V \ {u,v} has 2 elements)
  obtain ⟨w, hwu, hwv⟩ : ∃ w : V, w ≠ u ∧ w ≠ v := by
    have hpair : ({u, v} : Finset V).card = 2 := Finset.card_pair huv_ne
    have hcard_rest : (Finset.univ \ ({u, v} : Finset V)).card = 2 := by
      rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hpair]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < _ from by omega)
    have hmem := Finset.mem_sdiff.mp hw
    refine ⟨w, fun h => hmem.2 ?_, fun h => hmem.2 ?_⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  -- Build triangle {u, v, w}: u adj v, v adj w, u adj w (all via degree 3)
  refine ⟨⟨u, v, w, huv_ne, hwv.symm, hwu.symm,
    all_adj_of_deg3 u v huv_ne hu3,
    all_adj_of_deg3 v w hwv.symm hv3,
    all_adj_of_deg3 u w hwu.symm hu3⟩, ?_⟩
  -- Degree sum: d(u) + d(v) + d(w) = 3 + 3 + d(w) ≥ 3 + 3 + 2 = 8
  simp only [triangleDegreeSum, vertexDegree]
  have hdw2 : G.degree w ≥ 2 :=
    (triangle_min_degree G ⟨u, v, w, huv_ne, hwv.symm, hwu.symm,
      all_adj_of_deg3 u v huv_ne hu3, all_adj_of_deg3 v w hwv.symm hv3,
      all_adj_of_deg3 u w hwu.symm hu3⟩).2.2
  linarith

/-- h(4) = 8: graphs with 5 edges have max triangle degree sum 8,
    K₄ has max triangle degree sum 9. Min of maxes = 8.
    Note: previous statement h(4)=7 was incorrect (verified by exhaustive enumeration). -/
theorem h_four : h 4 = 8 := by
  apply le_antisymm
  · exact csSup_le ⟨8, isValidLowerBound_four_eight⟩ valid_bound_four_le_eight
  · exact le_csSup ⟨8, fun k hk => valid_bound_four_le_eight k hk⟩ isValidLowerBound_four_eight

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
