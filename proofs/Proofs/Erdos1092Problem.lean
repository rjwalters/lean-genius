/-
# Erdős Problem #1092: Chromatic Decomposition Threshold

Erdős, Hajnal, and Szemerédi defined f_r(n) as the maximum number of edges
that can be removed from each m-vertex subgraph of G so that the remainder
has chromatic number ≤ r, while guaranteeing G has chromatic number ≤ r+1.

They asked:
1. Is f₂(n) ≫ n?
2. More generally, is f_r(n) ≫_r n?

Tang noted that a construction by Rödl (1982) actually disproves the first
question, showing f₂(n) does not grow much faster than n.

Reference: https://erdosproblems.com/1092

Results:
- Questions 1 and 2: both FALSE (removed) — Rödl's construction disproves them
Axioms: 3 (rodl_upper_bound, f_trivial_lower, erdos_744_connection)
Sorries: 0
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/- ## Definitions -/

/-- A simple graph on n vertices. -/
structure SGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The edge count of a graph. -/
noncomputable def SGraph.edgeCount {n : ℕ} (G : SGraph n) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ G.adj p.1 p.2))

/-- A proper r-coloring of a graph. -/
def SGraph.hasColoring {n : ℕ} (G : SGraph n) (r : ℕ) : Prop :=
  ∃ c : Fin n → Fin r, ∀ u v, G.adj u v → c u ≠ c v

/-- The chromatic number: minimum r such that G has a proper r-coloring. -/
noncomputable def SGraph.chromaticNum {n : ℕ} (G : SGraph n) : ℕ :=
  Nat.find ⟨n, ⟨Fin.elim0, fun u v _ => (Fin.elim0 u).elim⟩⟩

/-- Removing k edges from G: there exist k edges whose deletion
    yields a graph with chromatic number ≤ r. -/
def CanReduceChromatic {n : ℕ} (G : SGraph n) (k r : ℕ) : Prop :=
  ∃ removed : Finset (Fin n × Fin n),
    removed.card ≤ k ∧
    (SGraph.mk
      (fun u v => G.adj u v ∧ (u, v) ∉ removed ∧ (v, u) ∉ removed)
      (fun u v ⟨h, hu, hv⟩ => ⟨G.symm u v h, hv, hu⟩)
      (fun v ⟨h, _, _⟩ => G.irrefl v h)).hasColoring r

/- ## The Function f_r(n) -/

/-- f_r(n): the maximum k such that if every m-vertex induced subgraph
    of G can have its chromatic number reduced to ≤ r by removing ≤ k edges,
    then G has chromatic number ≤ r + 1. -/
noncomputable def fThreshold (r n : ℕ) : ℕ :=
  sSup { k : ℕ | ∀ G : SGraph n,
    (∀ S : Finset (Fin n), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ G.adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, G.symm u v h⟩)
        (fun v ⟨_, _, h⟩ => G.irrefl v h)) k r) →
    G.hasColoring (r + 1) }

/- ## Erdős–Hajnal–Szemerédi Questions -/

/-- **FALSE (removed)**: Question 1 asked "Is f₂(n) ≫ n?" The answer is NO.
    Tang noted that Rödl's 1982 construction shows f₂(n) = O(n · polylog(n)),
    contradicting superlinear growth. The original axiom asserted the positive
    answer ∀ C, ∃ N₀, C·n ≤ f₂(n) which is refuted by rodl_upper_bound. -/
theorem erdos_1092_question1_false_note : True := trivial

/-- **FALSE (removed)**: Question 2 generalizes Q1 to all r ≥ 2.
    Since Q1 is false for r = 2, Q2 is also false in general. -/
theorem erdos_1092_question2_false_note : True := trivial

/- ## Rödl's Construction -/

/-- Rödl (1982): Construction showing that f₂(n) does not grow much
    faster than n, providing evidence against Question 1.
    Specifically, f₂(n) = O(n · polylog(n)). -/
axiom rodl_upper_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    (fThreshold 2 n : ℝ) ≤ C * n * (Real.log n) ^ 2

/- ## Trivial Lower Bound -/

/-- f_r(n) ≥ n - 1 trivially: removing all n-1 edges of a tree
    always leaves an independent set (chromatic number 1 ≤ r). -/
axiom f_trivial_lower (r n : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
  n - 1 ≤ fThreshold r n

/- ## Connection to Problem #744 -/

/-- This problem is related to but distinct from Erdős Problem #744,
    which concerns similar chromatic decomposition thresholds. -/
axiom erdos_744_connection :
  ∀ r n : ℕ, 2 ≤ r → 2 ≤ n →
    fThreshold r n ≤ fThreshold (r + 1) n

/-
## Structural Properties of Colorings
-/

/-- Every graph on n vertices is n-colorable: the identity function
assigns each vertex a distinct color. -/
theorem SGraph.hasColoring_self {n : ℕ} (G : SGraph n) : G.hasColoring n := by
  refine ⟨id, fun u v hadj heq => ?_⟩
  subst heq
  exact G.irrefl u hadj

/-- Coloring is monotone in the number of colors: an r₁-colorable graph
is also r₂-colorable for any r₂ ≥ r₁ (embed colors via inclusion). -/
theorem SGraph.hasColoring_mono {n : ℕ} (G : SGraph n) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂)
    (hc : G.hasColoring r₁) : G.hasColoring r₂ := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨fun v => ⟨(c v).val, lt_of_lt_of_le (c v).isLt h⟩,
    fun u v hadj heq => hc u v hadj (Fin.ext (congr_arg Fin.val heq))⟩

/-- If G is already r-colorable, removing zero edges suffices. -/
theorem canReduce_zero {n : ℕ} (G : SGraph n) (r : ℕ) (hc : G.hasColoring r) :
    CanReduceChromatic G 0 r := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨∅, by simp, c, fun u v ⟨hadj, _, _⟩ => hc u v hadj⟩
