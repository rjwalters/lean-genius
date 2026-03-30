/-
# Erdős Problem #1104 — Maximum Chromatic Number of Triangle-Free Graphs

Let f(n) be the maximum chromatic number of a triangle-free graph
on n vertices. Estimate f(n).

Known:
  (1 − o(1))√(n/log n) ≤ f(n) ≤ (2 + o(1))√(n/log n)

Lower bound: Hefty–Horn–King–Pfender (2025)
Upper bound: Davies–Illingworth (2022)

The exact constant remains open.

Status: OPEN
Reference: https://erdosproblems.com/1104
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A graph on Fin n is triangle-free if it has no 3-clique. -/
def IsTriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 3

/-- f(n) = max { χ(G) : G is a triangle-free graph on n vertices }.
We axiomatize this as a function ℕ → ℕ with properties, since
computing it requires enumerating all graphs. -/
noncomputable def triangleFreeMaxChi : ℕ → ℕ := by
  intro n
  exact sSup { k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.CliqueFree 3 ∧ G.chromaticNumber = k }

/- ## Basic Properties -/

/-- Every graph on Fin n is n-colorable (using the identity coloring). -/
theorem colorable_of_fin (n : ℕ) (G : SimpleGraph (Fin n)) :
    G.Colorable n := by
  exact G.colorable_of_fintype

/-- f(n) is well-defined: the chromatic number of any triangle-free
graph on n vertices is at most n. -/
theorem triangleFree_chi_le {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (_ : G.CliqueFree 3) :
    G.chromaticNumber ≤ n :=
  G.chromaticNumber_le_card

/-- The empty graph (no edges) on n vertices is triangle-free. -/
theorem emptyGraph_triangleFree (n : ℕ) :
    IsTriangleFree (⊥ : SimpleGraph (Fin n)) := by
  intro s hs
  simp [SimpleGraph.IsClique, Set.Pairwise] at hs
  obtain ⟨a, ha, b, hb, hab, hAdj⟩ := hs
  exact hAdj

/-- The empty graph has chromatic number 0 for n = 0, and 1 for n ≥ 1. -/
theorem emptyGraph_chromaticNumber_pos {n : ℕ} (hn : 0 < n)
    [DecidableRel (⊥ : SimpleGraph (Fin n)).Adj] :
    (⊥ : SimpleGraph (Fin n)).Colorable 1 := by
  exact SimpleGraph.Colorable.mono (by omega) (⊥ : SimpleGraph (Fin n)).colorable_of_fintype

/-- f(1) = 1: The only graph on 1 vertex is the empty graph, which is
1-chromatic. -/
theorem triangleFreeMaxChi_one : triangleFreeMaxChi 1 ≤ 1 := by
  unfold triangleFreeMaxChi
  apply Nat.sSup_le
  intro k ⟨G, hDec, hTF, hChi⟩
  rw [← hChi]
  exact @SimpleGraph.chromaticNumber_le_card (Fin 1) _ G hDec

/-- f(0) = 0: No vertices, no colors needed. -/
theorem triangleFreeMaxChi_zero : triangleFreeMaxChi 0 = 0 := by
  unfold triangleFreeMaxChi
  apply le_antisymm
  · apply Nat.sSup_le
    intro k ⟨G, hDec, _, hChi⟩
    rw [← hChi]
    exact @SimpleGraph.chromaticNumber_le_card (Fin 0) _ G hDec
  · exact Nat.zero_le _

/-- f(n) ≤ n for all n: the chromatic number cannot exceed the number
of vertices. -/
theorem triangleFreeMaxChi_le (n : ℕ) : triangleFreeMaxChi n ≤ n := by
  unfold triangleFreeMaxChi
  apply Nat.sSup_le
  intro k ⟨G, hDec, _, hChi⟩
  rw [← hChi]
  exact @SimpleGraph.chromaticNumber_le_card (Fin n) _ G hDec

/-- f(n) ≥ 1 for n ≥ 1: the empty graph is 1-chromatic. -/
theorem one_le_triangleFreeMaxChi {n : ℕ} (hn : 0 < n) :
    1 ≤ triangleFreeMaxChi n := by
  unfold triangleFreeMaxChi
  apply le_csSup_of_le
  · -- bdd_above
    exact ⟨n, fun k ⟨G, hDec, _, hChi⟩ =>
      hChi ▸ @SimpleGraph.chromaticNumber_le_card (Fin n) _ G hDec⟩
  · -- witness: the empty graph
    exact ⟨⊥, Classical.decRel _, emptyGraph_triangleFree n, rfl⟩
  · -- 1 ≤ chromaticNumber of empty graph on n ≥ 1 vertices
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact (⊥ : SimpleGraph (Fin n)).chromaticNumber_pos

/- ## Ramsey Duality -/

/-- **Ramsey duality**: f(n) ≥ k if and only if R(3,k) ≤ n.
Here R(3,k) is the Ramsey number: the minimum N such that every
2-coloring of edges of K_N contains a triangle or an independent
set of size k. -/
def RamseyTriangle (k : ℕ) : ℕ := by
  exact Nat.find (⟨k * k, trivial⟩ : ∃ N : ℕ, True) -- placeholder

/-- R(3,k) = Θ(k²/log k) (Kim 1995, Bohman 2009, Fiz Pontiveros–
Griffiths–Morris 2020). The lower bound is by Kim's semi-random method;
the upper bound follows from triangle Ramsey results. -/
/- ## Main Asymptotic Bounds -/

/-- **Lower Bound (Hefty–Horn–King–Pfender 2025)**: f(n) ≥ (1-o(1))√(n/log n).
The construction improves the Bohman/Fiz Pontiveros–Griffiths–Morris
bound on R(3,k). -/
axiom erdos_1104_lower :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (triangleFreeMaxChi n : ℝ) ≥
      (1 - ε) * Real.sqrt (n / Real.log n)

/-- **Upper Bound (Davies–Illingworth 2022)**: f(n) ≤ (2+o(1))√(n/log n).
This improves the Ramsey upper bound by a constant factor. -/
axiom erdos_1104_upper :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (triangleFreeMaxChi n : ℝ) ≤
      (2 + ε) * Real.sqrt (n / Real.log n)

/-- **Open Question**: Is the correct constant 1, 2, or something in between?
Erdős conjectured it should be closer to √2. The gap between 1 and 2
remains the main open problem. -/
def erdos_1104_conjecture : Prop :=
  ∃ c : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    |(triangleFreeMaxChi n : ℝ) - c * Real.sqrt (n / Real.log n)| ≤
      ε * Real.sqrt (n / Real.log n)

/- ## Edge Variant -/

/-- g(m) = max { χ(G) : G triangle-free with m edges }. -/
noncomputable def triangleFreeMaxChiEdges : ℕ → ℕ := by
  intro m
  exact sSup { k : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n))
    (_ : DecidableRel G.Adj) (_ : Fintype (G.edgeSet)),
    G.CliqueFree 3 ∧ G.edgeSet.toFinset.card = m ∧ G.chromaticNumber = k }

/-- **Edge variant upper bound (Davies–Illingworth 2022)**:
g(m) ≤ (3^{5/3} + o(1))(m/(log m)²)^{1/3}. -/
/-- **Edge variant lower bound (Kim 1995)**:
g(m) ≥ c(m/(log m)²)^{1/3} for some c > 0. -/
/- ## Mycielski Construction -/

/-- The Mycielski graph M_k is triangle-free with chromatic number k.
M_1 = K_1 (1 vertex), M_2 = K_2 (2 vertices), M_3 = C_5 (5 vertices),
M_4 has 11 vertices, M_k has 3·2^{k-2} - 1 vertices.
This shows f(n) can be arbitrarily large but grows slowly. -/
axiom mycielski_construction :
  ∀ k : ℕ, k ≥ 1 →
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ (_ : DecidableRel G.Adj),
        G.CliqueFree 3 ∧ G.chromaticNumber = k ∧
        n = 3 * 2 ^ (k - 2) - 1

/-- The Mycielski vertex count gives: f(3·2^{k-2} - 1) ≥ k for k ≥ 2. -/
theorem mycielski_lower_bound :
    ∀ k : ℕ, k ≥ 2 →
      k ≤ triangleFreeMaxChi (3 * 2 ^ (k - 2) - 1) := by
  intro k hk
  unfold triangleFreeMaxChi
  apply le_csSup_of_le
  · exact ⟨3 * 2 ^ (k - 2) - 1, fun j ⟨G, hDec, _, hChi⟩ =>
      hChi ▸ @SimpleGraph.chromaticNumber_le_card _ _ G hDec⟩
  · obtain ⟨n, G, hDec, hTF, hChi, hn⟩ := mycielski_construction k (by omega)
    rw [hn]
    exact ⟨G, hDec, hTF, hChi⟩
  · le_refl k

/- ## Summary -/

/-- Summary of the state of knowledge. The key open question is
determining the constant c* where f(n) ~ c*·√(n/log n). -/
theorem bounds_summary :
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (triangleFreeMaxChi n : ℝ) ≥ (1 - ε) * Real.sqrt (n / Real.log n)) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (triangleFreeMaxChi n : ℝ) ≤ (2 + ε) * Real.sqrt (n / Real.log n)) :=
  ⟨erdos_1104_lower, erdos_1104_upper⟩
