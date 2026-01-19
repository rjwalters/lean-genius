/-
  Erdős Problem #559: Size Ramsey Numbers for Bounded Degree Graphs

  Source: https://erdosproblems.com/559
  Status: DISPROVED (for d ≥ 3)

  Statement:
  Let R̂(G) denote the size Ramsey number: the minimal number of edges m
  such that there exists a graph H with m edges that is Ramsey for G.

  Conjecture (Beck/Erdős): If G has n vertices and maximum degree d, then
  R̂(G) ≪_d n (i.e., R̂(G) = O_d(n)).

  Resolution:
  DISPROVED for d = 3 by Rödl-Szemerédi (2000).

  Background:
  The size Ramsey number asks how few edges a graph H can have while still
  guaranteeing that any 2-coloring of H's edges contains a monochromatic
  copy of G. The conjecture suggested this is linear in n for bounded degree.

  Known Results:
  Positive (conjecture holds):
  - Paths: Beck (1983)
  - Trees: Friedman-Pippenger (1987)
  - Cycles: Haxell-Kohayakawa-Luczak (1995)

  Negative (conjecture fails for d = 3):
  - Rödl-Szemerédi (2000): R̂(G) ≫ n(log n)^c
  - Tikhomirov (2022): R̂(G) ≫ n·exp(c√(log n))

  Upper bounds for d = 3:
  - Kohayakawa et al.: n^{5/3+o(1)}
  - Conlon-Nenadov-Trujić: n^{8/5}
  - Draganić-Petrova (best): n^{3/2+o(1)}

  References:
  - [Be83b] Beck (1983), on size Ramsey number of paths, trees, circuits
  - [RoSz00] Rödl-Szemerédi (2000), size Ramsey numbers of bounded degree
  - [Ti22b] Tikhomirov (2022), bounded degree graphs with large size Ramsey
  - [DrPe22] Draganić-Petrova (2022), size Ramsey number of cubic graphs
-/

import Mathlib

namespace Erdos559

/-! ## Basic Definitions -/

/-- A simple graph with a finite vertex type -/
structure FiniteGraph (V : Type*) [Fintype V] where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v
  dec : DecidableRel adj := by infer_instance

/-- The number of edges in a graph -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) : ℕ :=
  (Finset.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2)
    Finset.univ).card

/-- The degree of a vertex -/
def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) (v : V) : ℕ :=
  (Finset.filter (fun u => G.adj v u) Finset.univ).card

/-- The maximum degree of a graph -/
def maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) : ℕ :=
  Finset.sup Finset.univ (degree G)

/-- A graph H is Ramsey for G if any 2-coloring of H's edges contains
    a monochromatic copy of G. -/
def IsRamseyFor {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (H : FiniteGraph W) (G : FiniteGraph V) : Prop :=
  ∀ (color : W → W → Bool),
    (∀ u v, color u v = color v u) →
    ∃ (f : V → W),
      Function.Injective f ∧
      ∃ (c : Bool), ∀ u v, G.adj u v → H.adj (f u) (f v) ∧ color (f u) (f v) = c

/-! ## Size Ramsey Number -/

/-- The size Ramsey number R̂(G) is the minimum number of edges m
    such that some graph H with m edges is Ramsey for G. -/
noncomputable def sizeRamsey {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) : ℕ :=
  Nat.find (⟨Fintype.card V * (Fintype.card V - 1) / 2,
    ⟨(⟨fun u v => u ≠ v, fun _ _ h => h.symm, fun _ h => h rfl⟩ :
      FiniteGraph V), by sorry⟩⟩ :
    ∃ m, ∃ (H : FiniteGraph (Fin m)), IsRamseyFor H G)

/-! ## The Conjecture (Disproved) -/

/-- The Beck/Erdős Conjecture: For graphs of bounded degree d,
    R̂(G) = O_d(n) where n = |V(G)|.

    This was DISPROVED for d ≥ 3. -/
def beck_erdos_conjecture : Prop :=
  ∀ d : ℕ, d ≥ 1 →
  ∃ c : ℝ, c > 0 ∧
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : FiniteGraph V),
    maxDegree G ≤ d →
    (sizeRamsey G : ℝ) ≤ c * Fintype.card V

/-- The conjecture is FALSE -/
theorem beck_erdos_conjecture_false : ¬beck_erdos_conjecture := by
  sorry -- Rödl-Szemerédi (2000)

/-! ## Positive Results (Special Cases) -/

/-- A graph is a path if it has n vertices and n-1 edges forming a chain -/
def IsPath {V : Type*} [Fintype V] [DecidableEq V] (G : FiniteGraph V) : Prop :=
  ∃ (ordering : Fin (Fintype.card V) → V),
    Function.Bijective ordering ∧
    (∀ i : Fin (Fintype.card V), ∀ j : Fin (Fintype.card V),
      G.adj (ordering i) (ordering j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))

/-- Beck (1983): Size Ramsey number of paths is linear -/
theorem beck_paths (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
    ∀ (G : FiniteGraph (Fin n)), IsPath G →
      (sizeRamsey G : ℝ) ≤ c * n := by
  sorry -- Beck (1983)

/-- A graph is a tree if it is connected and has n-1 edges -/
def IsTree {V : Type*} [Fintype V] [DecidableEq V] (G : FiniteGraph V) : Prop :=
  edgeCount G = Fintype.card V - 1 ∧
  -- Connected: any two vertices are reachable
  True -- Simplified; full connectivity definition omitted

/-- Friedman-Pippenger (1987): Size Ramsey number of trees is linear -/
theorem friedman_pippenger_trees (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
    ∀ (G : FiniteGraph (Fin n)), IsTree G →
      (sizeRamsey G : ℝ) ≤ c * n := by
  sorry -- Friedman-Pippenger (1987)

/-- A graph is a cycle if it has n vertices and n edges forming a ring -/
def IsCycle {V : Type*} [Fintype V] [DecidableEq V] (G : FiniteGraph V) : Prop :=
  edgeCount G = Fintype.card V ∧
  ∀ v : V, degree G v = 2

/-- Haxell-Kohayakawa-Luczak (1995): Size Ramsey number of cycles is linear -/
theorem haxell_kohayakawa_luczak_cycles (n : ℕ) (hn : n ≥ 3) :
    ∃ c : ℝ, c > 0 ∧
    ∀ (G : FiniteGraph (Fin n)), IsCycle G →
      (sizeRamsey G : ℝ) ≤ c * n := by
  sorry -- Haxell-Kohayakawa-Luczak (1995)

/-! ## Counterexamples (d = 3) -/

/-- Rödl-Szemerédi (2000): There exist degree-3 graphs with
    R̂(G) ≫ n(log n)^c -/
theorem rodl_szemeredi_counterexample :
    ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
    ∃ (G : FiniteGraph (Fin N)),
      maxDegree G ≤ 3 ∧
      (sizeRamsey G : ℝ) ≥ c * N * (Real.log N)^c := by
  sorry -- Rödl-Szemerédi (2000)

/-- Tikhomirov (2022): Improved lower bound R̂(G) ≫ n·exp(c√(log n)) -/
theorem tikhomirov_improved_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
    ∃ (G : FiniteGraph (Fin N)),
      maxDegree G ≤ 3 ∧
      (sizeRamsey G : ℝ) ≥ c * N * Real.exp (c * Real.sqrt (Real.log N)) := by
  sorry -- Tikhomirov (2022)

/-! ## Upper Bounds for Degree-3 -/

/-- Kohayakawa et al.: R̂(G) ≤ n^{5/3+o(1)} for degree-3 graphs -/
theorem kohayakawa_upper_bound :
    ∃ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) ∧
    ∀ N : ℕ, N ≥ 2 →
    ∀ (G : FiniteGraph (Fin N)),
      maxDegree G ≤ 3 →
      (sizeRamsey G : ℝ) ≤ (N : ℝ)^(5/3 + ε N) := by
  sorry -- Kohayakawa et al.

/-- Conlon-Nenadov-Trujić: R̂(G) ≪ n^{8/5} for degree-3 graphs -/
theorem conlon_nenadov_trujic_upper_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
    ∀ (G : FiniteGraph (Fin N)),
      maxDegree G ≤ 3 →
      (sizeRamsey G : ℝ) ≤ c * (N : ℝ)^(8/5) := by
  sorry -- Conlon-Nenadov-Trujić (2022)

/-- Draganić-Petrova (2022): Best known upper bound n^{3/2+o(1)} -/
theorem draganic_petrova_best_upper_bound :
    ∃ (ε : ℕ → ℝ), (∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, |ε N| < δ) ∧
    ∀ N : ℕ, N ≥ 2 →
    ∀ (G : FiniteGraph (Fin N)),
      maxDegree G ≤ 3 →
      (sizeRamsey G : ℝ) ≤ (N : ℝ)^(3/2 + ε N) := by
  sorry -- Draganić-Petrova (2022)

/-! ## The Open Question -/

/-- Open: What is the correct growth rate for degree-3 graphs?

    Current bounds:
    - Lower: n·exp(c√(log n)) (Tikhomirov)
    - Upper: n^{3/2+o(1)} (Draganić-Petrova)

    The gap is substantial. -/
def open_degree_3_question : Prop :=
  ∃ (f : ℕ → ℝ),
    (∀ N : ℕ, N ≥ 2 →
      ∀ (G : FiniteGraph (Fin N)), maxDegree G ≤ 3 →
        (sizeRamsey G : ℝ) ≤ f N) ∧
    (∀ N : ℕ, N ≥ 2 →
      ∃ (G : FiniteGraph (Fin N)), maxDegree G ≤ 3 ∧
        (sizeRamsey G : ℝ) ≥ f N / 2)

/-! ## Summary

**Status: DISPROVED (for d ≥ 3)**

The Beck-Erdős conjecture that R̂(G) ≪_d n for bounded-degree graphs
was disproved by Rödl-Szemerédi (2000) for d = 3.

**What holds:**
- Paths, trees, cycles: R̂(G) = O(n)

**What fails (d = 3):**
- Lower: R̂(G) ≫ n·exp(c√(log n)) (Tikhomirov)
- Upper: R̂(G) ≤ n^{3/2+o(1)} (Draganić-Petrova)

The exact growth rate for degree-3 graphs remains open.
-/

end Erdos559
