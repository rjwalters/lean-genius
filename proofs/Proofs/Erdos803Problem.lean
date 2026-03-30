/- Erdős Problem #803: D-Balanced Subgraphs in Dense Graphs

A graph H is D-balanced if Δ(H) ≤ D · δ(H). Is it true that for every
m ≥ 1, any sufficiently large graph with n log n edges contains a
O(1)-balanced subgraph with m vertices and ≫ m log m edges?

**Answer**: NO — disproved by Alon (2008). The maximum is O(m√(log m)),
not O(m log m). Janzer-Sudakov (2023) achieved the best positive bound.

**Key Results**:
- Erdős-Simonovits: Proved for polynomial density (n^(1+c) edges)
- Alon (2008): Disproved for logarithmic density — maximum is O(m√(log m))
- Janzer-Sudakov (2023): Best positive result is m√(log m)/(log log m)^(3/2)

References:
- [Al08] Alon, "The maximum number of edges in a balanced graph" (2008)
- [JaSu23] Janzer-Sudakov, "Nearly-balanced subgraphs" (2023)
- https://erdosproblems.com/803
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real SimpleGraph

namespace Erdos803

/- ##D-Balanced Graphs -/

/-- Maximum degree Δ(G) of a graph G. -/
noncomputable def maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ (fun v => G.degree v)

/-- Minimum degree δ(G) of a graph G. -/
noncomputable def minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.inf Finset.univ (fun v => G.degree v)

/-- A graph H is D-balanced (D-almost-regular) if Δ(H) ≤ D · δ(H). -/
def IsDBalanced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) : Prop :=
  maxDegree G ≤ D * minDegree G

/-- Regular graphs are 1-balanced. -/
theorem regular_is_1_balanced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hreg : ∀ v : V, G.degree v = k) : IsDBalanced G 1 := by
  unfold IsDBalanced maxDegree minDegree
  simp only [one_mul]
  have hmax : Finset.sup Finset.univ (fun v => G.degree v) = k := by
    apply Finset.sup_congr rfl
    intro v _
    exact hreg v
  have hmin : Finset.inf Finset.univ (fun v => G.degree v) = k := by
    apply Finset.inf_congr rfl
    intro v _
    exact hreg v
  simp [hmax, hmin]

/-- If G is D-balanced and D ≤ D', then G is D'-balanced. -/
theorem balanced_monotone {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D D' : ℕ)
    (hbal : IsDBalanced G D) (hle : D ≤ D') : IsDBalanced G D' := by
  unfold IsDBalanced at *
  calc maxDegree G ≤ D * minDegree G := hbal
    _ ≤ D' * minDegree G := Nat.mul_le_mul_right _ hle

/- ##Edge Density -/

/-- Number of edges in a graph. -/
noncomputable def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeSet.toFinset.card

/-- Number of vertices. -/
def vertexCount (V : Type*) [Fintype V] : ℕ := Fintype.card V

/-- A graph has logarithmic density if it has ≥ n log n edges. -/
def HasLogDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (edgeCount G : ℝ) ≥ (vertexCount V) * Real.log (vertexCount V)

/- ##The Conjecture (Disproved) -/

/-- The original conjecture: for every m ≥ 1, if n is sufficiently large,
any graph on n vertices with ≥ n log n edges contains a O(1)-balanced
subgraph with m vertices and ≥ m log m edges. -/
def Erdos803Conjecture : Prop :=
  ∃ D : ℕ, ∀ m : ℕ, m ≥ 1 →
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      vertexCount V ≥ N →
      HasLogDensity G →
      ∃ (W : Type*) [Fintype W] [DecidableEq W],
      ∃ (H : SimpleGraph W) [DecidableRel H.Adj],
      ∃ (f : W ↪ V),
        (∀ w₁ w₂, H.Adj w₁ w₂ → G.Adj (f w₁) (f w₂)) ∧
        vertexCount W = m ∧
        IsDBalanced H D ∧
        (edgeCount H : ℝ) ≥ m * Real.log m

/- ##Alon's Counterexample (2008) -/

/-- Alon's theorem (2008): The conjecture is FALSE. For every D > 1 and
large n, there exists a graph G with n vertices and ≥ n log n edges such
that any D-balanced subgraph H has ≤ m√(log m) + log D edges. -/
/-- The conjecture is false: Alon's counterexample applies for D = 2. -/
axiom erdos_803_disproved : ¬Erdos803Conjecture

/- ##Positive Results -/

/-- Erdős-Simonovits (polynomial density): For graphs with n^(1+c) edges
(c > 0), there exist O(1)-balanced subgraphs with m^(1+c) edges. -/
axiom erdos_simonovits_polynomial :
  ∀ c : ℝ, c > 0 →
    ∃ D : ℕ, ∀ m : ℕ, m ≥ 1 →
      ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        vertexCount V ≥ N →
        (edgeCount G : ℝ) ≥ (vertexCount V : ℝ)^(1 + c) →
        ∃ (W : Type*) [Fintype W] [DecidableEq W],
        ∃ (H : SimpleGraph W) [DecidableRel H.Adj],
        ∃ (f : W ↪ V),
          (∀ w₁ w₂, H.Adj w₁ w₂ → G.Adj (f w₁) (f w₂)) ∧
          vertexCount W = m ∧
          IsDBalanced H D ∧
          (edgeCount H : ℝ) ≥ (m : ℝ)^(1 + c)

/-- Janzer-Sudakov (2023): Best positive result for logarithmic density.
Any graph with n log n edges contains a O(1)-balanced subgraph on m
vertices with m√(log m)/(log log m)^(3/2) edges. -/
/- ##Summary -/

/-- **Erdős Problem #803 Summary.**
The conjecture is disproved: logarithmic-density graphs do NOT always contain
O(1)-balanced subgraphs with m log m edges. The correct threshold is
Θ(m√(log m)). Polynomial density behaves differently (conjecture holds). -/
theorem erdos_803_summary :
    ¬Erdos803Conjecture ∧
    (∀ c : ℝ, c > 0 →
      ∃ D : ℕ, ∀ m : ℕ, m ≥ 1 →
        ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          vertexCount V ≥ N →
          (edgeCount G : ℝ) ≥ (vertexCount V : ℝ)^(1 + c) →
          ∃ (W : Type*) [Fintype W] [DecidableEq W],
          ∃ (H : SimpleGraph W) [DecidableRel H.Adj],
          ∃ (f : W ↪ V),
            (∀ w₁ w₂, H.Adj w₁ w₂ → G.Adj (f w₁) (f w₂)) ∧
            vertexCount W = m ∧
            IsDBalanced H D ∧
            (edgeCount H : ℝ) ≥ (m : ℝ)^(1 + c)) :=
  ⟨erdos_803_disproved, erdos_simonovits_polynomial⟩

end Erdos803
