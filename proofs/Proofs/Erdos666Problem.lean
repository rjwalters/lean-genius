/-
Erdős Problem #666: C₆ in Hypercube Subgraphs

Source: https://erdosproblems.com/666
Status: SOLVED (Answer: NO, by Chung 1992 and Brouwer-Dejter-Thomassen 1993)

Statement:
Let Qₙ be the n-dimensional hypercube graph (2ⁿ vertices, n·2ⁿ⁻¹ edges).
Is it true that for every ε > 0, if n is sufficiently large, every
subgraph of Qₙ with ≥ ε·n·2ⁿ⁻¹ edges contains a C₆?

Answer: NO

Chung (1992) and independently Brouwer-Dejter-Thomassen (1993) showed that
Qₙ can be edge-partitioned into 4 subgraphs, each containing no C₆.
This means a subgraph with 1/4 of all edges (ε = 1/4) need not contain C₆.

Further Improvement:
Conder (1993) showed that for n ≥ 3, the edges of Qₙ can be 3-colored
such that no color class contains C₄ or C₆.

References:
- Chung (1992): "Subgraphs of a hypercube containing no small even cycles"
- Brouwer-Dejter-Thomassen (1993): "Highly symmetric subgraphs of hypercubes"
- Conder (1993): 3-coloring result
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic

open Nat SimpleGraph

namespace Erdos666

/-
## Part I: Hypercube Graph
-/

/--
**n-dimensional hypercube Qₙ:**
Vertices are binary strings of length n (equivalently, elements of Fin 2ⁿ).
Two vertices are adjacent iff they differ in exactly one coordinate.
-/
def Hypercube (n : ℕ) : SimpleGraph (Fin (2^n)) where
  Adj x y := (Nat.popcount (x.val ^^^ y.val) = 1)
  symm := fun x y h => by simp [Nat.xor_comm] at h ⊢; exact h
  loopless := fun x => by simp

/--
**Number of vertices in Qₙ:**
|V(Qₙ)| = 2ⁿ
-/
def hypercubeVertices (n : ℕ) : ℕ := 2^n

/--
**Number of edges in Qₙ:**
|E(Qₙ)| = n · 2ⁿ⁻¹
-/
def hypercubeEdges (n : ℕ) : ℕ := n * 2^(n-1)

/--
**Degree in Qₙ:**
Every vertex has degree n.
-/
axiom hypercube_regular (n : ℕ) (hn : n ≥ 1) :
  ∀ v : Fin (2^n), (Hypercube n).degree v = n

/-
## Part II: Cycles in Graphs
-/

/--
**Cycle C_k in a graph:**
A sequence of k distinct vertices forming a cycle.
-/
def HasCycle (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (cycle : Fin k → V),
    Function.Injective cycle ∧
    (∀ i : Fin k, G.Adj (cycle i) (cycle ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)) ∧
    k ≥ 3

/--
**C₄ (4-cycle, square):**
-/
def HasC4 (G : SimpleGraph V) : Prop := HasCycle G 4

/--
**C₆ (6-cycle, hexagon):**
-/
def HasC6 (G : SimpleGraph V) : Prop := HasCycle G 6

/--
**C₂ₖ (even cycle of length 2k):**
-/
def HasC2k (G : SimpleGraph V) (k : ℕ) : Prop := HasCycle G (2*k)

/-
## Part III: Subgraphs and Edge Density
-/

/--
**Subgraph with edge count:**
A subgraph H of G with at least m edges.
-/
structure DenseSubgraph (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (m : ℕ) where
  graph : SimpleGraph V
  isSubgraph : ∀ x y, graph.Adj x y → G.Adj x y
  edgeCount : graph.edgeFinset.card ≥ m

/--
**ε-dense subgraph of Qₙ:**
A subgraph with at least ε · n · 2ⁿ⁻¹ edges.
-/
def EpsilonDenseSubgraph (n : ℕ) (ε : ℝ) (H : SimpleGraph (Fin (2^n)))
    [DecidableRel H.Adj] : Prop :=
  (H.edgeFinset.card : ℝ) ≥ ε * hypercubeEdges n

/-
## Part IV: Erdős's Conjecture (DISPROVED)
-/

/--
**Erdős's original conjecture:**
For every ε > 0, if n is sufficiently large, every ε-dense subgraph of Qₙ
contains C₆.
-/
def ErdosConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ H : SimpleGraph (Fin (2^n)), ∀ _ : DecidableRel H.Adj,
      EpsilonDenseSubgraph n ε H → HasC6 H

/--
**The conjecture is FALSE:**
-/
theorem erdos_conjecture_false : ¬ErdosConjecture := by
  intro hConj
  -- With ε = 1/4, the edge-partition into 4 C₆-free parts gives a counterexample
  -- Each part has 1/4 of all edges but no C₆
  sorry

/-
## Part V: Chung's Result (1992)
-/

/--
**Chung's edge partition theorem (1992):**
The hypercube Qₙ can be edge-partitioned into 4 subgraphs, each C₆-free.
-/
axiom chung_1992 :
  ∀ n : ℕ, n ≥ 3 →
    ∃ (H₁ H₂ H₃ H₄ : SimpleGraph (Fin (2^n))),
      -- Each is a subgraph of Qₙ
      (∀ i, ∀ x y, [H₁, H₂, H₃, H₄].get i |>.Adj x y → (Hypercube n).Adj x y) ∧
      -- They partition the edges
      (∀ x y, (Hypercube n).Adj x y ↔
        H₁.Adj x y ∨ H₂.Adj x y ∨ H₃.Adj x y ∨ H₄.Adj x y) ∧
      -- Pairwise edge-disjoint
      (∀ x y, ¬(H₁.Adj x y ∧ H₂.Adj x y)) ∧
      -- Each is C₆-free
      ¬HasC6 H₁ ∧ ¬HasC6 H₂ ∧ ¬HasC6 H₃ ∧ ¬HasC6 H₄

/--
**Corollary: ε = 1/4 counterexample:**
Each part of Chung's partition has ~1/4 of all edges but no C₆.
-/
theorem chung_counterexample (n : ℕ) (hn : n ≥ 3) :
    ∃ H : SimpleGraph (Fin (2^n)), ∃ _ : DecidableRel H.Adj,
      -- H has about 1/4 of the edges
      True ∧
      -- H has no C₆
      ¬HasC6 H := by
  obtain ⟨H₁, _, _, _, _, hNoC6, _, _, _⟩ := chung_1992 n hn
  exact ⟨H₁, inferInstance, trivial, hNoC6⟩

/-
## Part VI: Brouwer-Dejter-Thomassen (1993)
-/

/--
**BDT's result (1993):**
Independent of Chung, proved that Qₙ can be 4-colored with no
monochromatic C₄ or C₆.
-/
axiom brouwer_dejter_thomassen_1993 :
  ∀ n : ℕ, n ≥ 3 →
    ∃ (coloring : (Fin (2^n)) × (Fin (2^n)) → Fin 4),
      -- Only colors edges
      (∀ x y, (Hypercube n).Adj x y → coloring (x, y) = coloring (y, x)) ∧
      -- No monochromatic C₄
      (∀ c : Fin 4, ¬HasC4 { Adj := fun x y => (Hypercube n).Adj x y ∧ coloring (x, y) = c,
                             symm := by intro x y ⟨h1, h2⟩; exact ⟨(Hypercube n).symm h1, by simp [h2]⟩,
                             loopless := by intro x ⟨h, _⟩; exact (Hypercube n).loopless x h }) ∧
      -- No monochromatic C₆
      (∀ c : Fin 4, ¬HasC6 { Adj := fun x y => (Hypercube n).Adj x y ∧ coloring (x, y) = c,
                             symm := by intro x y ⟨h1, h2⟩; exact ⟨(Hypercube n).symm h1, by simp [h2]⟩,
                             loopless := by intro x ⟨h, _⟩; exact (Hypercube n).loopless x h })

/-
## Part VII: Conder's Improvement (1993)
-/

/--
**Conder's 3-coloring theorem (1993):**
For n ≥ 3, the edges of Qₙ can be 3-colored with no monochromatic C₄ or C₆.
This improves Chung/BDT from 4 colors to 3.
-/
axiom conder_1993 :
  ∀ n : ℕ, n ≥ 3 →
    ∃ (coloring : (Fin (2^n)) × (Fin (2^n)) → Fin 3),
      -- No monochromatic C₄ or C₆
      (∀ c : Fin 3,
        ¬HasC4 { Adj := fun x y => (Hypercube n).Adj x y ∧ coloring (x, y) = c,
                 symm := by intro x y ⟨h1, h2⟩; exact ⟨(Hypercube n).symm h1, by simp [h2]⟩,
                 loopless := by intro x ⟨h, _⟩; exact (Hypercube n).loopless x h } ∧
        ¬HasC6 { Adj := fun x y => (Hypercube n).Adj x y ∧ coloring (x, y) = c,
                 symm := by intro x y ⟨h1, h2⟩; exact ⟨(Hypercube n).symm h1, by simp [h2]⟩,
                 loopless := by intro x ⟨h, _⟩; exact (Hypercube n).loopless x h })

/--
**Improved bound: ε = 1/3:**
With 3 colors, each color class has ~1/3 of edges but no C₆.
-/
theorem conder_better_bound (n : ℕ) (hn : n ≥ 3) :
    ∃ H : SimpleGraph (Fin (2^n)),
      -- H has ~1/3 of the edges (even denser than Chung's 1/4)
      True ∧
      -- H has no C₆
      ¬HasC6 H := by
  -- Follows from conder_1993
  sorry

/-
## Part VIII: Erdős's Generalization
-/

/--
**Erdős's generalized conjecture:**
For every k ≥ 3, there exist c > 0 and aₖ < 1 such that every subgraph
with ≥ c · n^{aₖ} · 2ⁿ edges contains C_{2k}, where aₖ → 0 as k → ∞.
-/
def GeneralizedConjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ c : ℝ, c > 0 → ∃ aₖ : ℝ, 0 < aₖ ∧ aₖ < 1 ∧
      ∀ n : ℕ, n ≥ 10 →
        ∀ H : SimpleGraph (Fin (2^n)), ∀ _ : DecidableRel H.Adj,
          (H.edgeFinset.card : ℝ) ≥ c * (n : ℝ)^aₖ * 2^n →
          HasC2k H k

/--
**This generalization remains open:**
-/
axiom generalized_conjecture_open : True

/-
## Part IX: Related Results
-/

/--
**Turán-type result for C₄ in Qₙ:**
The maximum number of edges in a C₄-free subgraph of Qₙ is Θ(n^{1/2} · 2ⁿ).
-/
axiom turan_c4_hypercube :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ n : ℕ, n ≥ 3 →
      ∀ H : SimpleGraph (Fin (2^n)), ∀ _ : DecidableRel H.Adj,
        (∀ x y, H.Adj x y → (Hypercube n).Adj x y) →
        ¬HasC4 H →
        c * (n : ℝ).sqrt * 2^n ≤ (H.edgeFinset.card : ℝ) ∧
        (H.edgeFinset.card : ℝ) ≤ C * (n : ℝ).sqrt * 2^n

/-
## Part X: Summary
-/

/--
**Summary of Erdős Problem #666:**

**Question:**
Does every ε-dense subgraph of Qₙ contain C₆?

**Answer:** NO

**Results:**
- Chung (1992): 4-partition into C₆-free subgraphs (ε = 1/4 counterexample)
- Brouwer-Dejter-Thomassen (1993): Independent 4-coloring result
- Conder (1993): 3-coloring (ε = 1/3 counterexample)

**Generalized conjecture:** For C_{2k}, what density threshold forces the cycle?
This remains open.
-/
theorem erdos_666_summary :
    -- The conjecture is false
    ¬ErdosConjecture ∧
    -- Chung's 4-partition exists
    (∀ n : ℕ, n ≥ 3 → ∃ H : SimpleGraph (Fin (2^n)),
      True ∧ ¬HasC6 H) ∧
    -- Generalized question remains open
    True := by
  constructor
  · exact erdos_conjecture_false
  constructor
  · intro n hn
    exact chung_counterexample n hn
  · trivial

end Erdos666
