/-
Erdős Problem #810: Rainbow C₄ in Edge-Colored Dense Graphs

Source: https://erdosproblems.com/810
Status: OPEN (Burr, Erdős, Graham, Sós)

## Statement

Does there exist ε > 0 such that for all sufficiently large n, there exists
a graph G on n vertices with at least εn² edges whose edges can be colored
with n colors so that every C₄ receives 4 distinct colors?

## Background

A problem of Burr, Erdős, Graham, and Sós [Er91]. See also Problem #809.
The Kővári-Sós-Turán theorem gives ex(n; C₄) = O(n^{3/2}), so C₄-free
graphs (which vacuously satisfy the rainbow condition) are too sparse.
Any positive answer must involve graphs with many C₄s, all of which
are rainbow — a delicate balance between density and structure.

## Approach

We formalize edge colorings, the C₄ structure, and the rainbow property.
The main conjecture is stated as a Prop definition (not an axiom, since it is OPEN).
The Kővári-Sós-Turán sparsity bound for C₄-free graphs is axiomatized.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos810

variable {n : ℕ}

-- ## Part I: Edge Colorings and Rainbow Subgraphs

/-- An edge coloring of a graph on Fin n using n colors.
    Assigns a color in Fin n to each edge (unordered pair). -/
def EdgeColoringN (G : SimpleGraph (Fin n)) :=
  ∀ (u v : Fin n), G.Adj u v → Fin n

/-- A 4-cycle in G given by four distinct vertices forming a cycle:
    v₁ -- v₂ -- v₃ -- v₄ -- v₁ -/
structure CycleFour (G : SimpleGraph (Fin n)) where
  v₁ : Fin n
  v₂ : Fin n
  v₃ : Fin n
  v₄ : Fin n
  distinct : ({v₁, v₂, v₃, v₄} : Finset (Fin n)).card = 4
  edge12 : G.Adj v₁ v₂
  edge23 : G.Adj v₂ v₃
  edge34 : G.Adj v₃ v₄
  edge41 : G.Adj v₄ v₁

/-- A C₄ is rainbow under a coloring if all 4 edges have distinct colors. -/
def CycleFour.isRainbow {G : SimpleGraph (Fin n)} (C : CycleFour G)
    (χ : EdgeColoringN G) : Prop :=
  let c₁ := χ C.v₁ C.v₂ C.edge12
  let c₂ := χ C.v₂ C.v₃ C.edge23
  let c₃ := χ C.v₃ C.v₄ C.edge34
  let c₄ := χ C.v₄ C.v₁ C.edge41
  ({c₁, c₂, c₃, c₄} : Finset (Fin n)).card = 4

/-- An edge coloring is rainbow-C₄ if every C₄ in G is rainbow. -/
def IsRainbowC4Coloring (G : SimpleGraph (Fin n)) (χ : EdgeColoringN G) : Prop :=
  ∀ C : CycleFour G, C.isRainbow χ

-- ## Part II: Dense Graphs with Rainbow-C₄ Colorings

/-- A graph on n vertices has a rainbow-C₄ n-coloring and at least εn² edges. -/
def HasDenseRainbowC4 (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
    ∃ χ : EdgeColoringN G, IsRainbowC4Coloring G χ

-- ## Part III: The Burr-Erdős-Graham-Sós Conjecture (OPEN)

/-- **Erdős Problem 810** (Burr-Erdős-Graham-Sós conjecture):
    Does there exist ε > 0 such that for all sufficiently large n,
    there is a graph on n vertices with at least εn² edges admitting
    an n-coloring where every C₄ is rainbow?

    This is an OPEN problem — stated as a Prop, not asserted as true. -/
def ErdosProblem810 : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    ∀ᶠ n in Filter.atTop, HasDenseRainbowC4 n ε

-- ## Part IV: Known Results (Axioms)

/-- **Kővári-Sós-Turán bound for C₄:**
    C₄-free graphs on n vertices have O(n^{3/2}) edges.
    This means C₄-free graphs (which vacuously satisfy the rainbow condition)
    have too few edges to achieve the quadratic density εn². -/
axiom kovari_sos_turan_C4 :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (hn : 1 ≤ n)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ C4 : CycleFour G, False) →
        (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)

/-- **Dense graphs contain C₄s:**
    Any graph with Ω(n²) edges must contain at least one C₄.
    This is a consequence of Kővári-Sós-Turán. -/
axiom dense_graph_has_C4 (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : ε > 0)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hd : ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
  ∃ C4 : CycleFour G, True

-- ## Part V: Structural Observations

/-- C₄-free graphs vacuously satisfy the rainbow condition. -/
theorem c4_free_vacuously_rainbow
    (G : SimpleGraph (Fin n)) (χ : EdgeColoringN G)
    (hfree : ∀ C4 : CycleFour G, False) :
    IsRainbowC4Coloring G χ :=
  fun C => False.elim (hfree C)

end Erdos810
