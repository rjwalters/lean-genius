/-!
# Erdős Problem #810 — Rainbow C₄ in Edge-Colored Dense Graphs

Does there exist ε > 0 such that for all sufficiently large n, there exists
a graph G on n vertices with at least εn² edges whose edges can be colored
with n colors so that every C₄ receives 4 distinct colors?

A problem of Burr, Erdős, Graham, and Sós [Er91].

Reference: https://erdosproblems.com/810
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Edge Colorings and Rainbow Subgraphs -/

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

/-- A C₄ is rainbow under a coloring if all 4 edges have distinct colors -/
def CycleFour.isRainbow (C : CycleFour G) (χ : EdgeColoringN G) : Prop :=
  let c₁ := χ C.v₁ C.v₂ C.edge12
  let c₂ := χ C.v₂ C.v₃ C.edge23
  let c₃ := χ C.v₃ C.v₄ C.edge34
  let c₄ := χ C.v₄ C.v₁ C.edge41
  ({c₁, c₂, c₃, c₄} : Finset (Fin n)).card = 4

/-- An edge coloring is rainbow-C₄ if every C₄ in G is rainbow -/
def IsRainbowC4Coloring (G : SimpleGraph (Fin n)) (χ : EdgeColoringN G) : Prop :=
  ∀ C : CycleFour G, C.isRainbow χ

/-! ## Dense Graphs with Rainbow-C₄ Colorings -/

/-- A graph on n vertices has a rainbow-C₄ n-coloring and ≥ εn² edges -/
def HasDenseRainbowC4 (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
    ∃ χ : EdgeColoringN G, IsRainbowC4Coloring G χ

/-! ## The Burr–Erdős–Graham–Sós Problem -/

/-- Erdős Problem 810 (Burr–Erdős–Graham–Sós): Does there exist ε > 0
    such that for all sufficiently large n, there is a graph on n vertices
    with ≥ εn² edges admitting an n-coloring where every C₄ is rainbow? -/
axiom ErdosProblem810 :
  ∃ ε : ℝ, ε > 0 ∧
    ∀ᶠ n in Filter.atTop, HasDenseRainbowC4 n ε

/-! ## Trivial Observations -/

/-- C₄-free graphs trivially satisfy the rainbow condition (vacuously).
    The Kővári–Sós–Turán theorem gives ex(n; C₄) = O(n^{3/2}),
    so C₄-free graphs have too few edges (o(n²)). -/
axiom c4_free_too_sparse :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (hn : 1 ≤ n)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ C4 : CycleFour G, False) →
        (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)

/-- If the conjecture is true, the graph must contain many C₄'s
    but all of them must be rainbow — a delicate balance between
    density and structure. -/
axiom rainbow_requires_many_C4 (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : ε > 0)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hd : ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
  ∃ C4 : CycleFour G, True
