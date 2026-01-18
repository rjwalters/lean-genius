/-
  Erdős Problem #86: C₄-Free Subgraphs of Hypercubes

  Source: https://erdosproblems.com/86
  Status: OPEN ($100 prize)

  Statement:
  Let Qₙ be the n-dimensional hypercube graph (2ⁿ vertices, n·2^(n-1) edges).
  Is it true that every subgraph of Qₙ with ≥ (1/2 + o(1))·n·2^(n-1) edges
  contains a C₄ (4-cycle)?

  Equivalently: Let f(n) = max edges in a C₄-free subgraph of Qₙ.
  Conjecture: f(n) ≤ (1/2 + o(1))·n·2^(n-1)

  Background:
  The n-dimensional hypercube Qₙ has vertices {0,1}ⁿ with edges between
  vertices differing in exactly one coordinate. This is a fundamental
  structure in combinatorics with applications in coding theory and
  computer science.

  The question asks: how many edges can we keep while avoiding 4-cycles?
  A C₄ in Qₙ corresponds to four vertices forming a "square" where
  two coordinates vary.

  Known Bounds:
  Lower bounds on f(n):
  • Erdős (1991): f(n) ≥ (1/2 + c/n)·n·2^(n-1) for some c > 0
  • Brass-Harborth-Nienborg (1995): f(n) ≥ (1/2 + c/√n)·n·2^(n-1)

  Upper bounds on f(n):
  • Balogh-Hu-Lidický-Liu (2014): f(n) ≤ 0.6068·n·2^(n-1)
  • Baber (2012): f(n) ≤ 0.60318·n·2^(n-1)

  The gap between 1/2 and 0.60318 remains open.

  References:
  [Er91] Erdős, P. "Problems and results in combinatorial analysis" (1991)
  [BHN95] Brass, Harborth, Nienborg "On the max edges in C₄-free Qₙ" (1995)
  [BHLL14] Balogh, Hu, Lidický, Liu "Upper bounds on 4-cycle-free subgraphs"
  [Ba12b] Baber, R. "Turán densities of hypercubes" arXiv:1201.3587 (2012)

  Tags: graph-theory, hypercube, extremal, cycles, open-problem
-/

import Mathlib

open Finset

/-
## The Hypercube Graph Qₙ

The n-dimensional hypercube has vertices {0,1}ⁿ with edges between
vertices that differ in exactly one coordinate.
-/

/-- Vertices of the n-dimensional hypercube: binary strings of length n -/
def HypercubeVertex (n : ℕ) := Fin n → Bool

/-- Two hypercube vertices are adjacent if they differ in exactly one coordinate -/
def hypercubeAdj (n : ℕ) (u v : HypercubeVertex n) : Prop :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

/-- The hypercube graph Qₙ -/
def hypercubeGraph (n : ℕ) : SimpleGraph (HypercubeVertex n) where
  Adj := hypercubeAdj n
  symm := by
    intro u v h
    simp only [hypercubeAdj] at h ⊢
    convert h using 2
    ext i
    constructor <;> (intro h'; exact h'.symm)
  loopless := by
    intro v h
    simp only [hypercubeAdj] at h
    have : (Finset.univ.filter (fun i => v i ≠ v i)).card = 0 := by
      simp
    omega

/-- Number of vertices in Qₙ is 2ⁿ -/
theorem hypercube_vertex_count (n : ℕ) :
    Fintype.card (HypercubeVertex n) = 2^n := by
  simp [HypercubeVertex]
  exact Fintype.card_fun

/-- Number of edges in Qₙ is n·2^(n-1) -/
axiom hypercube_edge_count (n : ℕ) (hn : n ≥ 1) :
    (hypercubeGraph n).edgeFinset.card = n * 2^(n-1)

/-
## 4-Cycles in Hypercubes

A C₄ in Qₙ consists of four vertices forming a "square":
two coordinates i,j vary independently while others are fixed.
-/

/-- A 4-cycle in a graph -/
def hasC4 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ a b c d : V, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A graph is C₄-free -/
def isC4Free (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ¬hasC4 G

/-
## The Function f(n)

f(n) = maximum number of edges in a C₄-free subgraph of Qₙ
-/

/-- A subgraph of the hypercube -/
def HypercubeSubgraph (n : ℕ) := { G : SimpleGraph (HypercubeVertex n) // G ≤ hypercubeGraph n }

/-- f(n): maximum edges in a C₄-free subgraph of Qₙ -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup { G.val.edgeFinset.card | G : HypercubeSubgraph n //
         ∀ [DecidableRel G.val.Adj], isC4Free G.val }

/-
## Known Bounds

The best known bounds leave a gap between 1/2 and ~0.603.
-/

/-- Erdős's lower bound (1991): f(n) ≥ (1/2 + c/n)·n·2^(n-1) -/
axiom erdos_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≥ (1/2 + c/n) * n * 2^(n-1)

/-- Brass-Harborth-Nienborg lower bound (1995): f(n) ≥ (1/2 + c/√n)·n·2^(n-1) -/
axiom bhn_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≥ (1/2 + c/Real.sqrt n) * n * 2^(n-1)

/-- Baber's upper bound (2012): f(n) ≤ 0.60318·n·2^(n-1) -/
axiom baber_upper_bound :
  ∀ n ≥ 1, (f n : ℝ) ≤ 0.60318 * n * 2^(n-1)

/-- Combined bounds: 1/2 < lim inf f(n)/(n·2^(n-1)) ≤ lim sup ≤ 0.60318 -/
theorem f_bounds_summary (n : ℕ) (hn : n ≥ 2) :
    (1/2 : ℝ) * n * 2^(n-1) < f n ∧ (f n : ℝ) ≤ 0.60318 * n * 2^(n-1) := by
  constructor
  · -- Lower bound from BHN
    have ⟨c, hc, hbound⟩ := bhn_lower_bound
    have h := hbound n hn
    calc (1/2 : ℝ) * n * 2^(n-1)
        < (1/2 + c/Real.sqrt n) * n * 2^(n-1) := by
          apply mul_lt_mul_of_pos_right
          · linarith [Real.sqrt_pos.mpr (by linarith : (n : ℝ) > 0)]
          · positivity
      _ ≤ f n := h
  · exact baber_upper_bound n (by omega)

/-
## Erdős's Conjecture (OPEN)

The main conjecture: f(n) = (1/2 + o(1))·n·2^(n-1)
-/

/-- Erdős's conjecture: f(n)/(n·2^(n-1)) → 1/2 as n → ∞ -/
def erdos86Conjecture : Prop :=
  Filter.Tendsto (fun n => (f n : ℝ) / (n * 2^(n-1)))
    Filter.atTop (nhds (1/2))

/-- Equivalent formulation: for all ε > 0, f(n) ≤ (1/2 + ε)·n·2^(n-1) for large n -/
def erdos86ConjectureAlt : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ (1/2 + ε) * n * 2^(n-1)

/-- The conjecture is currently open -/
axiom erdos86_open : ¬(erdos86Conjecture ∨ ¬erdos86Conjecture → False)
  -- This is a placeholder indicating the problem is open
  -- Neither proved nor disproved

/-
## What Would Resolve the Conjecture?

To prove: Show f(n) ≤ (1/2 + ε)·n·2^(n-1) for any ε > 0, for large n
To disprove: Construct C₄-free subgraphs with > (1/2 + c)·n·2^(n-1) edges
             for some fixed c > 0 and all n
-/

/-- If proven, the limit would be exactly 1/2 -/
theorem conjecture_implies_limit (h : erdos86Conjecture) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(f n : ℝ) / (n * 2^(n-1)) - 1/2| < ε := by
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  exact h ε hε

#check erdos86Conjecture
#check @f_bounds_summary
#check baber_upper_bound
#check bhn_lower_bound
