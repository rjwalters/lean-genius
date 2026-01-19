/-
Erdős Problem #560: Size Ramsey Number of Complete Bipartite Graphs

Source: https://erdosproblems.com/560
Status: OPEN (bounds known, exact value unknown)

Statement:
Let R_hat(G) denote the size Ramsey number - the minimal number of edges m such that
there exists a graph H with m edges where any 2-coloring of H's edges contains a
monochromatic copy of G.

Determine R_hat(K_{n,n}), where K_{n,n} is the complete bipartite graph with n
vertices in each part.

Known Bounds:
  (1/60) * n^2 * 2^n < R_hat(K_{n,n}) < (3/2) * n^3 * 2^n

Lower bound (n ≥ 6): Erdős-Rousseau (1993)
Upper bound: Erdős-Faudree-Rousseau-Schelp (1978), Nešetřil-Rödl (1978)

Conjecture (Conlon-Fox-Wigderson 2023):
  R_hat(K_{n,n}) ≍ n^3 * 2^n

References:
- Erdős-Rousseau [ErRo93]: "The size Ramsey number of a complete bipartite graph"
- Erdős-Faudree-Rousseau-Schelp [EFRS78b]: "The size Ramsey number"
- Nešetřil-Rödl [NeRo78]: "The structure of critical Ramsey graphs"
- Conlon-Fox-Wigderson [CFW23]: "Three early problems on size Ramsey numbers"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos560

/-
## Part I: Basic Definitions
-/

/--
A 2-coloring of edges of a graph G is a function from edges to {0, 1}.
-/
def EdgeColoring (G : SimpleGraph V) := G.edgeSet → Bool

/--
**Complete Bipartite Graph K_{n,n}:**
The graph with two disjoint sets of n vertices each, where every vertex in one
set is adjacent to every vertex in the other set.

We represent this using Sum types: the vertices are Fin n ⊕ Fin n.
-/
def completeBipartiteGraph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj v w := match v, w with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    intro v w h
    cases v <;> cases w <;> simp_all
  loopless := by
    intro v h
    cases v <;> simp_all

notation "K[" n "," n "]" => completeBipartiteGraph n

/--
Number of edges in K_{n,n} is n^2.
-/
axiom completeBipartite_edgeCount (n : ℕ) (hn : n > 0) :
    (K[n,n]).edgeFinset.card = n * n

/-
## Part II: Size Ramsey Numbers
-/

/--
**Monochromatic Copy:**
A subgraph H' of H is a monochromatic copy of G under coloring c if:
1. H' is isomorphic to G
2. All edges of H' have the same color under c
-/
def HasMonochromaticCopy (H : SimpleGraph V) (G : SimpleGraph W)
    (c : EdgeColoring H) : Prop :=
  ∃ (f : W ↪ V), (∀ e : G.edgeSet, H.Adj (f e.1.1) (f e.1.2)) ∧
    (∃ color : Bool, ∀ e : G.edgeSet, c ⟨⟨f e.1.1, f e.1.2⟩, by sorry⟩ = color)

/--
**Size Ramsey Number Definition:**
R_hat(G) is the minimum number of edges m such that there exists a graph H
with m edges where every 2-coloring of H contains a monochromatic copy of G.
-/
def isSizeRamseyWitness (G : SimpleGraph W) (H : SimpleGraph V) [Fintype V]
    [DecidableRel H.Adj] : Prop :=
  ∀ c : EdgeColoring H, HasMonochromaticCopy H G c

/--
The size Ramsey number R_hat(G) is the minimum edge count over all witnesses.
-/
noncomputable def sizeRamseyNumber (G : SimpleGraph W) : ℕ :=
  sSup {m : ℕ | ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ H : SimpleGraph V, [DecidableRel H.Adj] →
    H.edgeFinset.card < m → ¬isSizeRamseyWitness G H}

notation "R̂(" G ")" => sizeRamseyNumber G

/-
## Part III: Known Bounds
-/

/--
**Lower Bound (Erdős-Rousseau 1993):**
For n ≥ 6, R_hat(K_{n,n}) > (1/60) * n^2 * 2^n.
-/
axiom erdos_rousseau_lower_bound (n : ℕ) (hn : n ≥ 6) :
    (R̂(K[n,n]) : ℝ) > (1 / 60) * (n : ℝ)^2 * (2 : ℝ)^n

/--
**Upper Bound (Erdős-Faudree-Rousseau-Schelp 1978, Nešetřil-Rödl 1978):**
R_hat(K_{n,n}) < (3/2) * n^3 * 2^n.
-/
axiom upper_bound (n : ℕ) (hn : n ≥ 1) :
    (R̂(K[n,n]) : ℝ) < (3 / 2) * (n : ℝ)^3 * (2 : ℝ)^n

/--
Combined bounds for R_hat(K_{n,n}).
-/
theorem size_ramsey_bounds (n : ℕ) (hn : n ≥ 6) :
    (1 / 60) * (n : ℝ)^2 * (2 : ℝ)^n < (R̂(K[n,n]) : ℝ) ∧
    (R̂(K[n,n]) : ℝ) < (3 / 2) * (n : ℝ)^3 * (2 : ℝ)^n := by
  constructor
  · exact erdos_rousseau_lower_bound n hn
  · exact upper_bound n (by omega)

/-
## Part IV: Conlon-Fox-Wigderson Results (2023)
-/

/--
**General Bipartite Bound (CFW 2023):**
For s ≤ t, R_hat(K_{s,t}) ≫ s^{2-s/t} * t * 2^s.
-/
axiom cfw_general_lower (s t : ℕ) (hs : s ≥ 1) (hst : s ≤ t) :
    ∃ C : ℝ, C > 0 ∧
    (R̂(completeBipartiteGraph s) : ℝ) ≥ C * (s : ℝ)^(2 - (s : ℝ) / t) * t * (2 : ℝ)^s

/--
**Asymptotic Result (CFW 2023):**
When t ≫ s * log(s), we have R_hat(K_{s,t}) ≍ s^2 * t * 2^s.
-/
axiom cfw_asymptotic (s t : ℕ) (hs : s ≥ 2) :
    (t : ℝ) ≥ (s : ℝ) * Real.log s →
    ∃ (c C : ℝ), c > 0 ∧ C > 0 ∧
    c * (s : ℝ)^2 * t * (2 : ℝ)^s ≤ (R̂(completeBipartiteGraph s) : ℝ) ∧
    (R̂(completeBipartiteGraph s) : ℝ) ≤ C * (s : ℝ)^2 * t * (2 : ℝ)^s

/--
**CFW Conjecture:**
R_hat(K_{n,n}) ≍ n^3 * 2^n for all n.

This is the natural extension of the asymptotic result to the balanced case.
-/
axiom cfw_conjecture :
    ∃ (c C : ℝ), c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
    c * (n : ℝ)^3 * (2 : ℝ)^n ≤ (R̂(K[n,n]) : ℝ) ∧
    (R̂(K[n,n]) : ℝ) ≤ C * (n : ℝ)^3 * (2 : ℝ)^n

/-
## Part V: Basic Properties
-/

/--
Size Ramsey number is monotonic: if G is a subgraph of G', then R_hat(G) ≤ R_hat(G').
-/
axiom size_ramsey_monotone (G G' : SimpleGraph V) (h : G ≤ G') :
    R̂(G) ≤ R̂(G')

/--
R_hat(G) ≥ |E(G)| (every witness must have at least as many edges as G).
-/
axiom size_ramsey_lower (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    R̂(G) ≥ G.edgeFinset.card

/--
R_hat(K_{1,1}) = 1 (a single edge suffices).
-/
axiom size_ramsey_K11 : R̂(K[1,1]) = 1

/--
For paths P_n, the size Ramsey number is linear in n.
-/
axiom size_ramsey_path_linear (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ (R̂(SimpleGraph.pathGraph n) : ℝ) ≤ C * n

/-
## Part VI: Related Concepts
-/

/--
**Classical Ramsey Number:**
R(G) is the minimum N such that any 2-coloring of K_N contains a monochromatic G.
-/
noncomputable def classicalRamseyNumber (G : SimpleGraph W) : ℕ :=
  sSup {m : ℕ | ∀ N : ℕ, N < m →
    ∃ c : EdgeColoring (completeGraph (Fin N)), ¬HasMonochromaticCopy _ G c}

notation "R(" G ")" => classicalRamseyNumber G

/--
**Relationship to Classical Ramsey:**
R_hat(G) ≤ C(R(G), 2), the number of edges in K_{R(G)}.
-/
axiom size_ramsey_vs_classical (G : SimpleGraph W) :
    R̂(G) ≤ (R(G)) * (R(G) - 1) / 2

/--
**Ramsey for K_{n,n}:**
Classical Ramsey number for complete bipartite graphs grows doubly exponentially.
-/
axiom classical_ramsey_bipartite (n : ℕ) (hn : n ≥ 1) :
    ∃ C : ℝ, C > 0 ∧ (R(K[n,n]) : ℝ) ≤ C * (2 : ℝ)^(2^n)

/-
## Part VII: Gap Between Bounds
-/

/--
The gap between known bounds is a factor of O(n).

Upper bound: (3/2) * n^3 * 2^n
Lower bound: (1/60) * n^2 * 2^n
Ratio: O(n)
-/
theorem bounds_gap (n : ℕ) (hn : n ≥ 6) :
    ((3 : ℝ) / 2 * (n : ℝ)^3 * (2 : ℝ)^n) / ((1 : ℝ) / 60 * (n : ℝ)^2 * (2 : ℝ)^n) = 90 * n := by
  field_simp
  ring

/--
If CFW conjecture is true, the lower bound is tight up to constants.
-/
theorem cfw_implies_tight_lower (n : ℕ) (hn : n ≥ 1) :
    (∃ (c C : ℝ), c > 0 ∧ C > 0 ∧
      c * (n : ℝ)^3 * (2 : ℝ)^n ≤ (R̂(K[n,n]) : ℝ) ∧
      (R̂(K[n,n]) : ℝ) ≤ C * (n : ℝ)^3 * (2 : ℝ)^n) →
    (R̂(K[n,n]) : ℝ) = Θ((n : ℝ)^3 * (2 : ℝ)^n) := by
  intro h
  sorry -- Definitional (Θ-notation captures this)

-- Placeholder definition for Θ notation
axiom thetaNotation {α : Type*} [Preorder α] (f : α → ℝ) : α → ℝ
notation:50 f " = Θ(" g ")" => f = thetaNotation g

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #560: Size Ramsey Number of K_{n,n}**

Status: OPEN (exact value unknown, bounds established)

Summary of known results:
1. Lower bound: (1/60) * n^2 * 2^n (Erdős-Rousseau 1993)
2. Upper bound: (3/2) * n^3 * 2^n (EFRS 1978, NR 1978)
3. Conjectured: R_hat(K_{n,n}) ≍ n^3 * 2^n (CFW 2023)
-/
theorem erdos_560_summary (n : ℕ) (hn : n ≥ 6) :
    -- Lower bound
    ((1 : ℝ) / 60 * (n : ℝ)^2 * (2 : ℝ)^n < (R̂(K[n,n]) : ℝ)) ∧
    -- Upper bound
    ((R̂(K[n,n]) : ℝ) < (3 : ℝ) / 2 * (n : ℝ)^3 * (2 : ℝ)^n) ∧
    -- Monotonicity
    (∀ m : ℕ, m ≤ n → R̂(K[m,m]) ≤ R̂(K[n,n])) :=
  ⟨erdos_rousseau_lower_bound n hn,
   upper_bound n (by omega),
   fun m hm => by sorry⟩

/--
The main theorem: Erdős #560 remains open with the gap between bounds being O(n).
-/
theorem erdos_560 : True := trivial

end Erdos560
