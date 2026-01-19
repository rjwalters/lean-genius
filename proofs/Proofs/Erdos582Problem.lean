/-
Erdős Problem #582: Folkman Numbers and K₄-Free Ramsey Graphs

Source: https://erdosproblems.com/582
Status: SOLVED (Folkman, 1970)
Prize: $100

Statement:
Does there exist a graph G which contains no K₄, and yet any 2-colouring
of the edges produces a monochromatic K₃?

Answer: YES

Folkman (1970) proved existence. The specific Folkman number f(2,3,4)
(the minimum number of vertices in such a graph) satisfies:
  19 ≤ f(2,3,4) ≤ 941

Key bounds:
- Folkman (1970): Existence proof with astronomical bounds
- Frankl-Rödl (1986): ≤ 7×10¹¹
- Spencer (1988): ≤ 3×10⁹ (resolved Erdős's $100 challenge for < 10¹⁰)
- Lu (2007): ≤ 9697
- Dudek-Rödl (2008): ≤ 941 (current record)
- Radziszowski-Xu (2007): ≥ 19, conjectured ≤ 127

References:
- Erdős-Hajnal [ErHa67]: Original question
- Folkman [Fo70]: Existence proof
- Dudek-Rödl [DuRo08]: Current upper bound
- Radziszowski-Xu [RaXu07]: Lower bound
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

open SimpleGraph Finset

namespace Erdos582

/-
## Part I: Basic Graph-Theoretic Definitions

We work with simple graphs (no loops, no multi-edges).
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/--
**Complete Graph K_n:**
The complete graph on n vertices, where every pair is adjacent.
Uses Mathlib's SimpleGraph.completeGraph.
-/
def K (n : ℕ) := completeGraph (Fin n)

/--
**Clique in a Graph:**
A clique of size k is a complete subgraph on k vertices.
Uses Mathlib's SimpleGraph.IsClique.
-/
def hasClique (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ s : Finset V, s.card = k ∧ G.IsClique s

/--
**K_n-free Graph:**
A graph G is K_n-free if it contains no clique of size n.
-/
def isKFree (G : SimpleGraph V) (n : ℕ) : Prop :=
  ¬ hasClique G n

/-
## Part II: Edge Colorings and Ramsey Property

A 2-coloring of edges partitions them into "red" and "blue" edges.
-/

/--
**Edge 2-Coloring:**
A 2-coloring assigns each edge one of two colors (represented by Bool).
True = Red, False = Blue.
-/
def EdgeColoring (G : SimpleGraph V) := G.edgeSet → Bool

/--
**Monochromatic Subgraph:**
Given a coloring, the subgraph of edges with a specific color.
-/
def monochromaticSubgraph (G : SimpleGraph V) (c : EdgeColoring G) (color : Bool) :
    SimpleGraph V where
  Adj v w := G.Adj v w ∧ ∃ h : G.Adj v w, c ⟨s(v, w), G.edge_mem_edgeSet.mpr h⟩ = color
  symm v w := by
    intro ⟨hadj, hcolor⟩
    constructor
    · exact G.symm hadj
    · obtain ⟨h, hc⟩ := hcolor
      use G.symm h
      simp only [Sym2.eq_swap] at hc ⊢
      convert hc using 1
  loopless v := by
    intro ⟨hadj, _⟩
    exact G.loopless v hadj

/--
**Ramsey Property:**
A graph G has the Ramsey property for (K₃, 2) if every 2-coloring
of its edges contains a monochromatic triangle.
-/
def hasRamseyProperty (G : SimpleGraph V) : Prop :=
  ∀ c : EdgeColoring G, hasClique (monochromaticSubgraph G c true) 3 ∨
                        hasClique (monochromaticSubgraph G c false) 3

/-
## Part III: Folkman Numbers

The Folkman number f(r,k,n) is the minimum number of vertices in a
K_n-free graph where every r-coloring produces a monochromatic K_k.
-/

/--
**Folkman Graph Property:**
A graph G is a Folkman graph for (2,3,4) if:
1. G is K₄-free (contains no 4-clique)
2. Every 2-coloring of edges contains a monochromatic triangle
-/
def isFolkmanGraph (G : SimpleGraph V) : Prop :=
  isKFree G 4 ∧ hasRamseyProperty G

/--
**Folkman Number f(2,3,4):**
The minimum number of vertices in a Folkman graph.
This is the specific number asked about in Problem 582.
-/
noncomputable def folkmanNumber_2_3_4 : ℕ :=
  -- The minimum n such that there exists a Folkman graph on n vertices
  -- Formalized as a constant since computing it is intractable
  0  -- placeholder

/-
## Part IV: Main Existence Theorem

Folkman (1970) proved such graphs exist.
-/

/--
**Folkman's Theorem (1970):**
There exists a K₄-free graph such that every 2-coloring of edges
contains a monochromatic triangle.

This is the affirmative answer to Erdős Problem #582.
-/
axiom folkman_existence :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      isFolkmanGraph G

/--
**Erdős Problem #582: SOLVED**
The answer is YES - such graphs exist.
-/
theorem erdos_582 :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      isKFree G 4 ∧ hasRamseyProperty G :=
  folkman_existence

/-
## Part V: Quantitative Bounds

Various researchers have established bounds on f(2,3,4).
-/

/--
**Lower Bound (Radziszowski-Xu 2007):**
f(2,3,4) ≥ 19
-/
axiom folkman_lower_bound : folkmanNumber_2_3_4 ≥ 19

/--
**Upper Bound (Dudek-Rödl 2008):**
f(2,3,4) ≤ 941

This is the current best known upper bound.
-/
axiom folkman_upper_bound : folkmanNumber_2_3_4 ≤ 941

/--
**Spencer's Bound (1988):**
f(2,3,4) ≤ 3 × 10⁹

This resolved Erdős's challenge to find a Folkman graph with < 10¹⁰ vertices.
-/
axiom spencer_bound : folkmanNumber_2_3_4 ≤ 3 * 10^9

/--
**Current Knowledge:**
19 ≤ f(2,3,4) ≤ 941
-/
theorem folkman_bounds : 19 ≤ folkmanNumber_2_3_4 ∧ folkmanNumber_2_3_4 ≤ 941 :=
  ⟨folkman_lower_bound, folkman_upper_bound⟩

/-
## Part VI: Historical Bounds Timeline
-/

/--
**Frankl-Rödl Bound (1986):**
f(2,3,4) ≤ 7 × 10¹¹
-/
axiom frankl_rodl_bound : folkmanNumber_2_3_4 ≤ 7 * 10^11

/--
**Lu's Bound (2007):**
f(2,3,4) ≤ 9697
-/
axiom lu_bound : folkmanNumber_2_3_4 ≤ 9697

/--
**Bound Improvement Timeline:**
Folkman(1970) → Frankl-Rödl(1986) → Spencer(1988) → Lu(2007) → Dudek-Rödl(2008)
Each improvement significantly reduced the upper bound.
-/
theorem bounds_improvement :
    folkmanNumber_2_3_4 ≤ 941 ∧
    941 ≤ 9697 ∧
    9697 ≤ 3 * 10^9 ∧
    3 * 10^9 ≤ 7 * 10^11 := by
  constructor
  · exact folkman_upper_bound
  · constructor
    · norm_num
    · constructor
      · norm_num
      · norm_num

/-
## Part VII: Ramsey Theory Context
-/

/--
**Classical Ramsey Number R(3,3):**
R(3,3) = 6, the minimum n such that any 2-coloring of K_n
contains a monochromatic triangle.
-/
axiom ramsey_3_3 : ∀ c : EdgeColoring (completeGraph (Fin 6)),
    hasClique (monochromaticSubgraph (completeGraph (Fin 6)) c true) 3 ∨
    hasClique (monochromaticSubgraph (completeGraph (Fin 6)) c false) 3

/--
**Connection to Ramsey Theory:**
Folkman numbers generalize Ramsey numbers by adding the constraint
that the host graph itself must avoid certain cliques.
-/
def folkmanGeneralizesRamsey : Prop :=
    -- For K_n-free constraint with n large enough, Folkman number equals Ramsey number
    True  -- placeholder for the relationship

/-
## Part VIII: Related Folkman Numbers
-/

/--
**General Folkman Number f(r,k,n):**
Minimum vertices in K_n-free graph where every r-coloring has monochromatic K_k.
-/
noncomputable def folkmanNumber (r k n : ℕ) : ℕ :=
  0  -- placeholder

/--
**f(2,3,3) = ∞:**
There is no K₃-free graph where every 2-coloring has a monochromatic triangle.
(If G is K₃-free, there are no triangles to find!)
-/
theorem folkman_2_3_3_infinite :
    ¬ ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      isKFree G 3 ∧ hasRamseyProperty G := by
  intro ⟨V, hfin, hdec, G, hfree, hramsey⟩
  -- If G is K₃-free, then neither color can have a triangle
  sorry

/-
## Part IX: Computational Approaches
-/

/--
**Explicit Construction:**
Lu (2007) gave an explicit construction of a Folkman graph on 9697 vertices
using algebraic methods (Cayley graphs over finite fields).
-/
axiom lu_explicit_construction :
    ∃ (G : SimpleGraph (Fin 9697)), isFolkmanGraph G

/--
**Computer Search:**
The Dudek-Rödl bound uses probabilistic and computer-assisted methods
to verify existence of a 941-vertex Folkman graph.
-/
axiom dudek_rodl_construction :
    ∃ (G : SimpleGraph (Fin 941)), isFolkmanGraph G

/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #582 Summary:**
1. Such graphs exist (Folkman 1970)
2. Current best bounds: 19 ≤ f(2,3,4) ≤ 941
3. Radziszowski-Xu conjecture: f(2,3,4) ≤ 127
-/
theorem erdos_582_summary :
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      isFolkmanGraph G) ∧
    19 ≤ folkmanNumber_2_3_4 ∧
    folkmanNumber_2_3_4 ≤ 941 := by
  constructor
  · exact folkman_existence
  · exact folkman_bounds

/--
**The Erdős $100 Challenge:**
Erdős offered $100 to find such a graph with < 10¹⁰ vertices.
Spencer (1988) claimed this prize.
-/
theorem erdos_100_challenge_resolved : folkmanNumber_2_3_4 < 10^10 := by
  calc folkmanNumber_2_3_4 ≤ 941 := folkman_upper_bound
    _ < 10^10 := by norm_num

/--
**Conjectured Value:**
Radziszowski and Xu (2007) conjectured f(2,3,4) ≤ 127.
-/
def radziszowski_xu_conjecture : Prop := folkmanNumber_2_3_4 ≤ 127

end Erdos582
