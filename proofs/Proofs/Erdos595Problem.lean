/-
Erdős Problem #595: Infinite Graphs and Countable Triangle-Free Decomposition

Source: https://erdosproblems.com/595
Status: OPEN
Prize: $250

Statement:
Is there an infinite graph G which contains no K₄ and is not the union of
countably many triangle-free graphs?

Background:
This is a problem of Erdős and Hajnal concerning the chromatic properties
of infinite graphs. It asks whether the "local" constraint of being K₄-free
can coexist with a "global" resistance to decomposition into countably many
triangle-free parts.

Known Results:
- Folkman (1970) and Nešetřil-Rödl (1975) proved that for every finite n ≥ 1,
  there exists a K₄-free graph that is not the union of n triangle-free graphs.
- The infinite/countable case remains open.

Connection to Related Problems:
- Problem #582: Folkman numbers - finite analogue (SOLVED)
- Problem #596: General (G₁, G₂) decomposition pairs (OPEN)

References:
- Erdős-Hajnal: Original question
- Folkman [Fo70]: Finite case existence
- Nešetřil-Rödl [NeRo75]: Alternative proof of finite case
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.SetTheory.Cardinal.Basic

open SimpleGraph Finset Cardinal

namespace Erdos595

/- ## Part I: Basic Definitions

We work with simple graphs (undirected, no loops, no multi-edges).
-/

variable {V : Type*} [DecidableEq V]

/--
**Clique in a Graph:**
A clique of size k is a complete subgraph on k vertices.
-/
def hasCliqueInfinite (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ s : Set V, s.ncard = k ∧ G.IsClique s

/--
**K_n-free Graph:**
A graph G is K_n-free if it contains no clique of size n.
-/
def isKFreeInfinite (G : SimpleGraph V) (n : ℕ) : Prop :=
  ¬ hasCliqueInfinite G n

/--
**K₄-free Graph:**
A graph containing no complete graph on 4 vertices.
-/
def isK4Free (G : SimpleGraph V) : Prop := isKFreeInfinite G 4

/--
**Triangle-free Graph:**
A graph containing no complete graph on 3 vertices (no triangles).
-/
def isTriangleFree (G : SimpleGraph V) : Prop := isKFreeInfinite G 3

/- ## Part II: Graph Coverings and Unions -/

/--
**Subgraph Relation:**
H is a subgraph of G if every edge in H is also in G.
-/
def IsSubgraph (H G : SimpleGraph V) : Prop :=
  ∀ v w, H.Adj v w → G.Adj v w

/--
**Countable Union of Graphs:**
A graph G is a countable union of graphs from family F if every edge
of G belongs to some graph in F.
-/
def isCountableUnionOf (G : SimpleGraph V) (F : ℕ → SimpleGraph V) : Prop :=
  ∀ v w, G.Adj v w → ∃ n, (F n).Adj v w

/--
**Countable Triangle-Free Cover:**
G can be covered by countably many triangle-free graphs.
-/
def hasCountableTriangleFreeCover (G : SimpleGraph V) : Prop :=
  ∃ F : ℕ → SimpleGraph V,
    (∀ n, isTriangleFree (F n)) ∧
    (∀ n, IsSubgraph (F n) G) ∧
    isCountableUnionOf G F

/- ## Part III: The Main Conjecture

The Erdős-Hajnal question asks whether these two properties can coexist.
-/

/--
**Erdős Problem #595 (Conjecture):**
There exists an infinite K₄-free graph that cannot be expressed as
a countable union of triangle-free graphs.

Status: OPEN (as of 2024)
Prize: $250
-/
def erdos595_conjecture : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    Infinite V ∧
    isK4Free G ∧
    ¬ hasCountableTriangleFreeCover G

/- ## Part IV: Finite Analogues (Folkman-Nešetřil-Rödl)

While the infinite case is open, finite analogues are well understood.
-/

/--
**Finite n-Cover:**
G can be covered by exactly n triangle-free graphs.
-/
def hasFiniteTriangleFreeCover (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ F : Fin n → SimpleGraph V,
    (∀ i, isTriangleFree (F i)) ∧
    (∀ i, IsSubgraph (F i) G) ∧
    (∀ v w, G.Adj v w → ∃ i, (F i).Adj v w)

/--
**Folkman's Theorem (1970):**
For every n ≥ 1, there exists a finite K₄-free graph that cannot
be covered by n triangle-free graphs.

This establishes that finite resistance exists for every finite n.
-/
axiom folkman_finite_resistance (n : ℕ) (hn : n ≥ 1) :
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    isK4Free G ∧ ¬ hasFiniteTriangleFreeCover G n

/--
**Nešetřil-Rödl (1975):**
Alternative proof of finite resistance using Ramsey-type methods.
-/
axiom nesetril_rodl_finite_resistance (n : ℕ) (hn : n ≥ 1) :
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    isK4Free G ∧ ¬ hasFiniteTriangleFreeCover G n

/- ## Part V: Why the Infinite Case is Harder

The gap between finite and countably infinite is fundamental.
Having resistance to any finite cover does not automatically imply
resistance to a countable cover. A sequence of graphs G_n where
G_n resists n-covers could potentially be "combined" in a way
that admits a countable cover. This finite-to-countable gap is
the core difficulty of Problem 595.
-/

/--
**Problem 595 Reformulation:**
Does there exist a K₄-free graph with triangle-free chromatic number
strictly greater than ℵ₀?
-/
def problem595_reformulated : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    Infinite V ∧
    isK4Free G ∧
    ∀ F : ℕ → SimpleGraph V,
      (∀ n, isTriangleFree (F n)) →
      ¬ isCountableUnionOf G F

/- ## Part VI: Related Results -/

/--
**C₄-Free Special Case:**
Erdős and Hajnal proved: every C₄-free graph is a countable union of trees.
Since trees are triangle-free, this shows C₄-free graphs ARE countably coverable.
This contrasts with the K₄-free case which remains open.
-/
axiom c4_free_countable_trees :
  ∀ (V : Type) (G : SimpleGraph V),
    (¬ ∃ (a b c d : V), a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
      a ≠ c ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    hasCountableTriangleFreeCover G

/- ## Part VII: Summary -/

/--
**Finite Resistance Theorem:**
The finite version is completely settled - for every n, such graphs exist.
-/
theorem finite_case_complete :
  ∀ n : ℕ, n ≥ 1 →
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      isK4Free G ∧ ¬ hasFiniteTriangleFreeCover G n :=
  fun n hn => folkman_finite_resistance n hn

/--
**Erdős Problem #595: OPEN**

Is there an infinite graph G which contains no K₄ and is not the union
of countably many triangle-free graphs?

Prize: $250

Known:
- Finite resistance exists for every n (Folkman 1970, Nešetřil-Rödl 1975)
- C₄-free graphs ARE countably coverable (Erdős-Hajnal)
- The countable case for K₄-free graphs remains open
-/
theorem erdos_595_summary :
    (∀ n : ℕ, n ≥ 1 → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      isK4Free G ∧ ¬ hasFiniteTriangleFreeCover G n) ∧
    (∀ (V : Type) (G : SimpleGraph V),
      (¬ ∃ (a b c d : V), a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
        a ≠ c ∧ b ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
      hasCountableTriangleFreeCover G) :=
  ⟨folkman_finite_resistance, c4_free_countable_trees⟩

end Erdos595
