/-
Erdős Problem #1174: Monochromatic Cliques from Edge Colorings

Source: https://erdosproblems.com/1174
Status: OPEN (set-theoretic independence)
Reference: [Va99, 7.91]

Statement:
(a) Does there exist a graph G with no K₄ such that every edge colouring of G
    with countably many colours contains a monochromatic triangle (K₃)?

(b) Does there exist a graph G with no K_{ℵ₁} such that every edge colouring of G
    with countably many colours contains a monochromatic K_{ℵ₀}?

Key Results:
- This is a problem of Erdős and Hajnal
- Shelah showed that a graph possessing either property can consistently exist
  in certain set-theoretic models (i.e., the existence is consistent with ZFC)
- The problem asks whether such graphs exist in ZFC outright

Context:
This problem sits at the intersection of Ramsey theory and set theory.
By Ramsey's theorem, for any 2-coloring of K_ω (countably infinite complete graph),
there exists a monochromatic K_ω. This problem asks what happens when:
- We restrict the host graph (no K₄, or no K_{ℵ₁})
- We allow countably many colors (not just 2)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

open Cardinal SimpleGraph

namespace Erdos1174

/-
## Part I: Clique and Coloring Definitions
-/

/--
**Clique in a Graph:**
A set S of vertices forms a clique if every two distinct vertices in S are adjacent.
-/
def IsClique {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v w, v ∈ S → w ∈ S → v ≠ w → G.Adj v w

/--
**K₄-free Graph:**
A graph G is K₄-free if it contains no complete subgraph on 4 vertices.
-/
def IsK4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬(G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)

/--
**Clique-free for Cardinal κ:**
A graph G has no clique of cardinality κ.
No K_{ℵ₁} means no clique of size ℵ₁.
-/
def IsCliqueFreeCardinal {V : Type*} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∀ (S : Set V), IsClique G S → #S < κ

/--
**Symmetric Coloring:**
An edge coloring assigns colors to pairs of vertices, respecting symmetry.
-/
structure SymmetricColoring (V C : Type*) where
  color : V → V → C
  symm : ∀ v w, color v w = color w v

/-
## Part II: The Finite Question (Part a)
-/

/--
**Monochromatic Triangle:**
Three vertices form a monochromatic triangle under coloring f if
they are pairwise adjacent and all three edges have the same color.
-/
def HasMonochromaticTriangle {V : Type*} (G : SimpleGraph V)
    (f : V → V → ℕ) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
    f a b = f a c ∧ f a b = f b c

/--
**Erdős-Hajnal Property (Finite Version):**
A graph G has the EH-finite property if:
(1) G is K₄-free (no clique of size 4)
(2) Every edge coloring of G with countably many colors contains
    a monochromatic triangle (K₃)
-/
def ErdosHajnalFiniteProperty {V : Type*} (G : SimpleGraph V) : Prop :=
  IsK4Free G ∧
  ∀ (f : V → V → ℕ), (∀ v w, G.Adj v w → f v w = f w v) →
    HasMonochromaticTriangle G f

/--
**Erdős Problem #1174 (Part a):**
Does there exist a graph G that is K₄-free but has the property that
every countable edge coloring contains a monochromatic triangle?
-/
def erdos_1174a : Prop :=
  ∃ (V : Type*) (G : SimpleGraph V), ErdosHajnalFiniteProperty G

/-
## Part III: The Infinite Question (Part b)
-/

/--
**Monochromatic Countably Infinite Clique:**
Under coloring f, there exists a set S of vertices of cardinality ℵ₀
that forms a clique with all edges the same color.
-/
def HasMonochromaticAleph0Clique {V : Type*} (G : SimpleGraph V)
    (f : V → V → ℕ) : Prop :=
  ∃ (S : Set V) (c : ℕ),
    #S = Cardinal.aleph 0 ∧
    IsClique G S ∧
    ∀ v w, v ∈ S → w ∈ S → v ≠ w → f v w = c

/--
**Erdős-Hajnal Property (Infinite Version):**
A graph G has the EH-infinite property if:
(1) G has no clique of cardinality ℵ₁ (no K_{ℵ₁})
(2) Every edge coloring with countably many colors contains
    a monochromatic clique of cardinality ℵ₀ (a K_{ℵ₀})
-/
def ErdosHajnalInfiniteProperty {V : Type*} (G : SimpleGraph V) : Prop :=
  IsCliqueFreeCardinal G (Cardinal.aleph 1) ∧
  ∀ (f : V → V → ℕ), (∀ v w, G.Adj v w → f v w = f w v) →
    HasMonochromaticAleph0Clique G f

/--
**Erdős Problem #1174 (Part b):**
Does there exist a graph G with no K_{ℵ₁} such that every countable
edge coloring contains a monochromatic K_{ℵ₀}?
-/
def erdos_1174b : Prop :=
  ∃ (V : Type*) (G : SimpleGraph V), ErdosHajnalInfiniteProperty G

/-
## Part IV: Ramsey Theory Context
-/

/--
**Infinite Ramsey Theorem (2 colors):**
For any 2-coloring of edges of K_ω, there exists a monochromatic K_ω.
This uses the COMPLETE graph. Problem 1174 asks if the same holds
with restricted host graphs.
-/
/--
**Complete graph has the property trivially:**
K_ω (the complete graph on ℕ) satisfies the coloring property
by infinite Ramsey, but it contains cliques of all finite sizes,
so it is NOT K₄-free. This shows the constraint is essential.
-/
theorem complete_graph_not_k4free :
    ¬ IsK4Free (⊤ : SimpleGraph ℕ) := by
  intro h
  have : ¬(SimpleGraph.Adj ⊤ 0 1 ∧ SimpleGraph.Adj ⊤ 0 2 ∧ SimpleGraph.Adj ⊤ 0 3 ∧
            SimpleGraph.Adj ⊤ 1 2 ∧ SimpleGraph.Adj ⊤ 1 3 ∧ SimpleGraph.Adj ⊤ 2 3) := by
    exact h 0 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp [SimpleGraph.top_adj] at this

/-
## Part V: Partition Calculus Framework
-/

/--
**Partition Property (Finite Colors):**
G → (k)²_c means: for every c-coloring of edges of G,
there is a monochromatic k-clique.
-/
def partitionProperty {V : Type*} (G : SimpleGraph V)
    (k : ℕ) (numColors : ℕ) : Prop :=
  ∀ (f : V → V → Fin numColors), (∀ v w, G.Adj v w → f v w = f w v) →
    ∃ (S : Finset V), S.card = k ∧
      ∃ c : Fin numColors, ∀ v w, v ∈ (↑S : Set V) → w ∈ (↑S : Set V) → v ≠ w →
        G.Adj v w ∧ f v w = c

/--
**Nešetřil-Rödl Theorem (Context):**
For each fixed k, there exists a K₄-free graph G with G → (3)²_k.
This shows the finite-color version is achievable. The challenge
in Problem 1174 is extending to countably many colors.
-/
/-
## Part VI: Shelah's Consistency Results
-/

/- Shelah's consistency results:
Shelah showed that it is consistent with ZFC that graphs satisfying
either the finite property (part a) or the infinite property (part b)
exist. This means we cannot disprove existence in ZFC alone.
However, whether such graphs provably exist in ZFC remains open. -/

/-
## Part VII: Structural Observations
-/

/- K₄-free graphs can be triangle-rich:
Balanced complete tripartite graphs K_{n,n,n} are K₄-free
but contain n³ triangles. The Ramsey question asks whether
such triangle-richness can force monochromatic triangles
under countable edge colorings.

Relation between parts (a) and (b):
Part (b) is a natural infinite generalization of part (a).
A positive answer to (b) would yield structural results about
the Ramsey-theoretic forcing power of K_{ℵ₁}-free graphs. -/

/-
## Part VIII: Open Status and Summary
-/

/--
**Erdős Problem #1174: OPEN**
Both parts remain open in ZFC.

Summary of what is known:
1. For each fixed k, K₄-free graphs with G → (3)²_k exist (Nešetřil-Rödl)
2. Graphs satisfying either property consistently exist (Shelah)
3. Whether they exist in ZFC is unknown

The problem connects partition calculus, infinite Ramsey theory,
and set-theoretic independence.
-/
-- Problem remains OPEN in ZFC.

end Erdos1174
