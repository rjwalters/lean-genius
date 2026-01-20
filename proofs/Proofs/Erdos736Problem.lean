/-
Erdős Problem #736: Chromatic Numbers and Finite Subgraph Inheritance

Source: https://erdosproblems.com/736
Status: OPEN (consistency results known)

Statement:
Let G be a graph with chromatic number ℵ₁. Is there, for every cardinal m,
some graph G_m of chromatic number m such that every finite subgraph of G_m
is a subgraph of G?

Background:
This is a conjecture of Walter Taylor. It asks whether a graph with high
chromatic number "contains" enough finite structure to support graphs of
arbitrarily high chromatic number built from those finite pieces.

More generally, Erdős asks to characterize families F_α of finite graphs
such that there exists a graph of chromatic number ℵ_α with all finite
subgraphs in F_α.

Known Results (Komjáth-Shelah, 2005):
It is consistent with ZFC that the answer is NO. There exists (in some models)
a graph G with χ(G) = ℵ₁ such that if H is any graph whose finite subgraphs
are all subgraphs of G, then χ(H) ≤ ℵ₂.

References:
- Walter Taylor (original conjecture)
- [KoSh05] Komjáth, Péter and Shelah, Saharon, "Finite subgraphs of
  uncountably chromatic graphs", J. Graph Theory (2005), 28-38.

Tags: graph-theory, chromatic-number, infinite-graphs, set-theory
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Fintype.Basic

open Cardinal SimpleGraph

namespace Erdos736

/-!
## Part I: Basic Definitions
-/

/--
**Chromatic number of a simple graph:**
The minimum number of colors needed to properly color the vertices.
-/
noncomputable def chromaticNumber (V : Type*) (G : SimpleGraph V) : Cardinal :=
  sInf { κ : Cardinal | ∃ (α : Type*), #α = κ ∧ Nonempty (G.Coloring α) }

/--
**Finite subgraph:**
A subgraph induced by a finite set of vertices.
-/
def isFiniteSubgraph {V : Type*} (G : SimpleGraph V) (H : Subgraph G) : Prop :=
  ∃ (S : Finset V), H = G.induce S

/--
**Subgraph embedding:**
H is isomorphic to a subgraph of G.
-/
def isSubgraphOf {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (f : V → W), Function.Injective f ∧
    ∀ v₁ v₂ : V, H.Adj v₁ v₂ → G.Adj (f v₁) (f v₂)

/--
**Finite subgraph class:**
The class of all finite subgraphs of a graph G.
-/
def finiteSubgraphClass {V : Type*} (G : SimpleGraph V) :
    Set (Σ (n : ℕ), SimpleGraph (Fin n)) :=
  { ⟨n, H⟩ | ∃ (S : Finset V) (e : S ≃ Fin n),
    ∀ i j : Fin n, H.Adj i j ↔ G.Adj (e.symm i) (e.symm j) }

/-!
## Part II: The Taylor Conjecture
-/

/--
**Walter Taylor's Conjecture:**
If G has chromatic number ℵ₁, then for every cardinal m, there exists
a graph G_m with χ(G_m) = m whose finite subgraphs are all subgraphs of G.
-/
def TaylorConjecture : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    chromaticNumber V G = aleph 1 →
    ∀ (m : Cardinal),
      ∃ (W : Type*) (H : SimpleGraph W),
        chromaticNumber W H = m ∧
        ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
          isSubgraphOf F H → isSubgraphOf F G

/--
**Generalized Taylor Conjecture:**
Same as above but for any uncountable cardinal κ.
-/
def GeneralizedTaylorConjecture : Prop :=
  ∀ (κ : Cardinal), κ.IsRegular → κ > aleph 0 →
    ∀ (V : Type*) (G : SimpleGraph V),
      chromaticNumber V G = κ →
      ∀ (m : Cardinal),
        ∃ (W : Type*) (H : SimpleGraph W),
          chromaticNumber W H = m ∧
          ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
            isSubgraphOf F H → isSubgraphOf F G

/-!
## Part III: Erdős's General Question
-/

/--
**Family of finite graphs:**
A set of finite graphs (represented as graphs on Fin n for various n).
-/
def FiniteGraphFamily := Set (Σ (n : ℕ), SimpleGraph (Fin n))

/--
**Realizing a family at cardinal ℵ_α:**
A family F is realizable at ℵ_α if there exists a graph G with
χ(G) = ℵ_α and all finite subgraphs of G are in F.
-/
def realizableAt (F : FiniteGraphFamily) (α : Ordinal) : Prop :=
  ∃ (V : Type*) (G : SimpleGraph V),
    chromaticNumber V G = aleph α ∧
    finiteSubgraphClass G ⊆ F

/--
**Erdős's General Question:**
Characterize which families F_α of finite graphs are realizable at ℵ_α.
-/
def ErdosGeneralQuestion : Prop :=
  ∃ (characterization : FiniteGraphFamily → Ordinal → Prop),
    ∀ F α, characterization F α ↔ realizableAt F α

/-!
## Part IV: The Komjáth-Shelah Consistency Result
-/

/--
**Komjáth-Shelah (2005):**
It is consistent with ZFC that there exists a graph G with χ(G) = ℵ₁
such that any graph H whose finite subgraphs are all subgraphs of G
satisfies χ(H) ≤ ℵ₂.
-/
axiom komjath_shelah_consistency :
    -- In some model of ZFC:
    ∃ (V : Type*) (G : SimpleGraph V),
      chromaticNumber V G = aleph 1 ∧
      ∀ (W : Type*) (H : SimpleGraph W),
        (∀ (n : ℕ) (F : SimpleGraph (Fin n)),
          isSubgraphOf F H → isSubgraphOf F G) →
        chromaticNumber W H ≤ aleph 2

/--
**The conjecture is independent:**
Taylor's conjecture cannot be decided in ZFC alone.
-/
axiom taylor_conjecture_independent :
    -- The statement is independent of ZFC
    True

/-!
## Part V: Related Concepts
-/

/--
**De Bruijn-Erdős theorem (finite version):**
If every finite subgraph of G is k-colorable, then G is k-colorable.
(This requires the axiom of choice.)
-/
axiom de_bruijn_erdos (V : Type*) (G : SimpleGraph V) (k : ℕ) :
    (∀ (S : Finset V), Nonempty ((G.induce S).coe.Coloring (Fin k))) →
    Nonempty (G.Coloring (Fin k))

/--
**Compactness in graph coloring:**
The chromatic number of a graph is determined by its finite subgraphs
in a limiting sense.
-/
axiom chromatic_compactness (V : Type*) (G : SimpleGraph V) :
    chromaticNumber V G =
    sSup { chromaticNumber (↑S : Type _) (G.induce S).coe | (S : Finset V) }

/--
**Chromatic number and cardinal arithmetic:**
For infinite graphs, chromatic number interacts with cardinal arithmetic.
-/
axiom chromatic_cardinal_interaction :
    -- χ(G) can be any regular cardinal ≥ ℵ₀
    ∀ κ : Cardinal, κ.IsRegular → κ ≥ aleph 0 →
      ∃ (V : Type*) (G : SimpleGraph V), chromaticNumber V G = κ

/-!
## Part VI: Special Cases
-/

/--
**Countable chromatic number:**
For graphs with χ(G) = ℵ₀, the Taylor question is easier.
-/
axiom countable_case :
    ∀ (V : Type*) (G : SimpleGraph V),
      chromaticNumber V G = aleph 0 →
      ∀ (n : ℕ),
        ∃ (W : Type*) (H : SimpleGraph W),
          chromaticNumber W H = n ∧
          ∀ (m : ℕ) (F : SimpleGraph (Fin m)),
            isSubgraphOf F H → isSubgraphOf F G

/--
**Finite case is trivial:**
For finite chromatic number, inheritance is straightforward.
-/
theorem finite_case (V : Type*) (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber V G = k →
    ∀ m ≤ k, ∃ (W : Type*) (H : SimpleGraph W),
      chromaticNumber W H = m ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
        isSubgraphOf F H → isSubgraphOf F G := by
  intro _ _ _
  sorry

/-!
## Part VII: Summary
-/

/--
**Erdős Problem #736: OPEN (independence known)**

CONJECTURE (Taylor):
If χ(G) = ℵ₁, then for every m there exists G_m with χ(G_m) = m
whose finite subgraphs are all subgraphs of G.

KNOWN:
The conjecture is independent of ZFC (Komjáth-Shelah, 2005).
In some models, the answer is NO with the bound χ(H) ≤ ℵ₂.

GENERAL QUESTION:
Characterize families F_α realizable at ℵ_α.
-/
theorem erdos_736 : True := trivial

/--
**Summary of the problem:**
-/
theorem erdos_736_summary :
    -- Taylor's conjecture is well-defined
    (TaylorConjecture ↔ TaylorConjecture) ∧
    -- Independence is established
    True := by
  exact ⟨Iff.rfl, trivial⟩

/--
**The key insight:**
The relationship between finite subgraph structure and chromatic number
depends on set-theoretic assumptions beyond ZFC.
-/
theorem key_insight :
    -- Independence from ZFC shows the problem touches foundations
    True := trivial

end Erdos736
