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
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Fintype.Basic

open Cardinal SimpleGraph

namespace Erdos736

/-
## Part I: Basic Definitions
-/

/--
**Chromatic number of a simple graph:**
The minimum number of colors needed to properly color the vertices.
-/
noncomputable def chromaticNumber (V : Type) (G : SimpleGraph V) : Cardinal :=
  sInf { κ : Cardinal | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) }

/--
**Finite subgraph:**
The subgraph of `G` induced by a finite set of vertices.
-/
def isFiniteSubgraph {V : Type} (G : SimpleGraph V) (H : Subgraph G) : Prop :=
  ∃ (S : Finset V), H = (⊤ : G.Subgraph).induce (↑S : Set V)

/--
**Subgraph embedding:**
H is isomorphic to a subgraph of G.
-/
def isSubgraphOf {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (f : V → W), Function.Injective f ∧
    ∀ v₁ v₂ : V, H.Adj v₁ v₂ → G.Adj (f v₁) (f v₂)

/--
**Finite subgraph class:**
The class of all finite subgraphs of a graph G.
-/
def finiteSubgraphClass {V : Type} (G : SimpleGraph V) :
    Set (Σ (n : ℕ), SimpleGraph (Fin n)) :=
  { ⟨n, H⟩ | ∃ (S : Finset V) (e : S ≃ Fin n),
    ∀ i j : Fin n, H.Adj i j ↔ G.Adj (e.symm i) (e.symm j) }

/-
## Part II: The Taylor Conjecture
-/

/--
**Walter Taylor's Conjecture:**
If G has chromatic number ℵ₁, then for every cardinal m, there exists
a graph G_m with χ(G_m) = m whose finite subgraphs are all subgraphs of G.
-/
def TaylorConjecture : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    chromaticNumber V G = aleph 1 →
    ∀ (m : Cardinal),
      ∃ (W : Type) (H : SimpleGraph W),
        chromaticNumber W H = m ∧
        ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
          isSubgraphOf F H → isSubgraphOf F G

/--
**Generalized Taylor Conjecture:**
Same as above but for any uncountable cardinal κ.
-/
def GeneralizedTaylorConjecture : Prop :=
  ∀ (κ : Cardinal), Cardinal.IsRegular κ → κ > aleph 0 →
    ∀ (V : Type) (G : SimpleGraph V),
      chromaticNumber V G = κ →
      ∀ (m : Cardinal),
        ∃ (W : Type) (H : SimpleGraph W),
          chromaticNumber W H = m ∧
          ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
            isSubgraphOf F H → isSubgraphOf F G

/-
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
  ∃ (V : Type) (G : SimpleGraph V),
    chromaticNumber V G = aleph α ∧
    finiteSubgraphClass G ⊆ F

/--
**Erdős's General Question:**
Characterize which families F_α of finite graphs are realizable at ℵ_α.
-/
def ErdosGeneralQuestion : Prop :=
  ∃ (characterization : FiniteGraphFamily → Ordinal → Prop),
    ∀ F α, characterization F α ↔ realizableAt F α

/-
## Part IV: The Komjáth-Shelah Consistency Result
-/

/-
**Komjáth-Shelah (2005):**
It is consistent with ZFC that there exists a graph G with χ(G) = ℵ₁
such that any graph H whose finite subgraphs are all subgraphs of G
satisfies χ(H) ≤ ℵ₂.

**The conjecture is independent:**
Taylor's conjecture cannot be decided in ZFC alone.

(These are meta-mathematical consistency/independence results, not ZFC
theorems; they are recorded here as prose rather than as Lean declarations.)
-/

/-
## Part V: Related Concepts

**De Bruijn-Erdős theorem (finite version):**
If every finite subgraph of G is k-colorable, then G is k-colorable.
(This requires the axiom of choice.) Mathlib does not currently provide
this compactness theorem; it is the key missing ingredient for `finite_case`.

**Compactness in graph coloring:**
The chromatic number of a graph is determined by its finite subgraphs
in a limiting sense.

**Chromatic number and cardinal arithmetic:**
For infinite graphs, chromatic number interacts with cardinal arithmetic.
-/

/-
## Part VI: Special Cases

**Countable chromatic number:**
For graphs with χ(G) = ℵ₀, the Taylor question is easier.

**Finite case is trivial (informal):**
For finite chromatic number, inheritance is straightforward in principle —
see `finite_case` below for the precise statement.
-/
/--
**Finite chromatic number case.**
If `χ(G) = k` (finite), then for every `m ≤ k` there is a graph `H` with
`χ(H) = m` all of whose finite subgraphs embed into `G`.

The mathematically clean construction takes `H` to be an induced subgraph of
`G` on a suitable vertex subset `S`, so that finite subgraphs of `H` embed
into `G` for free. The remaining content is an *intermediate-value* property:
some induced subgraph attains chromatic number exactly `m` for each
`0 ≤ m ≤ k`. Establishing this needs (i) a finite subgraph witnessing
`χ = k`, which is the **de Bruijn-Erdős compactness theorem** (not yet in
Mathlib), and (ii) a vertex-deletion continuity step. The boundary cases
`m = 0` (`H = ⊥` on an empty type) and `m = k` (`H = G`) are immediate; the
intermediate cases are the obstruction. Left as `sorry` pending the missing
compactness infrastructure.
-/
theorem finite_case (V : Type) (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber V G = k →
    ∀ m ≤ k, ∃ (W : Type) (H : SimpleGraph W),
      chromaticNumber W H = m ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
        isSubgraphOf F H → isSubgraphOf F G := by
  intro _ _ _
  sorry

/-
## Part VII: Summary
-/

/--
**Summary of the problem:**
-/
theorem erdos_736_summary : TaylorConjecture ↔ TaylorConjecture :=
  Iff.rfl

end Erdos736
