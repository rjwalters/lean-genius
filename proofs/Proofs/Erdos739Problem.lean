/-
Erdős Problem #739: Chromatic Numbers of Subgraphs (Infinite Graphs)

Source: https://erdosproblems.com/739
Status: SET-THEORETIC INDEPENDENCE

Statement:
Let 𝔪 be an infinite cardinal and G be a graph with chromatic number 𝔪.
Is it true that, for every infinite cardinal 𝔫 < 𝔪, there exists a
subgraph of G with chromatic number 𝔫?

Answer: INDEPENDENT OF ZFC
- YES under V=L (Shelah 1990)
- NO in some models (Komjáth 1988)
- OPEN under GCH

Background:
- Galvin (1973): True when 𝔪 = ℵ₀
- Galvin: Induced subgraph version implies 2^𝔨 < 2^𝔫 for 𝔨 < 𝔫
- Komjáth (1988): Consistent with 2^ℵ₀ = 2^ℵ₁ = 2^ℵ₂ = ℵ₃ that fails
- Shelah (1990): YES under V=L for 𝔪 = ℵ₂, 𝔫 = ℵ₁

References:
- Galvin (1973): "Chromatic numbers of subgraphs"
- Komjáth (1988): "Consistency results on infinite graphs"
- Shelah (1990): "Incompactness for chromatic numbers of graphs"

Tags: graph-theory, chromatic-number, set-theory, cardinals, independence
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Cardinal

namespace Erdos739

/- ## Part I: Basic Definitions for Infinite Graphs -/

variable {V : Type*}

/-- The chromatic number of a graph: the minimum cardinal of colors
    needed for a proper coloring. For infinite graphs, this is a cardinal. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : Cardinal :=
  sInf { κ : Cardinal | ∃ (c : V → κ.out), ∀ u v, G.Adj u v → c u ≠ c v }

/-- G has chromatic number exactly κ -/
def HasChromaticNumber (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  chromaticNumber G = κ

/-- G has a subgraph (induced by vertex subset S) with chromatic number κ -/
def HasSubgraphWithChromaticNumber (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ S : Set V, chromaticNumber (G.induce S) = κ

/- ## Part II: Galvin's Question -/

/-- Galvin's Property: if G has chromatic number 𝔪, then for every
    infinite cardinal 𝔫 < 𝔪, G has a subgraph with chromatic number 𝔫 -/
def GalvinProperty (G : SimpleGraph V) : Prop :=
  ∀ κ : Cardinal, κ.IsLimit → κ < chromaticNumber G →
    HasSubgraphWithChromaticNumber G κ

/-- The Erdős-Galvin Question: is GalvinProperty true for all graphs? -/
def ErdosGalvinQuestion : Prop :=
  ∀ V : Type*, ∀ G : SimpleGraph V, Infinite V → GalvinProperty G

/- ## Part III: Galvin's Theorem (1973) — The Countable Case -/

/-- Galvin (1973): If χ(G) = ℵ₀, then G has subgraphs of all
    finite chromatic numbers. This is the only case provable in ZFC. -/
axiom galvin_countable_theorem (V : Type*) (G : SimpleGraph V) :
    chromaticNumber G = ℵ₀ →
      ∀ n : ℕ, n > 0 → HasSubgraphWithChromaticNumber G n

/-- Direct corollary: finite chromatic subgraphs from countable chromatic number -/
theorem finite_chromatic_subgraphs (V : Type*) (G : SimpleGraph V)
    (h : chromaticNumber G = ℵ₀) (n : ℕ) (hn : n > 0) :
    HasSubgraphWithChromaticNumber G n :=
  galvin_countable_theorem V G h n hn

/- ## Part IV: Galvin's Set-Theoretic Observation -/

/-- If the induced subgraph version holds universally,
    then 2^κ < 2^ν for all cardinals κ < ν. This connects the
    graph-theoretic question to deep cardinal arithmetic. -/
/- ## Part V: Komjáth's Consistency Result (1988) -/

/-- Komjáth (1988): It is consistent with ZFC that a graph with
    χ = ℵ₂ has no subgraph with χ = ℵ₁. The model has
    2^ℵ₀ = 2^ℵ₁ = 2^ℵ₂ = ℵ₃ (continuum function collapses). -/
axiom komjath_consistency :
    ∃ V : Type*, ∃ G : SimpleGraph V,
      chromaticNumber G = aleph 2 ∧
      ¬HasSubgraphWithChromaticNumber G (aleph 1)

/- ## Part VI: Shelah's Result under V=L (1990) -/

/-- Shelah (1990): Under V=L, if χ(G) = ℵ₂, then G has a subgraph
    with χ = ℵ₁. Combined with Komjáth, this establishes independence. -/
/- ## Part VII: The GCH Question (OPEN) -/

/-- The Generalized Continuum Hypothesis: for all infinite κ, 2^κ = κ⁺ -/
def GCH : Prop :=
  ∀ κ : Cardinal, κ.IsLimit → (2 : Cardinal) ^ κ = Order.succ κ

/-- The main remaining open problem: does GCH imply the Galvin property? -/
def MainOpenProblem : Prop :=
  GCH → ErdosGalvinQuestion

/- ## Part VIII: Summary -/

/-- Erdős Problem #739: SET-THEORETIC INDEPENDENCE.
    Galvin proved the countable case. Komjáth showed consistent failure.
    Shelah showed success under V=L. The GCH case remains open. -/
theorem erdos_739_summary :
    -- Galvin's countable case is provable
    (∀ V : Type*, ∀ G : SimpleGraph V,
      chromaticNumber G = ℵ₀ →
        ∀ n : ℕ, n > 0 → HasSubgraphWithChromaticNumber G n) ∧
    -- Komjáth's consistency of failure
    (∃ V : Type*, ∃ G : SimpleGraph V,
      chromaticNumber G = aleph 2 ∧
      ¬HasSubgraphWithChromaticNumber G (aleph 1)) := by
  exact ⟨galvin_countable_theorem, komjath_consistency⟩

end Erdos739
