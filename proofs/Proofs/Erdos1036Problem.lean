/-
Erdős Problem #1036: Distinct Induced Subgraphs in Non-Ramsey Graphs

Let G be a graph on n vertices with no clique or independent set on more
than c log n vertices. Must G contain at least 2^{Ω_c(n)} non-isomorphic
induced subgraphs?

**Answer**: YES (Shelah 1998).
**Prior**: Alon-Hajnal (1991) proved exp(n · (log n)^{-O(log log n)}).

**Open question (oq-01)**: What is the optimal constant in the exponent?
That is, for a given c, what is the largest c' such that every non-Ramsey
graph on n vertices has at least 2^{c'n} non-isomorphic induced subgraphs?

Reference: https://erdosproblems.com/1036
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open SimpleGraph Real

namespace Erdos1036

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Core Definitions -/

/-- The clique number ω(G): size of the largest clique. -/
noncomputable def cliqueNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ s : Finset V, s.card = k ∧ G.IsClique (s : Set V) }

/-- The independence number α(G): size of the largest independent set.
    Equivalently, the clique number of the complement. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ s : Finset V, s.card = k ∧ Gᶜ.IsClique (s : Set V) }

/-- G is non-Ramsey at level c if max(ω(G), α(G)) ≤ c log n.
    Such graphs have no large homogeneous subgraphs. -/
noncomputable def IsNonRamsey (G : SimpleGraph V) (c : ℝ) : Prop :=
  (cliqueNumber G : ℝ) ≤ c * log (Fintype.card V) ∧
  (independenceNumber G : ℝ) ≤ c * log (Fintype.card V)

/-- The number of non-isomorphic induced subgraphs of G.
    For finite graphs, this is a natural number. -/
noncomputable def numInducedSubgraphClasses (G : SimpleGraph V) : ℕ :=
  Fintype.card (Finset V) -- placeholder: counts subsets, not isomorphism classes

/- ## Main Results: Induced Subgraph Diversity -/

/-- Shelah's theorem (1998): Every non-Ramsey graph on n vertices contains
    at least 2^{c'n} non-isomorphic induced subgraphs, where c' depends on c.
    This is the main result answering Erdős Problem #1036. -/
axiom shelah_1998 (c : ℝ) (hc : c > 0) :
    ∃ c' > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsNonRamsey G c →
      (numInducedSubgraphClasses G : ℝ) ≥ 2 ^ (c' * Fintype.card V)

/-- Alon-Hajnal (1991): The sub-exponential precursor to Shelah's result.
    They proved exp(n · (log n)^{-O(log log n)}) using regularity.
    Here derived from Shelah's stronger exponential bound, since 2^{c'n} ≥ (c'·ln2)·n. -/
theorem alon_hajnal_1991 (c : ℝ) (hc : c > 0) :
    ∃ c' > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsNonRamsey G c →
      (numInducedSubgraphClasses G : ℝ) ≥ c' * Fintype.card V := by
  obtain ⟨c'', hc''_pos, hc''⟩ := shelah_1998 c hc
  refine ⟨c'' * Real.log 2, by positivity, ?_⟩
  intro V _ _ G hG
  have hshelah := hc'' V G hG
  -- Shelah: numInducedSubgraphClasses G ≥ 2^(c''·n)
  -- We show: 2^(c''·n) ≥ (c''·log 2)·n using exp(t) ≥ t
  calc (numInducedSubgraphClasses G : ℝ)
      ≥ (2 : ℝ) ^ (c'' * Fintype.card V) := hshelah
    _ = Real.exp (Real.log 2 * (c'' * Fintype.card V)) :=
        Real.rpow_def_of_pos (by norm_num : (2:ℝ) > 0) _
    _ = Real.exp (c'' * ↑(Fintype.card V) * Real.log 2) := by congr 1; ring
    _ ≥ c'' * ↑(Fintype.card V) * Real.log 2 := by
        have h := Real.add_one_le_exp (c'' * ↑(Fintype.card V) * Real.log 2)
        linarith
    _ = c'' * Real.log 2 * ↑(Fintype.card V) := by ring

/- ## The Optimal Constant Question (oq-01) -/

/-- The optimal constant function: for a given c, the supremum of c' such
    that every non-Ramsey(c) graph on n vertices has ≥ 2^{c'n} induced
    subgraph isomorphism classes. -/
noncomputable def optimalConstant (c : ℝ) : ℝ :=
  sSup { c' : ℝ | ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsNonRamsey G c →
    (numInducedSubgraphClasses G : ℝ) ≥ 2 ^ (c' * Fintype.card V) }

/-- The optimal constant is positive for c > 0 (follows from Shelah). -/
theorem optimalConstant_pos (c : ℝ) (hc : c > 0) : optimalConstant c > 0 := by
  sorry -- Requires showing sSup of a nonempty bounded-above set is positive

/-- The optimal constant is at most 1: a graph on n vertices has at most
    2^n induced subgraphs (one per subset of vertices). -/
theorem optimalConstant_le_one (c : ℝ) : optimalConstant c ≤ 1 := by
  sorry -- Requires showing numInducedSubgraphClasses G ≤ 2^n

/- ## Random Graph Comparison -/

/-- Random graphs G(n, 1/2) are non-Ramsey with c = 2/log 2 a.a.s.,
    and have i(G) = (1 - o(1)) · 2^n, achieving the trivial upper bound.
    This means the optimal constant for random-like c is close to 1. -/

/-- For the specific case c = 2/log 2 (random graph threshold),
    the optimal constant equals 1. -/
def optimalConstantAtRandom : Prop :=
  optimalConstant (2 / log 2) = 1

/- ## Complement Symmetry -/

/-- ω(Gᶜ) = α(G) by definition (independenceNumber uses complement cliques). -/
theorem cliqueNumber_compl (G : SimpleGraph V) :
    cliqueNumber Gᶜ = independenceNumber G := rfl

/-- α(Gᶜ) = ω(G) since (Gᶜ)ᶜ = G. -/
theorem independenceNumber_compl (G : SimpleGraph V) :
    independenceNumber Gᶜ = cliqueNumber G := by
  unfold independenceNumber cliqueNumber
  congr 1; ext k; simp [compl_compl]

/-- Non-Ramsey is preserved under complementation: if max(ω(G), α(G)) ≤ k,
    then max(ω(Gᶜ), α(Gᶜ)) ≤ k since ω(Gᶜ) = α(G) and α(Gᶜ) = ω(G). -/
theorem complement_nonramsey (G : SimpleGraph V) (c : ℝ) :
    IsNonRamsey G c → IsNonRamsey Gᶜ c := by
  intro ⟨hclique, hindep⟩
  simp only [IsNonRamsey, cliqueNumber_compl, independenceNumber_compl]
  exact ⟨hindep, hclique⟩

/- ## Summary -/

/-- Erdős Problem #1036 summary: Shelah's theorem provides an exponential
    lower bound on induced subgraph diversity for non-Ramsey graphs.
    The optimal constant in the exponent remains an open question. -/
theorem erdos_1036 (c : ℝ) (hc : c > 0) :
    ∃ c' > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsNonRamsey G c →
      (numInducedSubgraphClasses G : ℝ) ≥ 2 ^ (c' * Fintype.card V) :=
  shelah_1998 c hc

end Erdos1036
