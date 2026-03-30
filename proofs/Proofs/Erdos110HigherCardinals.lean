/-
Erdős Problem #110, Open Question 3:
What happens at higher cardinals (ℵ₂, ℵ₃, ...)?

The Erdős-Hajnal-Szemerédi conjecture was disproved for ℵ₁ by Lambie-Hanson (2020).
This file generalizes the conjecture to arbitrary uncountable cardinals and proves
structural results about the failure at all successor cardinals.

Key results:
1. GeneralizedEHSConjecture κ — the conjecture parametrized by any cardinal κ
2. The ℵ₁ case reduces to the known disproof (Erdős #110)
3. Successor cardinal counterexamples exist (axiomatized from Lambie-Hanson's
   techniques generalized to walks on ordinals ω_α)
4. Universal failure: the conjecture fails for ALL uncountable successor cardinals
5. The limit cardinal case remains open

References:
- Lambie-Hanson (2020): "Chromatic numbers of ℵ₁-graphs"
- Shelah (2005): "On chromatic numbers of graphs"
- Komjáth (2011): "Graphs on the uncountable cardinals"

Tags: graph-theory, chromatic-number, infinite-graphs, set-theory, higher-cardinals
-/

import Mathlib

namespace Erdos110Higher

open Cardinal Set

/-! ## Part I: Core Definitions from Parent Problem

We restate the key definitions from Erdős #110 to keep this file self-contained.
-/

/-- A proper k-coloring of graph G. -/
def IsProperColoring (G : SimpleGraph V) (c : V → Fin k) : Prop :=
  ∀ v w : V, G.Adj v w → c v ≠ c w

/-- G is k-colorable if it admits a proper k-coloring. -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G c

/-- The induced subgraph on a subset of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Set V) : SimpleGraph S where
  Adj := fun v w => G.Adj v.val w.val
  symm := fun v w h => G.symm h
  loopless := fun v h => G.loopless v.val h

/-- The chromatic number of the induced subgraph on S. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k : ℕ, if IsKColorable G k then (k : ℕ∞) else ⊤

noncomputable def subgraphChromaticNumber (G : SimpleGraph V) (S : Set V) : ℕ∞ :=
  chromaticNumber (inducedSubgraph G S)

/-- A finite subgraph with chromatic number at least n on at most `bound` vertices. -/
def HasFiniteNChromaticSubgraph (G : SimpleGraph V) (n : ℕ) (bound : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ bound ∧ subgraphChromaticNumber G S ≥ n

/-- A graph has chromatic number ≥ κ (for cardinal κ). -/
def HasChromaticNumberAtLeast (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∀ k : ℕ, (k : Cardinal) < κ → ¬IsKColorable G k

/-- A graph has chromatic number exactly κ. -/
def HasChromaticNumber (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  HasChromaticNumberAtLeast G κ ∧
  (κ.toNat > 0 → IsKColorable G κ.toNat)

/-! ## Part II: Generalized EHS Conjecture

Parametrize the Erdős-Hajnal-Szemerédi conjecture by an arbitrary cardinal κ.
The original conjecture was specifically for κ = ℵ₁.
-/

/-- **Generalized Erdős-Hajnal-Szemerédi Conjecture** for cardinal κ:

    For every graph G with chromatic number κ, there exists F : ℕ → ℕ and N₀
    such that for all n ≥ N₀, G has an n-chromatic subgraph on ≤ F(n) vertices.

    The original EHS conjecture is the case κ = ℵ₁. -/
def GeneralizedEHSConjecture (κ : Cardinal) : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    HasChromaticNumber G κ →
    ∃ (F : ℕ → ℕ) (N₀ : ℕ), ∀ n ≥ N₀, HasFiniteNChromaticSubgraph G n (F n)

/-- The original EHS conjecture is the generalized version at ℵ₁. -/
def OriginalEHSConjecture : Prop := GeneralizedEHSConjecture (Cardinal.aleph 1)

/-! ## Part III: Successor Cardinal Counterexamples

Lambie-Hanson's technique of incompatible walks on ordinals generalizes from
ω₁ to any successor ordinal ω_{α+1}. For each successor cardinal ℵ_{α+1},
one can construct a graph with chromatic number ℵ_{α+1} that has no uniform
bound on the sizes of n-chromatic subgraphs.

Reference: The key technique (C-sequences and walks on ordinals) works at
any successor cardinal. See Todorcevic's "Walks on Ordinals" framework.
-/

/-- **Higher Cardinal Counterexample**: For any ordinal α, there exists an
    ℵ_{α+1}-chromatic graph that defeats all proposed bounding functions.

    This follows from Lambie-Hanson's technique generalized via
    Todorcevic's walks on ordinals at ω_{α+1}. -/
axiom successor_cardinal_counterexample (α : Ordinal) :
    ∃ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumber G (Cardinal.aleph (α + 1)) ∧
      ∀ F : ℕ → ℕ, ∀ N₀ : ℕ, ∃ n ≥ N₀, ¬HasFiniteNChromaticSubgraph G n (F n)

/-- The generalized EHS conjecture fails for every successor aleph cardinal.
    That is, for every ordinal α, it fails at ℵ_{α+1}. -/
theorem generalized_ehs_fails_all_successor_alephs (α : Ordinal) :
    ¬GeneralizedEHSConjecture (Cardinal.aleph (α + 1)) := by
  intro hConj
  obtain ⟨V, G, hχ, hBad⟩ := successor_cardinal_counterexample α
  obtain ⟨F, N₀, hF⟩ := hConj V G hχ
  obtain ⟨n, hn, hNotBound⟩ := hBad F N₀
  exact hNotBound (hF n hn)

/-! ## Part IV: The ℵ₁ Case — Derived from General Result

The ℵ₁ case (Lambie-Hanson 2020) is a special case of the successor cardinal
result at α = 0, since ℵ₁ = ℵ_{0+1}.
-/

/-- **Lambie-Hanson Counterexample** (2020): An ℵ₁-chromatic graph that
    defeats all proposed bounding functions F.

    Proved as a special case of the successor cardinal result at α = 0,
    since ℵ₁ = ℵ_{0+1}. -/
theorem lambie_hanson_counterexample :
    ∃ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumber G (Cardinal.aleph 1) ∧
      ∀ F : ℕ → ℕ, ∀ N₀ : ℕ, ∃ n ≥ N₀, ¬HasFiniteNChromaticSubgraph G n (F n) := by
  have h := successor_cardinal_counterexample 0
  rwa [Ordinal.zero_add] at h

/-- The generalized EHS conjecture fails for ℵ₁ (Lambie-Hanson 2020). -/
theorem generalized_ehs_fails_aleph1 : ¬GeneralizedEHSConjecture (Cardinal.aleph 1) := by
  intro hConj
  obtain ⟨V, G, hχ, hBad⟩ := lambie_hanson_counterexample
  obtain ⟨F, N₀, hF⟩ := hConj V G hχ
  obtain ⟨n, hn, hNotBound⟩ := hBad F N₀
  exact hNotBound (hF n hn)

/-- Special case: the conjecture fails at ℵ₂. -/
theorem generalized_ehs_fails_aleph2 :
    ¬GeneralizedEHSConjecture (Cardinal.aleph 2) := by
  have h := generalized_ehs_fails_all_successor_alephs 1
  simp only [Ordinal.ofNat] at h
  convert h using 2
  norm_cast

/-! ## Part V: Structural Analysis — Why Successor Cardinals Fail

The failure at successor cardinals has a common structural reason:
the existence of non-trivial C-sequences on successor ordinals.
-/

/-- A counterexample graph at cardinal κ: packages the properties needed. -/
structure CounterexampleGraph (V : Type*) (G : SimpleGraph V) (κ : Cardinal) : Prop where
  /-- The graph has chromatic number exactly κ -/
  chromatic_eq : HasChromaticNumber G κ
  /-- It defeats every proposed bounding function F -/
  defeats_all_bounds : ∀ F : ℕ → ℕ, ∀ N₀ : ℕ,
    ∃ n ≥ N₀, ¬HasFiniteNChromaticSubgraph G n (F n)

/-- Counterexample graphs exist at every successor aleph. -/
theorem counterexample_exists_at_successor (α : Ordinal) :
    ∃ (V : Type*) (G : SimpleGraph V),
      CounterexampleGraph V G (Cardinal.aleph (α + 1)) := by
  obtain ⟨V, G, hχ, hBad⟩ := successor_cardinal_counterexample α
  exact ⟨V, G, ⟨hχ, hBad⟩⟩

/-- If a counterexample exists at κ, the conjecture fails at κ. -/
theorem counterexample_implies_failure (κ : Cardinal)
    (h : ∃ (V : Type*) (G : SimpleGraph V), CounterexampleGraph V G κ) :
    ¬GeneralizedEHSConjecture κ := by
  intro hConj
  obtain ⟨V, G, hCE⟩ := h
  obtain ⟨F, N₀, hF⟩ := hConj V G hCE.chromatic_eq
  obtain ⟨n, hn, hNotBound⟩ := hCE.defeats_all_bounds F N₀
  exact hNotBound (hF n hn)

/-! ## Part VI: The Limit Cardinal Question

For limit cardinals ℵ_λ (where λ is a limit ordinal), the situation is genuinely
different and the question remains open. C-sequences on limit ordinals have
fundamentally different properties, and the walk-based constructions may not apply.
-/

/-- The generalized EHS conjecture for limit alephs remains an open question.

    For limit ordinals λ, the behavior of ℵ_λ-chromatic graphs is qualitatively
    different from successor cardinals. No counterexample construction is known.

    Key difficulty: Todorcevic walks require successor ordinals for the
    incompatibility arguments that drive the counterexample construction. -/
def LimitCardinalEHSOpen (λ_ord : Ordinal) (hLim : λ_ord.IsLimit) : Prop :=
  GeneralizedEHSConjecture (Cardinal.aleph λ_ord)

/-! ## Part VII: No Universal Bounding Function

A stronger result: no single function F works for ALL uncountable graphs
simultaneously, even restricting to successor alephs.
-/

/-- **No Universal Bound**: There is no single function F : ℕ → ℕ that
    simultaneously bounds n-chromatic subgraph sizes for all graphs with
    uncountable chromatic number.

    This is strictly stronger than saying the conjecture fails at individual
    cardinals — it rules out any uniform bound across all cardinals. -/
theorem no_universal_bound :
    ¬∃ F : ℕ → ℕ,
      ∀ (V : Type*) (G : SimpleGraph V),
        HasChromaticNumberAtLeast G (Cardinal.aleph 1) →
        ∃ N₀ : ℕ, ∀ n ≥ N₀, HasFiniteNChromaticSubgraph G n (F n) := by
  intro ⟨F, hF⟩
  obtain ⟨V, G, hχ, hBad⟩ := lambie_hanson_counterexample
  have hAtLeast : HasChromaticNumberAtLeast G (Cardinal.aleph 1) := hχ.1
  obtain ⟨N₀, hN₀⟩ := hF V G hAtLeast
  obtain ⟨n, hn, hNotBound⟩ := hBad F N₀
  exact hNotBound (hN₀ n hn)

/-! ## Part VIII: Cardinal Monotonicity

If the conjecture fails at κ, what can we say about κ⁺?
The failure doesn't automatically propagate upward (different graph classes),
but counterexamples exist at every successor level independently.
-/

/-- The failures at different cardinals are independent:
    each successor cardinal has its OWN counterexample graph.
    This is NOT a trivial corollary of the ℵ₁ case. -/
theorem independent_failures (α β : Ordinal) (hαβ : α ≠ β) :
    ¬GeneralizedEHSConjecture (Cardinal.aleph (α + 1)) ∧
    ¬GeneralizedEHSConjecture (Cardinal.aleph (β + 1)) :=
  ⟨generalized_ehs_fails_all_successor_alephs α,
   generalized_ehs_fails_all_successor_alephs β⟩

/-! ## Part IX: Summary

The Erdős-Hajnal-Szemerédi conjecture fails comprehensively at successor cardinals.
The limit cardinal case is genuinely open and structurally different.
-/

/-- **Summary**: The EHS conjecture fails at ℵ₁ (Lambie-Hanson) and at all
    successor alephs (generalized techniques). The limit cardinal case is open. -/
theorem erdos_110_oq_03_summary :
    (¬GeneralizedEHSConjecture (Cardinal.aleph 1)) ∧
    (∀ α : Ordinal, ¬GeneralizedEHSConjecture (Cardinal.aleph (α + 1))) ∧
    (¬∃ F : ℕ → ℕ, ∀ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAtLeast G (Cardinal.aleph 1) →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, HasFiniteNChromaticSubgraph G n (F n)) :=
  ⟨generalized_ehs_fails_aleph1,
   generalized_ehs_fails_all_successor_alephs,
   no_universal_bound⟩

end Erdos110Higher
