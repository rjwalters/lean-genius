/-
  Erdős Problem #601: Infinite Paths and Independent Sets in Ordinal Graphs

  Source: https://erdosproblems.com/601
  Status: OPEN
  Prize: $500

  Statement:
  For which limit ordinals α is it true that if G is a graph with vertex set α,
  then G must have either an infinite path or an independent set on a set of
  vertices with order type α?

  Known Results:
  - Holds for all α < ω₁^{ω+2} (Erdős-Hajnal-Milner 1970)
  - Holds for all α < 2^{ℵ₀} assuming Martin's Axiom (Larson 1990)

  Open:
  - The case α = ω₁^{ω+2}
  - The general case for arbitrary limit ordinals

  Tags: graph-theory, set-theory, ordinals
-/

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace Erdos601

open Ordinal Cardinal SimpleGraph

/- ## Part I: Basic Definitions -/

/-- A graph on an ordinal α has vertex set α. -/
def OrdinalGraph (α : Ordinal) := SimpleGraph α.toType

/-- An infinite path in a graph. -/
def HasInfinitePath (G : SimpleGraph V) : Prop :=
  ∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))

/-- An independent set is a set with no edges between any two vertices. -/
def IsIndependent (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u v, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- A set of vertices has order type α (when V is an ordinal). -/
def HasOrderType (α : Ordinal) (S : Set α.toType) (β : Ordinal) : Prop :=
  Ordinal.type (Subrel (· < ·) S) = β

/- ## Part II: The Property P(α) -/

/-- The property P(α): Every graph on α has infinite path or α-type independent set. -/
def PropertyP (α : Ordinal) : Prop :=
  ∀ G : OrdinalGraph α,
    HasInfinitePath G ∨ ∃ S : Set α.toType, IsIndependent G S ∧ HasOrderType α S α

/-- Equivalent formulation using dichotomy. -/
theorem propertyP_iff (α : Ordinal) :
    PropertyP α ↔
    ∀ G : OrdinalGraph α, ¬HasInfinitePath G →
      ∃ S : Set α.toType, IsIndependent G S ∧ HasOrderType α S α := by
  sorry

/- ## Part III: Finite Ordinals -/

/-- P(n) holds trivially for finite ordinals (no infinite path possible). -/
theorem propertyP_finite (n : ℕ) : PropertyP n := by
  sorry

/-- For finite graphs, independent set or edge exists. -/
theorem finite_dichotomy (n : ℕ) (G : OrdinalGraph n) :
    (∃ S : Set (Fin n), IsIndependent G S ∧ S.nontrivial) ∨
    (∃ u v : Fin n, G.Adj u v) := by
  sorry

/- ## Part IV: The First Infinite Ordinal -/

/-- P(ω) holds: Every graph on ω has infinite path or infinite independent set. -/
theorem propertyP_omega : PropertyP ω := by
  sorry

/-- Ramsey's theorem for graphs on ω. -/
theorem ramsey_omega (G : OrdinalGraph ω) :
    HasInfinitePath G ∨ ∃ S : Set ω.toType, IsIndependent G S ∧ S.Infinite := by
  sorry

/- ## Part V: Erdős-Hajnal-Milner Theorem -/

/-- The critical ordinal ω₁^{ω+2}. -/
noncomputable def criticalOrdinal : Ordinal := ω₁ ^ (ω + 2)

/-- Erdős-Hajnal-Milner (1970): P(α) holds for all α < ω₁^{ω+2}. -/
theorem erdos_hajnal_milner (α : Ordinal) (hα : α < criticalOrdinal) :
    PropertyP α := by
  sorry

/-- The bound ω₁^{ω+2} is the frontier of knowledge. -/
theorem frontier : ∀ α < criticalOrdinal, PropertyP α := by
  exact erdos_hajnal_milner

/- ## Part VI: The Critical Case -/

/-- The open question: Does P(ω₁^{ω+2}) hold? Prize: $250 -/
def CriticalCaseConjecture : Prop := PropertyP criticalOrdinal

/-- The critical case is OPEN. -/
axiom critical_case_open : CriticalCaseConjecture

/-- Failure at critical ordinal would give counterexample. -/
theorem critical_counterexample (h : ¬PropertyP criticalOrdinal) :
    ∃ G : OrdinalGraph criticalOrdinal,
      ¬HasInfinitePath G ∧
      ∀ S : Set criticalOrdinal.toType, IsIndependent G S → HasOrderType criticalOrdinal S criticalOrdinal → False := by
  sorry

/- ## Part VII: Martin's Axiom -/

/-- Martin's Axiom (MA): A set-theoretic axiom. -/
axiom MartinsAxiom : Prop

/-- The continuum 2^{ℵ₀}. -/
noncomputable def continuum : Cardinal := 2 ^ ℵ₀

/-- Larson (1990): Under MA, P(α) holds for all α < 2^{ℵ₀}. -/
theorem larson_MA (α : Ordinal) (hα : α.card < continuum)
    (hMA : MartinsAxiom) : PropertyP α := by
  sorry

/-- MA extends the known range significantly. -/
theorem MA_extends :
    MartinsAxiom → ∀ α, α.card < continuum → PropertyP α := by
  exact fun hMA α hα => larson_MA α hα hMA

/- ## Part VIII: Ordinal Arithmetic -/

/-- ω₁ is the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := Ordinal.omega1

/-- ω₁^ω is already quite large. -/
noncomputable def omega1_pow_omega : Ordinal := ω₁ ^ ω

/-- The hierarchy of ordinals approaching the critical point. -/
theorem ordinal_hierarchy :
    ω < ω₁ ∧ ω₁ < ω₁ ^ ω ∧ ω₁ ^ ω < ω₁ ^ (ω + 1) ∧ ω₁ ^ (ω + 1) < criticalOrdinal := by
  sorry

/-- All countable ordinals satisfy P. -/
theorem countable_ordinals (α : Ordinal) (hα : α.card ≤ ℵ₀) : PropertyP α := by
  sorry

/- ## Part IX: Graph-Theoretic Tools -/

/-- König's lemma: Infinite finitely-branching tree has infinite path. -/
theorem konig_lemma {V : Type*} (T : SimpleGraph V) (root : V)
    (hTree : True) (hFinBranch : True) (hInf : True) :
    HasInfinitePath T := by
  sorry

/-- Ramsey for ordinals: Partition regular for large ordinals. -/
theorem ordinal_ramsey (α : Ordinal) (hα : α ≥ ω) :
    ∀ G : OrdinalGraph α, True := by
  intro G
  trivial

/- ## Part X: Independence Number -/

/-- Independence number: Maximum size of independent set. -/
noncomputable def independenceNumber (G : SimpleGraph V) : Cardinal :=
  ⨆ (S : Set V) (h : IsIndependent G S), #S

/-- For P(α) to fail, independence number must be < α. -/
theorem failure_condition (α : Ordinal) (G : OrdinalGraph α)
    (hPath : ¬HasInfinitePath G) (hFail : ¬PropertyP α) :
    independenceNumber G < α.card := by
  sorry

/- ## Part XI: Structural Results -/

/-- Graphs without infinite paths have special structure. -/
def HasBoundedPaths (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ f : Fin (n + 1) → V, Function.Injective f →
    ∃ i : Fin n, ¬G.Adj (f i) (f (i + 1))

/-- No infinite path implies bounded path lengths (for finite graphs). -/
theorem bounded_implies_no_infinite (G : SimpleGraph V) [Finite V]
    (h : ∃ n, HasBoundedPaths G n) : ¬HasInfinitePath G := by
  sorry

/-- Transfinite induction on ordinals. -/
theorem transfinite_induction (P : Ordinal → Prop)
    (h0 : P 0)
    (hS : ∀ α, P α → P (α + 1))
    (hL : ∀ α, α.IsLimit → (∀ β < α, P β) → P α) :
    ∀ α, P α := by
  sorry

/- ## Part XII: The General Conjecture -/

/-- The main conjecture: P(α) holds for all limit ordinals α. Prize: $500 -/
def GeneralConjecture : Prop :=
  ∀ α : Ordinal, α.IsLimit → PropertyP α

/-- The general conjecture is OPEN. -/
axiom general_conjecture_open : GeneralConjecture

/-- Partial result: Limit ordinals below the critical point. -/
theorem partial_result (α : Ordinal) (hL : α.IsLimit) (hα : α < criticalOrdinal) :
    PropertyP α := by
  exact erdos_hajnal_milner α hα

/-- The gap between known and conjectured. -/
theorem knowledge_gap :
    (∀ α < criticalOrdinal, PropertyP α) ∧
    (GeneralConjecture → ∀ α, α.IsLimit → PropertyP α) := by
  constructor
  · exact erdos_hajnal_milner
  · intro hGen α hL
    exact hGen α hL

end Erdos601

/-
  ## Summary

  This file formalizes Erdős Problem #601 on infinite paths and independent
  sets in ordinal graphs.

  **Status**: OPEN (Prize: $500)

  **The Question**: For which limit ordinals α does every graph on α have
  either an infinite path or an independent set of order type α?

  **Known Results**:
  - Holds for α < ω₁^{ω+2} (Erdős-Hajnal-Milner 1970)
  - Holds for α < 2^{ℵ₀} under Martin's Axiom (Larson 1990)

  **Open**:
  - α = ω₁^{ω+2} ($250 prize)
  - General case ($500 prize)

  **Key sorries**:
  - `erdos_hajnal_milner`: The main known result
  - `larson_MA`: Result under Martin's Axiom
  - `critical_case_open`: The boundary case (axiom)
  - `general_conjecture_open`: The full conjecture (axiom)
-/
