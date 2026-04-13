import Mathlib

/-
# Schauder Fixed Point — OQ-03: Kakutani Fixed Point Theorem

## Research Problem: schauder-fixed-point-oq-03

OQ: How can we formalize the Kakutani fixed point theorem for
set-valued maps?

Kakutani (1941): Let S ⊆ ℝⁿ be nonempty, compact, convex.
Let F : S → 2^S be an upper hemicontinuous set-valued map
with nonempty, closed, convex values. Then F has a fixed point:
∃ x ∈ S, x ∈ F(x).

This generalizes Brouwer/Schauder to correspondences and is the
key tool for proving existence of Nash equilibria.

Tags: fixed-point, kakutani, set-valued-map, game-theory
-/

open Set Filter Topology

namespace KakutaniFixedPoint

-- ============================================================
-- Part I: Set-Valued Maps
-- ============================================================

/-- A set-valued map (correspondence) from X to Y assigns
    to each x ∈ X a subset F(x) ⊆ Y. -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- The graph of a set-valued map. -/
def SetValuedMap.graph {X Y : Type*} (F : SetValuedMap X Y) : Set (X × Y) :=
  {p | p.2 ∈ F p.1}

/-- A set-valued map has nonempty values. -/
def HasNonemptyValues {X Y : Type*} (F : SetValuedMap X Y) : Prop :=
  ∀ x, (F x).Nonempty

/-- A set-valued map has closed values (in a topological space). -/
def HasClosedValues {X Y : Type*} [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ x, IsClosed (F x)

/-- A set-valued map has convex values (in a vector space). -/
def HasConvexValues {X : Type*} {Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ x, Convex ℝ (F x)

-- ============================================================
-- Part II: Upper Hemicontinuity
-- ============================================================

/-- Upper hemicontinuity: F is upper hemicontinuous if for every
    open set V ⊇ F(x₀), there exists a neighborhood U of x₀
    such that F(x) ⊆ V for all x ∈ U.

    Equivalently: the preimage {x | F(x) ⊆ V} is open for
    every open V. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}

/-- A continuous single-valued function is upper hemicontinuous
    when viewed as a set-valued map. -/
theorem continuous_is_uhc {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    IsUpperHemicontinuous (fun x => {f x}) := by
  intro V hV
  have : {x | {f x} ⊆ V} = f ⁻¹' V := by
    ext x; simp [Set.singleton_subset_iff]
  rw [this]
  exact hV.preimage hf

-- ============================================================
-- Part III: Fixed Points of Set-Valued Maps
-- ============================================================

/-- A fixed point of a set-valued map F: x ∈ F(x). -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

/-- For single-valued maps, this reduces to f(x) = x. -/
theorem fixedpoint_singlevalued {X : Type*} {f : X → X} (x : X) :
    IsFixedPoint (fun y => {f y}) x ↔ f x = x := by
  simp [IsFixedPoint]

-- ============================================================
-- Part IV: Kakutani's Theorem (Finite-Dimensional)
-- ============================================================

/-- Kakutani Fixed Point Theorem (1941):

    Let S ⊆ ℝⁿ be nonempty, compact, convex. Let F : S → 2^S
    be upper hemicontinuous with nonempty, closed, convex values.
    Then F has a fixed point: ∃ x ∈ S, x ∈ F(x).

    The proof uses Brouwer's theorem applied to approximate
    single-valued selections of F.

    Axiomatized because the proof requires:
    1. Finite-dimensional simplicial approximation
    2. Convergence of approximate fixed points
    3. Upper hemicontinuity to pass to the limit -/
axiom kakutani_finite_dim {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : HasNonemptyValues F) (hF_closed : HasClosedValues F)
    (hF_convex : HasConvexValues F)
    (hF_uhc : IsUpperHemicontinuous F) :
    ∃ x : ↥S, IsFixedPoint F x

-- ============================================================
-- Part V: Recovering Brouwer
-- ============================================================

/-- Kakutani implies Brouwer: every continuous function on a
    compact convex set has a fixed point. -/
theorem brouwer_from_kakutani {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- View f as a set-valued map F(x) = {f(x)}
  let F : SetValuedMap ↥S ↥S := fun x => {f x}
  have hF_ne : HasNonemptyValues F := fun x => Set.singleton_nonempty (f x)
  have hF_closed : HasClosedValues F := fun x => isClosed_singleton
  have hF_convex : HasConvexValues F := fun x => convex_singleton (f x)
  have hF_uhc : IsUpperHemicontinuous F := continuous_is_uhc hf
  obtain ⟨x, hx⟩ := kakutani_finite_dim S hS_ne hS_compact hS_convex
    F hF_ne hF_closed hF_convex hF_uhc
  exact ⟨x, (fixedpoint_singlevalued x).mp hx⟩

-- ============================================================
-- Part VI: Application to Game Theory
-- ============================================================

/-- Nash equilibrium existence context:

    In an n-player game, the best response correspondence
    BR : strategy profiles → 2^(strategy profiles)
    maps each profile to the set of profiles where each player
    plays a best response.

    If the strategy spaces are compact convex (mixed strategies)
    and the payoff functions are continuous, then BR satisfies
    the Kakutani conditions. Hence Nash equilibria exist. -/
/- nash_equilibrium_sketch: Nash equilibria exist by Kakutani's fixed point
    theorem applied to the best response correspondence (sketch). -/

/-
  Summary

  This file formalizes the Kakutani fixed point theorem framework:

  - Set-valued maps (correspondences) with graph, nonempty/closed/convex values
  - Upper hemicontinuity definition and proof that continuous functions are UHC
  - Fixed points of set-valued maps: x ∈ F(x)
  - Kakutani's theorem axiomatized for finite-dimensional Euclidean space
  - Recovery of Brouwer as a corollary

  1 axiom (Kakutani's theorem), 0 sorries.
  The connection to Nash equilibrium existence is sketched.
-/

end KakutaniFixedPoint
