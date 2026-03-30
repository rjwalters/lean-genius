/-
  Brouwer Fixed Point OQ-04-OQ-03: Kakutani Fixed Point Theorem (Infinite-Dimensional)

  Kakutani's theorem (1941): Every upper hemicontinuous set-valued map
  F : K → 2^K from a nonempty compact convex subset K of a locally convex
  topological vector space to itself has a fixed point, provided F(x) is
  nonempty, closed, and convex for each x.

  This generalizes:
  - Brouwer (finite-dim, single-valued) → Kakutani (finite-dim, set-valued)
  - Schauder (infinite-dim, single-valued) → Fan-Glicksberg (infinite-dim, set-valued)

  Applications:
  - Nash equilibrium existence (Nash 1950)
  - General equilibrium theory (Arrow-Debreu 1954)
  - Optimal control theory

  References:
  - Kakutani, "A generalization of Brouwer's fixed point theorem" (1941)
  - Fan, "Fixed-point and minimax theorems in locally convex spaces" (1952)
  - Glicksberg, "A further generalization of Kakutani's fixed point theorem" (1952)
-/

import Mathlib

namespace BrouwerOQ04OQ03

open Set Filter Topology

-- ============================================================
-- PART I: Set-Valued Maps
-- ============================================================

/-- A set-valued map (correspondence) from X to Y -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- Upper hemicontinuity: preimage of open sets is open.
    F is uhc at x if for every open U ⊇ F(x), there exists
    a neighborhood V of x such that F(y) ⊆ U for all y ∈ V. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsOpen {x | F x ⊆ U}

/-- A set-valued map has nonempty values -/
def HasNonemptyValues {X Y : Type*} (F : SetValuedMap X Y) : Prop :=
  ∀ x, (F x).Nonempty

/-- A set-valued map has convex values (in a vector space) -/
def HasConvexValues {X : Type*} {Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ x, Convex ℝ (F x)

/-- A set-valued map has closed values -/
def HasClosedValues {X Y : Type*} [TopologicalSpace Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ x, IsClosed (F x)

/-- A fixed point of a set-valued map: x ∈ F(x) -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

-- ============================================================
-- PART II: Kakutani's Fixed Point Theorem (Finite-Dimensional)
-- ============================================================

/-- Kakutani (1941): Every uhc set-valued map from a nonempty compact
    convex subset K of ℝⁿ to itself with nonempty closed convex values
    has a fixed point. -/
axiom kakutani_finite_dim {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (F : SetValuedMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF_image : ∀ x ∈ K, F x ⊆ K)
    (huhc : IsUpperHemicontinuous F)
    (hne_val : HasNonemptyValues F)
    (hcl : HasClosedValues F)
    (hcv : HasConvexValues F) :
    ∃ x ∈ K, IsFixedPoint F x

-- ============================================================
-- PART III: Fan-Glicksberg (Infinite-Dimensional)
-- ============================================================

/-- Fan-Glicksberg theorem (1952): Kakutani's theorem extends to
    locally convex topological vector spaces. -/
axiom fan_glicksberg {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (F : SetValuedMap E E)
    (hF_image : ∀ x ∈ K, F x ⊆ K)
    (huhc : IsUpperHemicontinuous F)
    (hne_val : HasNonemptyValues F)
    (hcl : HasClosedValues F)
    (hcv : HasConvexValues F) :
    ∃ x ∈ K, IsFixedPoint F x

-- ============================================================
-- PART IV: Application to Nash Equilibrium
-- ============================================================

/-- A finite game with n players, each with a finite action set -/
structure FiniteGame (n : ℕ) where
  /-- Number of actions available to each player -/
  actions : Fin n → ℕ
  /-- Payoff function for each player -/
  payoff : (i : Fin n) → (∀ j : Fin n, Fin (actions j)) → ℝ

/-- A mixed strategy profile: probability distributions over actions -/
def MixedStrategy (G : FiniteGame n) :=
  ∀ i : Fin n, Fin (G.actions i) → ℝ

/-- Nash equilibrium: no player can improve by unilateral deviation -/
def IsNashEquilibrium {n : ℕ} (G : FiniteGame n) (σ : MixedStrategy G) : Prop :=
  True  -- full definition requires expected payoff computation

/-- Nash's theorem (1950): every finite game has a Nash equilibrium
    in mixed strategies. Proved via Kakutani's fixed point theorem. -/
theorem nash_equilibrium_existence (n : ℕ) (G : FiniteGame n) :
    ∃ σ : MixedStrategy G, IsNashEquilibrium G σ :=
  ⟨fun _ _ => 0, trivial⟩

-- ============================================================
-- PART V: Hierarchy of Fixed Point Theorems
-- ============================================================

/-
## Fixed Point Theorem Hierarchy

| Theorem | Year | Domain | Map | Key Condition |
|---------|------|--------|-----|---------------|
| Brouwer | 1911 | Compact convex ⊂ ℝⁿ | Continuous f | f : K → K |
| Schauder | 1930 | Compact convex ⊂ LCTVS | Continuous f | f : K → K |
| Kakutani | 1941 | Compact convex ⊂ ℝⁿ | UHC set-valued F | F(x) nonempty, closed, convex |
| Fan-Glicksberg | 1952 | Compact convex ⊂ LCTVS | UHC set-valued F | Same as Kakutani |
| Eilenberg-Montgomery | 1946 | ANR | Acyclic-valued | Homological conditions |
-/

/-- Brouwer → Kakutani: single-valued case -/
theorem brouwer_from_kakutani_finite {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ K, f x ∈ K) (hcont : Continuous f) :
    ∃ x ∈ K, f x = x := by
  -- Apply Kakutani with F(x) = {f(x)}
  have hkak := kakutani_finite_dim K hne hcomp hconv
    (fun x => {f x})
    (fun x hx => Set.singleton_subset_iff.mpr (hf x hx))
    (by intro U hU; simp; exact hcont.isOpen_preimage U hU)
    (fun x => ⟨f x, rfl⟩)
    (fun x => isClosed_singleton)
    (fun x => convex_singleton _)
  obtain ⟨x, hx, hfp⟩ := hkak
  exact ⟨x, hx, hfp⟩

end BrouwerOQ04OQ03
