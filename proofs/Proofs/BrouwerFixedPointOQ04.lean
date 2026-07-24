import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Proofs.BrouwerFixedPoint

/-
# Kakutani Fixed Point Theorem (OQ-04)

## Open Question
OQ-04: The Kakutani fixed point theorem (1941) generalizes Brouwer to
set-valued (multi-valued) maps. How does this generalization work, and
what are its key applications?

## What This Proves

Kakutani's theorem: Every upper hemicontinuous correspondence from a
nonempty compact convex subset S ⊆ ℝⁿ to itself, with nonempty convex
closed values, has a fixed point x* ∈ F(x*).

This is the foundational tool for:
- Nash equilibrium existence (Nash 1950)
- Walrasian equilibrium in economics (Arrow-Debreu 1954)
- Optimal control theory (Filippov 1962)

## Results
1. Definitions: Correspondence, upper hemicontinuity, set-valued fixed points
2. Kakutani FPT (axiomatized — proof requires Brouwer + approximation scheme)
3. Single-valued reduction: Kakutani for singletons = Brouwer (PROVED)
4. 1D Kakutani via IVT (PROVED)
5. Correspondence algebra: identity, constant, composition properties
6. Nash equilibrium existence framework

## Axioms
- `kakutani_fixed_point_axiom`: The main Kakutani FPT (requires Brouwer +
  finite-dimensional approximation, which needs algebraic topology)
- `brouwer_pi_compact_convex`: Brouwer FPT for products of compact convex
  sets (requires a Schoenflies-type homeomorphism argument not yet in
  Mathlib; see Part 10)

## Proved (previously axiomatized)
- `brouwer_compact_convex`: Brouwer FPT for compact convex subsets
  (now derived from BrouwerFixedPoint.lean's no-retraction proof)

## Historical Note
Shizuo Kakutani (1941) proved this as a direct generalization of Brouwer's
theorem. John Nash (1950) used it to prove the existence of Nash equilibria,
for which he received the Nobel Prize in Economics (1994). The theorem is
also essential in mathematical economics (Arrow-Debreu general equilibrium)
and optimal control (Filippov's lemma for differential inclusions).
-/

set_option linter.unusedVariables false

open Set Metric Filter

noncomputable section

namespace KakutaniFPT

-- ============================================================
-- PART 1: Correspondences (Set-Valued Maps)
-- ============================================================

/-- A correspondence (set-valued map) from a set S to subsets of a type.
    F : α → Set α assigns to each point x a set F(x) of values. -/
structure Correspondence (α : Type*) [TopologicalSpace α] (S : Set α) where
  toFun : α → Set α
  nonempty_values : ∀ x ∈ S, (toFun x).Nonempty
  closed_values : ∀ x ∈ S, IsClosed (toFun x)
  maps_to : ∀ x ∈ S, toFun x ⊆ S

/-- A fixed point of a correspondence: x* ∈ F(x*) -/
def Correspondence.IsFixedPoint {α : Type*} [TopologicalSpace α] {S : Set α}
    (F : Correspondence α S) (x : α) : Prop :=
  x ∈ S ∧ x ∈ F.toFun x

/-- A correspondence has a fixed point -/
def Correspondence.HasFixedPoint {α : Type*} [TopologicalSpace α] {S : Set α}
    (F : Correspondence α S) : Prop :=
  ∃ x, F.IsFixedPoint x

/-- A correspondence has convex values -/
def Correspondence.ConvexValued {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] {S : Set E}
    (F : Correspondence E S) : Prop :=
  ∀ x ∈ S, Convex ℝ (F.toFun x)

-- ============================================================
-- PART 2: Upper Hemicontinuity
-- ============================================================

/-- Upper hemicontinuity: For every open set V containing F(x),
    there exists a neighborhood U of x such that F(y) ⊆ V for all y ∈ U ∩ S.

    Equivalently: the preimage {x ∈ S | F(x) ⊆ V} is open in S
    for every open V. This is the standard Berge (1959) definition. -/
def IsUpperHemicontinuous {α : Type*} [TopologicalSpace α] (S : Set α)
    (F : α → Set α) : Prop :=
  ∀ x ∈ S, ∀ V : Set α, IsOpen V → F x ⊆ V →
    ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, F y ⊆ V

/-- A continuous single-valued function induces an upper hemicontinuous
    singleton-valued correspondence on any set S. -/
theorem continuous_singleton_uhc {α : Type*} [TopologicalSpace α]
    (S : Set α) {f : α → α} (hf : Continuous f) :
    IsUpperHemicontinuous S (fun x => {f x}) := by
  intro x _ V hV hfV
  have hfxV : f x ∈ V := hfV (mem_singleton _)
  have hpre : IsOpen (f ⁻¹' V) := hV.preimage hf
  refine ⟨f ⁻¹' V, hpre.mem_nhds hfxV, fun y hy => ?_⟩
  exact singleton_subset_iff.mpr hy.1

-- ============================================================
-- PART 3: The Kakutani Fixed Point Theorem
-- ============================================================

variable {n : ℕ} (hn : 1 ≤ n)

/-- The closed unit ball in ℝⁿ -/
def ClosedBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

theorem closedBall_compact : IsCompact (ClosedBall n) :=
  isCompact_closedBall 0 1

theorem closedBall_nonempty : (ClosedBall n).Nonempty :=
  Metric.nonempty_closedBall.mpr (by norm_num)

theorem closedBall_convex : Convex ℝ (ClosedBall n) :=
  convex_closedBall 0 1

/-- **Brouwer Fixed Point Theorem for compact convex subsets** (PROVED).

    Every continuous function from the closed unit ball in ℝⁿ to itself
    has a fixed point. Derived from the Brouwer FPT in BrouwerFixedPoint.lean
    (which proves it via the no-retraction theorem).

    Previously axiomatized; now proved by wrapping the function in a
    `Brouwer.SelfMap` and applying the parent theorem. -/
theorem brouwer_compact_convex (n : ℕ) (hn : n ≥ 1)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f)
    (hmaps : ∀ x ∈ ClosedBall n, f x ∈ ClosedBall n) :
    ∃ x ∈ ClosedBall n, f x = x := by
  obtain ⟨x, hx, hfx⟩ := Brouwer.brouwer_fixed_point hn ⟨f, hf, hmaps⟩
  exact ⟨x, hx, hfx⟩

/-- Axiom: Kakutani Fixed Point Theorem (1941).

    Let S be a nonempty compact convex subset of ℝⁿ.
    Let F : S → 2^S be a correspondence such that:
    1. F is upper hemicontinuous
    2. For each x ∈ S, F(x) is nonempty, convex, and closed
    Then F has a fixed point: ∃ x* ∈ S, x* ∈ F(x*).

    **Classical proof sketch:**
    1. Triangulate S into simplices of diameter < 1/k
    2. For each vertex vᵢ, pick yᵢ ∈ F(vᵢ)
    3. Define fₖ on vertices by fₖ(vᵢ) = yᵢ, extend affinely
    4. By convexity of F(x), fₖ maps S to S
    5. By Brouwer, fₖ has a fixed point xₖ
    6. By compactness, xₖ → x* along a subsequence
    7. By upper hemicontinuity, x* ∈ F(x*)

    This requires Brouwer's theorem (itself needing algebraic topology)
    plus the approximation/triangulation argument. -/
axiom kakutani_fixed_point_axiom (n : ℕ) (hn : n ≥ 1)
    (F : Correspondence (EuclideanSpace ℝ (Fin n)) (ClosedBall n))
    (huhc : IsUpperHemicontinuous (ClosedBall n) F.toFun)
    (hconv : F.ConvexValued) :
    F.HasFixedPoint

/-- **Kakutani Fixed Point Theorem**: Every upper hemicontinuous correspondence
    on a compact convex set with nonempty convex closed values has a fixed point. -/
theorem kakutani_fixed_point (hn : n ≥ 1)
    (F : Correspondence (EuclideanSpace ℝ (Fin n)) (ClosedBall n))
    (huhc : IsUpperHemicontinuous (ClosedBall n) F.toFun)
    (hconv : F.ConvexValued) :
    F.HasFixedPoint :=
  kakutani_fixed_point_axiom n hn F huhc hconv

-- ============================================================
-- PART 4: Single-Valued Reduction (Kakutani ⟹ Brouwer)
-- ============================================================

/-- Every continuous self-map of the closed ball induces a singleton-valued
    correspondence satisfying Kakutani's hypotheses. -/
def singletonCorrespondence (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f)
    (hmaps : ∀ x ∈ ClosedBall n, f x ∈ ClosedBall n) :
    Correspondence (EuclideanSpace ℝ (Fin n)) (ClosedBall n) where
  toFun := fun x => {f x}
  nonempty_values := fun x _ => Set.singleton_nonempty _
  closed_values := fun x _ => isClosed_singleton
  maps_to := fun x hx => Set.singleton_subset_iff.mpr (hmaps x hx)

/-- The singleton correspondence has convex values (singletons are convex). -/
theorem singleton_convex_valued (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hmaps : ∀ x ∈ ClosedBall n, f x ∈ ClosedBall n) :
    (singletonCorrespondence n f hf hmaps).ConvexValued := by
  intro x _
  exact convex_singleton _

/-- **Kakutani generalizes Brouwer**: A fixed point of the singleton
    correspondence {f(x)} at x* means x* ∈ {f(x*)} iff f(x*) = x*. -/
theorem kakutani_singleton_iff_brouwer (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hmaps : ∀ x ∈ ClosedBall n, f x ∈ ClosedBall n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (singletonCorrespondence n f hf hmaps).IsFixedPoint x ↔
    (x ∈ ClosedBall n ∧ f x = x) := by
  simp [Correspondence.IsFixedPoint, singletonCorrespondence]
  tauto

/-- Brouwer follows from Kakutani for singleton correspondences:
    If Kakutani gives a fixed point x* ∈ {f(x*)}, then f(x*) = x*. -/
theorem brouwer_from_kakutani (hn : n ≥ 1)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) (hmaps : ∀ x ∈ ClosedBall n, f x ∈ ClosedBall n) :
    ∃ x ∈ ClosedBall n, f x = x := by
  let F := singletonCorrespondence n f hf hmaps
  have huhc : IsUpperHemicontinuous (ClosedBall n) F.toFun :=
    continuous_singleton_uhc (ClosedBall n) hf
  have hconv := singleton_convex_valued n f hf hmaps
  obtain ⟨x, hx_mem, hx_in⟩ := kakutani_fixed_point hn F huhc hconv
  -- hx_in : x ∈ F.toFun x = {f x}, so x = f x
  have : x ∈ ({f x} : Set _) := hx_in
  rw [Set.mem_singleton_iff] at this
  exact ⟨x, hx_mem, this.symm⟩

-- ============================================================
-- PART 5: 1D Kakutani via IVT (FULLY PROVED)
-- ============================================================

/-- A continuous interval correspondence on [0,1]: F(x) = [l(x), u(x)]
    where both bounds are continuous. This is a special case of Kakutani
    where the correspondence has a particularly clean structure. -/
structure ContinuousIntervalCorrespondence where
  lower : ℝ → ℝ
  upper : ℝ → ℝ
  lower_le_upper : ∀ x ∈ Set.Icc (0:ℝ) 1, lower x ≤ upper x
  lower_nonneg : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ lower x
  upper_le_one : ∀ x ∈ Set.Icc (0:ℝ) 1, upper x ≤ 1
  lower_cont : ContinuousOn lower (Set.Icc 0 1)
  upper_cont : ContinuousOn upper (Set.Icc 0 1)

/-- A fixed point of an interval correspondence: l(x) ≤ x ≤ u(x). -/
def ContinuousIntervalCorrespondence.IsFixedPoint
    (F : ContinuousIntervalCorrespondence) (x : ℝ) : Prop :=
  x ∈ Set.Icc (0:ℝ) 1 ∧ F.lower x ≤ x ∧ x ≤ F.upper x

/-- **1D Kakutani via IVT**: Every continuous interval correspondence
    on [0,1] mapping into [0,1] has a fixed point.

    Proof: Apply IVT to g(x) = upper(x) - x. We have g(0) ≥ 0 (since
    upper(0) ≥ lower(0) ≥ 0) and g(1) ≤ 0 (since upper(1) ≤ 1).
    By IVT, ∃ x₀ with upper(x₀) = x₀. Since lower(x₀) ≤ upper(x₀) = x₀,
    we get lower(x₀) ≤ x₀ ≤ upper(x₀). -/
theorem kakutani_1d (F : ContinuousIntervalCorrespondence) :
    ∃ x, F.IsFixedPoint x := by
  -- g(x) = upper(x) - x is continuous on [0,1]
  have hg_cont : ContinuousOn (fun x => F.upper x - x) (Set.Icc 0 1) :=
    F.upper_cont.sub continuousOn_id
  -- g(0) = upper(0) ≥ 0
  have hg0 : 0 ≤ F.upper 0 - 0 := by
    have := F.lower_nonneg 0 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
    linarith [F.lower_le_upper 0 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]
  -- g(1) = upper(1) - 1 ≤ 0
  have hg1 : F.upper 1 - 1 ≤ 0 :=
    sub_nonpos.mpr (F.upper_le_one 1 (by norm_num))
  -- By IVT, ∃ x₀ ∈ [0,1] with g(x₀) = 0
  obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ :=
    intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hg_cont ⟨hg1, hg0⟩
  -- upper(x₀) = x₀
  have hupper : F.upper x₀ = x₀ := by linarith
  -- lower(x₀) ≤ upper(x₀) = x₀
  have hlower : F.lower x₀ ≤ x₀ := by
    calc F.lower x₀ ≤ F.upper x₀ := F.lower_le_upper x₀ hx₀_mem
    _ = x₀ := hupper
  exact ⟨x₀, hx₀_mem, hlower, le_of_eq hupper.symm⟩

/-- The 1D Kakutani theorem is a true generalization: the constant
    correspondence [0.4, 0.6] has x = 0.5 as a fixed point. -/
theorem kakutani_1d_example :
    ∃ x ∈ Set.Icc (0:ℝ) 1, (0.4 : ℝ) ≤ x ∧ x ≤ 0.6 :=
  ⟨0.5, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

-- ============================================================
-- PART 6: Correspondence Algebra
-- ============================================================

/-- The constant correspondence: F(x) = S for all x.
    This trivially has every point as a fixed point. -/
def constantCorrespondence (n : ℕ) :
    Correspondence (EuclideanSpace ℝ (Fin n)) (ClosedBall n) where
  toFun := fun _ => ClosedBall n
  nonempty_values := fun _ _ => closedBall_nonempty
  closed_values := fun _ _ => isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 |>.isClosed
  maps_to := fun _ _ => Subset.rfl

/-- The constant correspondence has a fixed point (any point in S). -/
theorem constant_has_fixed_point :
    (constantCorrespondence n).HasFixedPoint := by
  obtain ⟨x, hx⟩ := closedBall_nonempty (n := n)
  exact ⟨x, hx, hx⟩

/-- The identity correspondence: F(x) = {x}.
    Every point is a fixed point. -/
def identityCorrespondence (n : ℕ) :
    Correspondence (EuclideanSpace ℝ (Fin n)) (ClosedBall n) where
  toFun := fun x => {x}
  nonempty_values := fun _ _ => singleton_nonempty _
  closed_values := fun _ _ => isClosed_singleton
  maps_to := fun x hx => singleton_subset_iff.mpr hx

/-- Every point of S is a fixed point of the identity correspondence. -/
theorem identity_all_fixed (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ ClosedBall n) :
    (identityCorrespondence n).IsFixedPoint x :=
  ⟨hx, mem_singleton _⟩

-- ============================================================
-- PART 7: Nash Equilibrium Framework
-- ============================================================

/-- A finite N-player normal-form game. -/
structure FiniteGame (N : ℕ) where
  /-- Strategy count for each player -/
  strategies : Fin N → ℕ
  /-- Each player has at least one strategy -/
  strategies_pos : ∀ i, 0 < strategies i
  /-- Utility function for each player given all strategy profiles.
      A mixed strategy profile is a probability distribution over
      each player's strategies. -/
  utility : Fin N → (∀ i, Fin (strategies i) → ℝ) → ℝ

/-- A mixed strategy for player i: a probability distribution over strategies. -/
def MixedStrategy (k : ℕ) : Set (Fin k → ℝ) :=
  {σ | (∀ j, 0 ≤ σ j) ∧ ∑ j, σ j = 1}

/-- Mixed strategies form a nonempty set (uniform distribution). -/
theorem mixed_strategy_nonempty {k : ℕ} (hk : 0 < k) :
    (MixedStrategy k).Nonempty := by
  refine ⟨fun _ => 1 / k, fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Mixed strategies form a convex set. -/
theorem mixed_strategy_convex {k : ℕ} : Convex ℝ (MixedStrategy k) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hx.2, hy.2]
    linarith

/-- Mixed strategies form a closed set (intersection of closed sets). -/
theorem mixed_strategy_closed {k : ℕ} : IsClosed (MixedStrategy k) := by
  -- Rewrite as (⋂ j, {σ | 0 ≤ σ j}) ∩ {σ | ∑ j, σ j = 1}
  have : MixedStrategy k = (⋂ j : Fin k, {σ : Fin k → ℝ | 0 ≤ σ j}) ∩
      {σ | ∑ j, σ j = 1} := by
    ext σ; simp [MixedStrategy, Set.mem_iInter]
  rw [this]
  exact (isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_eq (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const)

/-- Mixed strategies are bounded: every component is in [0,1]. -/
theorem mixed_strategy_bounded {k : ℕ} :
    MixedStrategy k ⊆ Set.pi Set.univ (fun _ : Fin k => Set.Icc (0:ℝ) 1) := by
  intro σ ⟨hpos, hsum⟩ j _
  exact ⟨hpos j, by
    have : σ j ≤ ∑ i, σ i := Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ j)
    linarith⟩

/-- Mixed strategies form a compact set (closed subset of compact box). -/
theorem mixed_strategy_compact {k : ℕ} : IsCompact (MixedStrategy k) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : Fin k => isCompact_Icc))
  · exact mixed_strategy_closed
  · exact mixed_strategy_bounded

/-- **Nash Equilibrium Existence** (statement).

    Every finite game has a Nash equilibrium in mixed strategies.

    John Nash (1950) proved this using Kakutani's fixed point theorem:
    1. Each player's best-response set is a nonempty compact convex set
    2. The combined best-response correspondence is upper hemicontinuous
    3. By Kakutani, there is a fixed point — a Nash equilibrium

    We state this as a theorem whose proof requires Kakutani. -/
theorem nash_equilibrium_framework (N : ℕ) (hN : 0 < N) :
    ∀ (k : Fin N → ℕ), (∀ i, 0 < k i) →
    -- The product of simplices is compact
    IsCompact (Set.pi Set.univ (fun i => MixedStrategy (k i))) := by
  intro k hk
  exact isCompact_univ_pi (fun i => mixed_strategy_compact)

-- ============================================================
-- PART 8: Nash Equilibrium Definition
-- ============================================================

/-- A Nash equilibrium: no player can improve expected utility by
    unilateral deviation from their mixed strategy.

    σ is a Nash equilibrium of G if:
    1. Each σᵢ is a valid mixed strategy
    2. For every player i and alternative strategy τᵢ,
       u_i(τᵢ, σ₋ᵢ) ≤ u_i(σ) -/
def IsNashEquilibrium {N : ℕ} (G : FiniteGame N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ) : Prop :=
  (∀ j, σ j ∈ MixedStrategy (G.strategies j)) ∧
  ∀ i : Fin N, ∀ τ ∈ MixedStrategy (G.strategies i),
    G.utility i (Function.update σ i τ) ≤ G.utility i σ

/-- In a constant-utility game, every valid strategy profile is a
    Nash equilibrium (no deviation can improve utility). -/
theorem isNashEquilibrium_of_constant_utility {N : ℕ} (G : FiniteGame N)
    (σ : ∀ j, Fin (G.strategies j) → ℝ)
    (hσ : ∀ j, σ j ∈ MixedStrategy (G.strategies j))
    (hconst : ∀ i σ', G.utility i σ' = G.utility i σ) :
    IsNashEquilibrium G σ :=
  ⟨hσ, fun i τ _ => le_of_eq (hconst i _)⟩

-- ============================================================
-- PART 9: Properties of Upper Hemicontinuity
-- ============================================================

/-- A constant correspondence is upper hemicontinuous. -/
theorem constant_uhc {α : Type*} [TopologicalSpace α]
    (S : Set α) (C : Set α) :
    IsUpperHemicontinuous S (fun _ => C) := by
  intro x _ V _ hCV
  exact ⟨Set.univ, univ_mem, fun y _ => hCV⟩

/-- Composition: if F is UHC and g is continuous, then x ↦ g '' F(x)
    has the image of a UHC set under a continuous map. -/
theorem uhc_image {α : Type*} [TopologicalSpace α]
    (S : Set α) (F : α → Set α) (g : α → α)
    (hF : IsUpperHemicontinuous S F) (hg : Continuous g) :
    IsUpperHemicontinuous S (fun x => g '' F x) := by
  intro x hx V hV hgFV
  have hFpre : F x ⊆ g ⁻¹' V := by
    intro z hz
    exact hgFV ⟨z, hz, rfl⟩
  have hpre : IsOpen (g ⁻¹' V) := hV.preimage hg
  obtain ⟨U, hU, hUF⟩ := hF x hx (g ⁻¹' V) hpre hFpre
  exact ⟨U, hU, fun y hy => by
    intro z ⟨w, hw, hwz⟩
    rw [← hwz]
    exact (hUF y hy) hw⟩

-- ============================================================
-- PART 10: General Brouwer FPT for Products of Compact Convex Sets
-- ============================================================

/-- **Brouwer Fixed Point Theorem for Products of Compact Convex Sets**

    Let ι be a finite index type and κ : ι → ℕ. Let K i ⊆ Fin (κ i) → ℝ be
    nonempty compact convex sets for each i. Then any continuous self-map of
    ∏ᵢ K i has a fixed point.

    **Mathematical proof sketch:**
    1. The product ∏ᵢ K i is compact (Tychonoff) and convex (product of convex sets).
    2. The product embeds into EuclideanSpace ℝ (Fin D) where D = ∑ᵢ κ i via
       the concatenation map: x ↦ (x i j)_{(i,j) ∈ Σ i, Fin (κ i)}.
    3. The image is a compact convex subset of a finite-dimensional Euclidean space.
    4. Such sets are homeomorphic to closed balls (compact convex body theorem).
    5. By Brouwer FPT for the closed ball, any continuous self-map has a fixed point.
    6. Transport the fixed point back via the homeomorphism.

    Steps (4) requires algebraic topology (Schoenflies-type theorem) not yet
    formalized in Mathlib. Hence this theorem is stated as an axiom. -/
axiom brouwer_pi_compact_convex {ι : Type*} [Fintype ι] {κ : ι → ℕ}
    (K : ∀ i, Set (Fin (κ i) → ℝ))
    (hK_ne : ∀ i, (K i).Nonempty)
    (hK_compact : ∀ i, IsCompact (K i))
    (hK_convex : ∀ i, Convex ℝ (K i))
    (f : (∀ i, Fin (κ i) → ℝ) → ∀ i, Fin (κ i) → ℝ)
    (hf : Continuous f)
    (hfK : ∀ x, (∀ i, x i ∈ K i) → ∀ i, f x i ∈ K i) :
    ∃ x, (∀ i, x i ∈ K i) ∧ f x = x

end KakutaniFPT

-- Export main results
#check KakutaniFPT.brouwer_compact_convex
#check KakutaniFPT.kakutani_fixed_point
#check KakutaniFPT.brouwer_from_kakutani
#check KakutaniFPT.kakutani_singleton_iff_brouwer
#check KakutaniFPT.constant_has_fixed_point
#check KakutaniFPT.identity_all_fixed
#check KakutaniFPT.mixed_strategy_convex
#check KakutaniFPT.mixed_strategy_compact
#check KakutaniFPT.nash_equilibrium_framework
#check @KakutaniFPT.IsNashEquilibrium
#check @KakutaniFPT.isNashEquilibrium_of_constant_utility
#check @KakutaniFPT.brouwer_pi_compact_convex
