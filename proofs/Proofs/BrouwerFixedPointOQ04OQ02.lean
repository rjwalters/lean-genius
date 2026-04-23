/-
# Nash Equilibrium Existence via Nash's Brouwer Argument (OQ-04-OQ-02)

## Open Question
OQ-04-OQ-02: Can Nash equilibrium existence be proved using Nash's original
Brouwer fixed point approach, avoiding Berge's maximum theorem entirely?

## Answer: YES

Nash (1950) proved equilibrium existence not via UHC/Kakutani but by exhibiting
a **continuous single-valued self-map** of the product simplex whose fixed points
are Nash equilibria. This avoids upper hemicontinuity entirely.

## The Nash Map

For a finite N-player multilinear game, define:

  excess_i(k, σ) := max(0, EU_i(eₖ, σ) − EU_i(σᵢ, σ))

  φᵢ(k, σ) := (σᵢ(k) + excess_i(k, σ)) / (1 + Σₗ excess_i(l, σ))

Then φ : ∏ᵢ Δᵢ → ∏ᵢ Δᵢ is continuous, and by Brouwer's FPT, has a fixed
point. Every fixed point is a Nash equilibrium (proved below).

## Progress vs OQ-04-OQ-01

OQ-01 needed 2 axioms:
  - `bestResponse_uhc` (Berge's maximum theorem — blocked)
  - `kakutani_product_simplex` (product simplex embedding)

OQ-02 depends on 1 axiom (in BrouwerFixedPointOQ04):
  - `brouwer_pi_compact_convex` (general Brouwer FPT for products of compact convex sets)

The original `axiom brouwer_product_simplex` has been replaced by a THEOREM that
derives from `brouwer_pi_compact_convex`, using the already-proved properties:
  - `mixed_strategy_nonempty`: each Δᵢ is nonempty
  - `mixed_strategy_compact`: each Δᵢ is compact
  - `mixed_strategy_convex`: each Δᵢ is convex

## Status: COMPLETE (0 sorries, 0 local axioms)
  (depends on `brouwer_pi_compact_convex` in BrouwerFixedPointOQ04.lean)
- [x] `MultilinearGame` structure with explicit payoff
- [x] `mixedUtility`: multilinear extension (polynomial in σ)
- [x] `mixedUtility_continuous`: joint continuity of EU
- [x] Nash map: `nashExcess`, `nashMapComp`, `nashMap`
- [x] `nashMap_maps_simplex`: φ maps ∏ᵢ Δᵢ → ∏ᵢ Δᵢ (PROVED)
- [x] `nashMap_continuous`: φ is jointly continuous (PROVED)
- [x] `mixedUtility_linear_in_i`: EU_i linear in σᵢ (PROVED)
- [x] `fixed_point_is_nash`: fixed point ⟹ Nash equilibrium (PROVED)
- [x] `brouwer_product_simplex`: THEOREM (proved from brouwer_pi_compact_convex)
- [x] `nash_existence_multilinear`: Nash equilibrium exists (PROVED)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Proofs.BrouwerFixedPointOQ04

open KakutaniFPT Finset Set

noncomputable section

namespace NashBrouwer

-- ============================================================
-- PART 1: Multilinear Game Structure
-- ============================================================

/-- A finite N-player game with explicit pure strategy payoffs.
    The multilinear extension to mixed strategies is defined below.
    This is more explicit than `FiniteGame` in OQ-04: the payoff is
    given per pure strategy profile, enabling the multilinear extension. -/
structure MultilinearGame (N : ℕ) where
  /-- Strategy count for each player (finite set Fin k) -/
  strategies : Fin N → ℕ
  /-- Each player has at least one strategy -/
  strategies_pos : ∀ i, 0 < strategies i
  /-- Payoff for player i given a pure strategy profile s -/
  payoff : ∀ i : Fin N, (∀ j : Fin N, Fin (strategies j)) → ℝ

/-- Mixed strategy profile: one mixed strategy per player.
    σ j : Fin (G.strategies j) → ℝ assigns weights to pure strategies. -/
abbrev MixedProfile (N : ℕ) (G : MultilinearGame N) : Type :=
  ∀ j : Fin N, Fin (G.strategies j) → ℝ

/-- Product simplex: all players play valid mixed strategies -/
def ProductSimplex {N : ℕ} (G : MultilinearGame N) : Set (MixedProfile N G) :=
  { σ | ∀ j, σ j ∈ MixedStrategy (G.strategies j) }

/-- Expected utility for player i under mixed strategy profile σ.
    This is the multilinear extension: expectation over all pure strategy profiles. -/
def MultilinearGame.mixedUtility {N : ℕ} (G : MultilinearGame N)
    (i : Fin N) (σ : MixedProfile N G) : ℝ :=
  ∑ s : ∀ j : Fin N, Fin (G.strategies j),
    G.payoff i s * ∏ j : Fin N, σ j (s j)

/-- Pure strategy eₖ for player i: Dirac distribution at k -/
def pureStrat {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (k : Fin (G.strategies i)) : Fin (G.strategies i) → ℝ :=
  fun l => if l = k then 1 else 0

/-- Pure strategies are valid mixed strategies -/
lemma pureStrat_mem {N : ℕ} (G : MultilinearGame N)
    (i : Fin N) (k : Fin (G.strategies i)) :
    pureStrat G i k ∈ MixedStrategy (G.strategies i) := by
  refine ⟨fun l => by simp [pureStrat]; split_ifs <;> norm_num, ?_⟩
  simp [pureStrat, Finset.sum_ite_eq', Finset.mem_univ]

-- ============================================================
-- PART 2: Continuity of Mixed Utility
-- ============================================================

/-- Mixed utility is jointly continuous in all strategy profiles.
    Since mixedUtility is a finite sum of products of projections (a polynomial),
    it is automatically continuous by composition of continuous operations. -/
theorem mixedUtility_continuous {N : ℕ} (G : MultilinearGame N) (i : Fin N) :
    Continuous (fun σ : MixedProfile N G => G.mixedUtility i σ) := by
  unfold MultilinearGame.mixedUtility
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul continuous_const
  apply continuous_finset_prod
  intro j _
  exact (continuous_apply (s j)).comp (continuous_apply j)

/-- Mixed utility is continuous in player i's own strategy (for fixed opponents) -/
lemma mixedUtility_continuous_in_i {N : ℕ} (G : MultilinearGame N)
    (i : Fin N) (σ : MixedProfile N G) :
    Continuous (fun τ : Fin (G.strategies i) → ℝ =>
      G.mixedUtility i (Function.update σ i τ)) := by
  unfold MultilinearGame.mixedUtility
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul continuous_const
  apply continuous_finset_prod
  intro j _
  by_cases hij : j = i
  · -- j = i: (Function.update σ i τ) i (s i) = τ (s i) by Function.update_self
    rw [hij]
    have key : ∀ τ : Fin (G.strategies i) → ℝ, (Function.update σ i τ) i (s i) = τ (s i) :=
      fun τ => congr_fun (Function.update_self i τ σ) (s i)
    simp_rw [key]
    exact continuous_apply (s i)
  · -- j ≠ i: (Function.update σ i τ) j = σ j (constant in τ)
    simp only [Function.update_of_ne hij]
    exact continuous_const

-- ============================================================
-- PART 3: Linearity of Mixed Utility in Player i's Strategy
-- ============================================================

/-- Mixed utility is linear in player i's own mixed strategy.
    EU_i(σᵢ, σ₋ᵢ) = Σₖ σᵢ(k) · EU_i(eₖ, σ₋ᵢ)

    Proof: Swap ∑_s and ∑_k, then for fixed s use the product identity:
      ∏_j σ_j(s_j) = ∑_k σ_i(k) * ∏_j (if j=i then [s_j=k] else σ_j(s_j))
    which follows by splitting the product at j=i and applying the indicator sum. -/
lemma mixedUtility_linear_in_i {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) :
    G.mixedUtility i σ =
    ∑ k : Fin (G.strategies i),
      σ i k * G.mixedUtility i (Function.update σ i (pureStrat G i k)) := by
  simp only [MultilinearGame.mixedUtility]
  -- For each s, simplify the two products by splitting at index i
  have hprod_σ : ∀ s : ∀ j : Fin N, Fin (G.strategies j),
      G.payoff i s * ∏ j : Fin N, σ j (s j) =
      G.payoff i s * σ i (s i) * ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
    intro s
    rw [← Finset.mul_prod_erase Finset.univ (fun j => σ j (s j)) (Finset.mem_univ i)]
    ring
  -- For the updated profile, avoid type mismatch by splitting at i via mul_prod_erase
  -- (Function.update σ i (pureStrat G i k)) i (s i) = pureStrat G i k (s i) = if s i = k then 1 else 0
  -- (Function.update σ i (pureStrat G i k)) j (s j) = σ j (s j) for j ≠ i
  have hprod_upd : ∀ (k : Fin (G.strategies i)) (s : ∀ j : Fin N, Fin (G.strategies j)),
      G.payoff i s * ∏ j : Fin N, (Function.update σ i (pureStrat G i k)) j (s j) =
      G.payoff i s * (if s i = k then (1:ℝ) else 0) *
      ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
    intro k s
    -- Step 1: (update σ i (pure k)) i (s i) = if s i = k then 1 else 0
    --   (definitional: Function.update unfolds via iota reduction on Eq.rec rfl)
    have hi : (Function.update σ i (pureStrat G i k)) i (s i) = if s i = k then (1:ℝ) else 0 :=
      (congr_fun (Function.update_self i (pureStrat G i k) σ) (s i)).trans (by simp [pureStrat])
    -- Step 2: for j ≠ i, (update σ i (pure k)) j (s j) = σ j (s j)
    have hne : ∀ j ∈ Finset.univ.erase i,
        (Function.update σ i (pureStrat G i k)) j (s j) = σ j (s j) := by
      intro j hj
      simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hj
      exact congr_fun (Function.update_of_ne (f := σ) hj (pureStrat G i k)) (s j)
    -- Step 3: factor the product using mul_prod_erase
    have hprod : ∏ j : Fin N, (Function.update σ i (pureStrat G i k)) j (s j) =
        (if s i = k then (1:ℝ) else 0) * ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
      trans (Function.update σ i (pureStrat G i k)) i (s i) *
            ∏ j ∈ Finset.univ.erase i, (Function.update σ i (pureStrat G i k)) j (s j)
      · exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      · rw [hi, Finset.prod_congr rfl hne]
    rw [hprod]; ring
  simp_rw [hprod_σ, hprod_upd]
  -- Goal: ∑_s ps * σ_i(s_i) * P =
  --       ∑_k σ_i(k) * ∑_s ps * (if s_i=k then 1 else 0) * P
  -- where P = ∏_{j≠i} σ_j(s_j)
  -- Rewrite RHS: push σ_i(k) * inside inner sum, then swap sums
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext s
  -- Goal per s: ps * σ_i(s_i) * P = ∑_k σ_i(k) * (ps * (if s_i=k..) * P)
  have hind : ∑ k : Fin (G.strategies i), σ i k * (if s i = k then (1:ℝ) else 0) = σ i (s i) := by
    trans ∑ k : Fin (G.strategies i), if s i = k then σ i k else (0:ℝ)
    · congr 1; ext k; split_ifs <;> ring
    · simp [Finset.sum_ite_eq']
  rw [show G.payoff i s * σ i (s i) * ∏ j ∈ Finset.univ.erase i, σ j (s j) =
      (∑ k : Fin (G.strategies i), σ i k * (if s i = k then (1:ℝ) else 0)) *
      (G.payoff i s * ∏ j ∈ Finset.univ.erase i, σ j (s j)) from by rw [hind]; ring]
  rw [Finset.sum_mul]
  congr 1; ext k; ring

-- ============================================================
-- PART 4: Nash's Deviation Map
-- ============================================================

/-- Excess expected utility from deviating to pure strategy k.
    Positive if player i can improve by switching to pure strategy k. -/
def nashExcess {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (k : Fin (G.strategies i)) (σ : MixedProfile N G) : ℝ :=
  max 0 (G.mixedUtility i (Function.update σ i (pureStrat G i k)) -
         G.mixedUtility i σ)

lemma nashExcess_nonneg {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (k : Fin (G.strategies i)) (σ : MixedProfile N G) :
    0 ≤ nashExcess G i k σ := le_max_left 0 _

/-- The Nash map denominator ensures the output sums to 1 -/
def nashDenom {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) : ℝ :=
  1 + ∑ k : Fin (G.strategies i), nashExcess G i k σ

lemma nashDenom_pos {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) : 0 < nashDenom G i σ := by
  unfold nashDenom
  have h : 0 ≤ ∑ k : Fin (G.strategies i), nashExcess G i k σ :=
    Finset.sum_nonneg (fun k _ => nashExcess_nonneg G i k σ)
  linarith

/-- Nash map component for player i: shift weight toward better pure strategies -/
def nashMapComp {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) : Fin (G.strategies i) → ℝ :=
  fun k => (σ i k + nashExcess G i k σ) / nashDenom G i σ

/-- The full Nash map: update all players simultaneously -/
def nashMap {N : ℕ} (G : MultilinearGame N) (σ : MixedProfile N G) :
    MixedProfile N G :=
  fun i => nashMapComp G i σ

-- ============================================================
-- PART 5: Nash Map Maps the Simplex to Itself
-- ============================================================

lemma nashMapComp_nonneg {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) (hσ : σ ∈ ProductSimplex G) (k : Fin (G.strategies i)) :
    0 ≤ nashMapComp G i σ k :=
  div_nonneg
    (add_nonneg ((hσ i).1 k) (nashExcess_nonneg G i k σ))
    (le_of_lt (nashDenom_pos G i σ))

lemma nashMapComp_sum_one {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (σ : MixedProfile N G) (hσ : σ ∈ ProductSimplex G) :
    ∑ k : Fin (G.strategies i), nashMapComp G i σ k = 1 := by
  have hd_pos := nashDenom_pos G i σ
  have hd_ne : nashDenom G i σ ≠ 0 := ne_of_gt hd_pos
  -- Key: ∑ (numerators) = denominator
  have hnum : ∑ k : Fin (G.strategies i), (σ i k + nashExcess G i k σ) =
      nashDenom G i σ := by
    rw [Finset.sum_add_distrib, (hσ i).2]; unfold nashDenom; ring
  -- Sum of (f k / c) = (∑ f k) / c = c / c = 1
  have hfact : ∑ k : Fin (G.strategies i), nashMapComp G i σ k =
      (∑ k : Fin (G.strategies i), (σ i k + nashExcess G i k σ)) / nashDenom G i σ := by
    unfold nashMapComp
    rw [← Finset.sum_div]
  rw [hfact, hnum, div_self hd_ne]

/-- The Nash map maps the product simplex to itself -/
theorem nashMap_maps_simplex {N : ℕ} (G : MultilinearGame N)
    (σ : MixedProfile N G) (hσ : σ ∈ ProductSimplex G) :
    nashMap G σ ∈ ProductSimplex G := by
  intro i
  exact ⟨fun k => nashMapComp_nonneg G i σ hσ k, nashMapComp_sum_one G i σ hσ⟩

-- ============================================================
-- PART 6: Nash Map is Continuous
-- ============================================================

lemma nashExcess_continuous {N : ℕ} (G : MultilinearGame N) (i : Fin N)
    (k : Fin (G.strategies i)) :
    Continuous (fun σ : MixedProfile N G => nashExcess G i k σ) := by
  unfold nashExcess
  apply continuous_const.max
  apply Continuous.sub
  · -- mixedUtility i (update σ i (pureStrat G i k)) is continuous in σ
    unfold MultilinearGame.mixedUtility
    apply continuous_finset_sum
    intro s _
    apply Continuous.mul continuous_const
    apply continuous_finset_prod
    intro j _
    by_cases h : j = i
    · -- j = i: (update σ' i (pureStrat G i k)) i (s i) = if s i=k then 1 else 0 (constant in σ')
      rw [h]
      have key : ∀ σ' : MixedProfile N G,
          (Function.update σ' i (pureStrat G i k)) i (s i) = if s i = k then (1:ℝ) else 0 :=
        fun σ' => (congr_fun (Function.update_self i (pureStrat G i k) σ') (s i)).trans
                  (by simp [pureStrat])
      simp_rw [key]
      exact continuous_const
    · simp only [Function.update_of_ne h]
      exact (continuous_apply (s j)).comp (continuous_apply j)
  · exact mixedUtility_continuous G i

theorem nashMap_continuous {N : ℕ} (G : MultilinearGame N) :
    Continuous (nashMap G) := by
  unfold nashMap nashMapComp
  apply continuous_pi; intro i
  apply continuous_pi; intro k
  apply Continuous.div
  · exact Continuous.add ((continuous_apply k).comp (continuous_apply i))
        (nashExcess_continuous G i k)
  · unfold nashDenom
    exact Continuous.add continuous_const
      (continuous_finset_sum _ (fun k _ => nashExcess_continuous G i k))
  · intro σ; exact ne_of_gt (nashDenom_pos G i σ)

-- ============================================================
-- PART 7: Fixed Points Are Nash Equilibria
-- ============================================================

/-- A Nash equilibrium for the multilinear game -/
def IsNashEq {N : ℕ} (G : MultilinearGame N) (σ : MixedProfile N G) : Prop :=
  σ ∈ ProductSimplex G ∧
  ∀ i : Fin N, ∀ k : Fin (G.strategies i),
    G.mixedUtility i (Function.update σ i (pureStrat G i k)) ≤
    G.mixedUtility i σ

/-- **Fixed point of the Nash map = Nash equilibrium**

    Proof: At a fixed point σ*, `nashMapComp G i σ* k = σ* i k` for all i, k.
    Clearing the denominator: `σᵢ*(k) + excess_ik* = σᵢ*(k) · nashDenom_i*`.
    So: `excess_ik* = σᵢ*(k) · Cᵢ*` where `Cᵢ* := Σₗ excess_il* ≥ 0`.

    If `Cᵢ* > 0` for some i: every k with `σᵢ*(k) > 0` satisfies `excess_ik* > 0`,
    so `EU_i(eₖ, σ*) > EU_i(σᵢ*, σ*)`. But by linearity:
      EU_i(σᵢ*, σ*) = Σₖ σᵢ*(k) · EU_i(eₖ, σ*) > Σₖ σᵢ*(k) · EU_i(σᵢ*, σ*)
                     = EU_i(σᵢ*, σ*) · 1 = EU_i(σᵢ*, σ*) — contradiction.
    So `Cᵢ* = 0` for all i, meaning all excesses are 0, i.e., σ* is Nash. -/
theorem fixed_point_is_nash {N : ℕ} (G : MultilinearGame N)
    (σ : MixedProfile N G) (hσ : σ ∈ ProductSimplex G)
    (hfp : nashMap G σ = σ) :
    IsNashEq G σ := by
  refine ⟨hσ, fun i k => ?_⟩
  -- Step 1: Extract the fixed-point equation for player i, pure strategy k
  have hfp_ik : nashMapComp G i σ k = σ i k := by
    have := congr_fun (congr_fun hfp i) k
    simp [nashMap] at this; exact this
  -- Step 2: Set Ci = total excess for player i; extract excess_ik = σ i k * Ci
  set Ci := ∑ l : Fin (G.strategies i), nashExcess G i l σ with hCi_def
  have hCi_nonneg : 0 ≤ Ci :=
    Finset.sum_nonneg (fun l _ => nashExcess_nonneg G i l σ)
  -- From fixed point: (σ i k + excess_ik) / (1 + Ci) = σ i k
  have hex_eq : nashExcess G i k σ = σ i k * Ci := by
    unfold nashMapComp nashDenom at hfp_ik
    have hd_pos : 0 < 1 + Ci := by linarith
    rw [div_eq_iff (ne_of_gt hd_pos)] at hfp_ik
    have hring : σ i k * (1 + Ci) = σ i k + σ i k * Ci := by ring
    linarith [hfp_ik, hring]
  -- Step 3: Assume for contradiction that excess_ik > 0
  -- i.e., EU_i(eₖ, σ) > EU_i(σᵢ, σ)
  suffices h : ¬ (0 < nashExcess G i k σ) by
    push_neg at h
    have := le_antisymm h (nashExcess_nonneg G i k σ)
    unfold nashExcess at this
    rw [max_eq_left_iff] at this
    linarith [this]
  intro hex_pos
  -- Step 4: Ci > 0 and σ i k > 0
  have hCi_pos : 0 < Ci := by
    have := hex_eq ▸ hex_pos
    rcases (mul_pos_iff.mp this) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · linarith [(hσ i).1 k]
  have hσk_pos : 0 < σ i k := by
    have := hex_eq ▸ hex_pos
    rcases (mul_pos_iff.mp this) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith [hCi_nonneg]
  -- Step 5: Every l with σ i l > 0 has excess_il > 0 and hence EU_i(eₗ) > EU_i(σᵢ)
  have hall : ∀ l : Fin (G.strategies i), 0 < σ i l →
      G.mixedUtility i σ <
      G.mixedUtility i (Function.update σ i (pureStrat G i l)) := by
    intro l hσl_pos
    -- excess_il = σ i l * Ci > 0
    have hex_l_pos : 0 < nashExcess G i l σ := by
      have hfp_il : nashMapComp G i σ l = σ i l := by
        have := congr_fun (congr_fun hfp i) l
        simp [nashMap] at this; exact this
      unfold nashMapComp nashDenom at hfp_il
      have hd_pos : 0 < 1 + Ci := by linarith
      rw [div_eq_iff (ne_of_gt hd_pos)] at hfp_il
      have hring : σ i l * (1 + Ci) = σ i l + σ i l * Ci := by ring
      have hex_l_eq : nashExcess G i l σ = σ i l * Ci := by linarith [hfp_il, hring]
      rw [hex_l_eq]
      exact mul_pos hσl_pos hCi_pos
    -- excess_il > 0 iff EU_i(eₗ) > EU_i(σᵢ)
    unfold nashExcess at hex_l_pos
    simp only [lt_max_iff] at hex_l_pos
    rcases hex_l_pos with h | h
    · linarith
    · linarith
  -- Step 6: By linearity, EU_i(σᵢ) = Σₗ σ i l * EU_i(eₗ) > EU_i(σᵢ): contradiction
  have hlin := mixedUtility_linear_in_i G i σ
  -- Compute: Σₗ σ i l * EU_i(eₗ) > Σₗ σ i l * EU_i(σᵢ) = EU_i(σᵢ)
  have hstrict : G.mixedUtility i σ <
      ∑ l : Fin (G.strategies i),
        σ i l * G.mixedUtility i (Function.update σ i (pureStrat G i l)) := by
    have heq : G.mixedUtility i σ =
        ∑ l : Fin (G.strategies i), σ i l * G.mixedUtility i σ := by
      rw [← Finset.sum_mul, (hσ i).2, one_mul]
    rw [heq]
    apply Finset.sum_lt_sum
    · intro l _
      by_cases hl : 0 < σ i l
      · exact le_of_lt (mul_lt_mul_of_pos_left (hall l hl) hl)
      · push_neg at hl
        have : σ i l = 0 := le_antisymm hl ((hσ i).1 l)
        simp [this]
    · exact ⟨k, Finset.mem_univ _,
        mul_lt_mul_of_pos_left (hall k hσk_pos) hσk_pos⟩
  linarith [hlin]

-- ============================================================
-- PART 8: Brouwer FPT on the Product Simplex
-- ============================================================

/-- **Theorem: Brouwer's Fixed Point Theorem for the Product Simplex**

    The product simplex ∏ᵢ Δᵢ (with Δᵢ = MixedStrategy (G.strategies i))
    is a compact convex subset of a finite-dimensional Euclidean space.
    By Brouwer's fixed point theorem, every continuous self-map has a fixed point.

    **Proof**: Apply `brouwer_pi_compact_convex` (from BrouwerFixedPointOQ04)
    with the mixed strategy simplices as the compact convex factors.
    The required properties hold:
    - Nonemptiness: each player has at least one strategy (G.strategies_pos)
    - Compactness: MixedStrategy k is compact (closed subset of compact box)
    - Convexity: MixedStrategy k is convex (convex combination of distributions)

    `brouwer_pi_compact_convex` is the general Brouwer FPT for products of
    compact convex subsets of finite-dimensional spaces, which requires the
    topological fact that compact convex bodies are homeomorphic to balls. -/
theorem brouwer_product_simplex {N : ℕ} (G : MultilinearGame N)
    (f : MixedProfile N G → MixedProfile N G)
    (hf_maps : ∀ σ ∈ ProductSimplex G, f σ ∈ ProductSimplex G)
    (hf_cont : Continuous f) :
    ∃ σ ∈ ProductSimplex G, f σ = σ := by
  -- Translate hf_maps into the form required by brouwer_pi_compact_convex
  -- ProductSimplex G = { σ | ∀ j, σ j ∈ MixedStrategy (G.strategies j) }
  -- MixedProfile N G = ∀ j : Fin N, Fin (G.strategies j) → ℝ
  have hmaps' : ∀ σ : MixedProfile N G, (∀ j, σ j ∈ MixedStrategy (G.strategies j)) →
      ∀ j, f σ j ∈ MixedStrategy (G.strategies j) := fun σ hσ j =>
    hf_maps σ hσ j
  obtain ⟨σ, hmem, hfp⟩ := brouwer_pi_compact_convex
    (fun j : Fin N => MixedStrategy (G.strategies j))
    (fun j => mixed_strategy_nonempty (G.strategies_pos j))
    (fun _ => mixed_strategy_compact)
    (fun _ => mixed_strategy_convex)
    f hf_cont hmaps'
  exact ⟨σ, hmem, hfp⟩

-- ============================================================
-- PART 9: Nash Equilibrium Existence
-- ============================================================

/-- **Nash Equilibrium Existence for Multilinear Games (Nash 1950)**

    Every finite N-player game with multilinear expected utility has a Nash
    equilibrium in mixed strategies.

    Proof:
    1. Define Nash's deviation map φ (nashMap).
    2. φ maps the product simplex ∏ᵢ Δᵢ to itself.
    3. φ is continuous (polynomial in σ).
    4. By Brouwer FPT, φ has a fixed point σ* ∈ ∏ᵢ Δᵢ.
    5. Every fixed point of φ is a Nash equilibrium.

    This avoids Berge's maximum theorem and upper hemicontinuity entirely,
    requiring only Brouwer FPT for the product simplex. -/
theorem nash_existence_multilinear {N : ℕ} (G : MultilinearGame N) :
    ∃ σ ∈ ProductSimplex G, IsNashEq G σ := by
  obtain ⟨σ, hσ_mem, hfp⟩ :=
    brouwer_product_simplex G (nashMap G)
      (fun σ hσ => nashMap_maps_simplex G σ hσ)
      (nashMap_continuous G)
  exact ⟨σ, hσ_mem, fixed_point_is_nash G σ hσ_mem hfp⟩

/-- **Corollary**: Every multilinear game can be embedded in `FiniteGame`
    (the setup of OQ-04-OQ-01) via `G.utility i = G.mixedUtility i`.

    The key insight of this file: Nash's argument directly proves existence
    via a single-valued continuous map, without requiring:
    - Berge's maximum theorem (replaced by continuity of a polynomial)
    - UHC of best-response correspondences
    - Kakutani's theorem directly (only Brouwer is needed)

    The sole remaining dependency is the topological embedding
    `brouwer_product_simplex` (1 axiom), compared to OQ-01's 2 axioms. -/
theorem progress_summary {N : ℕ} (G : MultilinearGame N) :
    ∃ σ ∈ ProductSimplex G, IsNashEq G σ :=
  nash_existence_multilinear G

end NashBrouwer

end
