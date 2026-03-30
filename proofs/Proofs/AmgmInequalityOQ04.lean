/-
Gauss AGM Iteration and Connection to Elliptic Integrals

## What This Proves

The arithmetic-geometric mean (AGM) of two positive reals a ≥ b > 0 is defined by
the iteration:
  aₙ₊₁ = (aₙ + bₙ)/2,  bₙ₊₁ = √(aₙ · bₙ)
starting from a₀ = a, b₀ = b.

Both sequences converge to the same limit M(a,b), the arithmetic-geometric mean.

This file formalizes:
1. The AGM iteration and its basic properties
2. The sandwich property: bₙ ≤ bₙ₊₁ ≤ aₙ₊₁ ≤ aₙ
3. Gap contraction: aₙ₊₁ - bₙ₊₁ ≤ (aₙ - bₙ)/2
4. Convergence of both sequences to a common limit
5. The connection to elliptic integrals (axiomatized)

## Key Result

Gauss (1799) discovered that M(1, √2/2) = π / (2K(1/√2)), where K is the
complete elliptic integral of the first kind. This remarkable connection links
a simple iteration to deep transcendental functions.

## Status
- [x] AGM iteration defined
- [x] AM ≥ GM proved (from (a-b)² ≥ 0)
- [x] Sandwich property proved
- [x] Gap contraction proved
- [x] Convergence proved (via Mathlib monotone convergence)
- [ ] Elliptic integral connection (axiomatized, K(k) not in Mathlib)
-/

import Mathlib

open Filter Set Real

namespace AmgmInequalityOQ04

-- ============================================================================
-- § 1. Core Definitions
-- ============================================================================

/-- The AGM iteration step: given (a, b), produce ((a+b)/2, √(ab)). -/
noncomputable def agmStep (a b : ℝ) : ℝ × ℝ :=
  ((a + b) / 2, Real.sqrt (a * b))

/-- The AGM sequence: iterating agmStep from initial values (a, b). -/
noncomputable def agmSeq (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 =>
    let prev := agmSeq a b n
    agmStep prev.1 prev.2

/-- The a-sequence: arithmetic means. -/
noncomputable def agmA (a b : ℝ) (n : ℕ) : ℝ := (agmSeq a b n).1

/-- The b-sequence: geometric means. -/
noncomputable def agmB (a b : ℝ) (n : ℕ) : ℝ := (agmSeq a b n).2

/-- Initial values. -/
theorem agmA_zero (a b : ℝ) : agmA a b 0 = a := rfl
theorem agmB_zero (a b : ℝ) : agmB a b 0 = b := rfl

/-- Recurrence relations. -/
theorem agmA_succ (a b : ℝ) (n : ℕ) :
    agmA a b (n + 1) = (agmA a b n + agmB a b n) / 2 := by
  simp [agmA, agmSeq, agmStep]

theorem agmB_succ (a b : ℝ) (n : ℕ) :
    agmB a b (n + 1) = Real.sqrt (agmA a b n * agmB a b n) := by
  simp [agmB, agmA, agmSeq, agmStep]

-- ============================================================================
-- § 2. AM ≥ GM for Two Variables
-- ============================================================================

/-- **AM ≥ GM for two non-negative reals.**
    (a + b)/2 ≥ √(ab), with equality iff a = b.
    Proof: ((a+b)/2)² - ab = (a-b)²/4 ≥ 0. -/
theorem am_ge_gm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsum : 0 ≤ (a + b) / 2 := by linarith
  rw [← Real.sqrt_sq hsum]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])

-- ============================================================================
-- § 3. Positivity and Ordering Invariants
-- ============================================================================

variable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)

/-- Both sequences remain positive (proved simultaneously). -/
private theorem agm_pos_aux :
    ∀ n, 0 < agmA a b n ∧ 0 < agmB a b n := by
  intro n
  induction n with
  | zero => exact ⟨ha, hb⟩
  | succ n ih =>
    constructor
    · rw [agmA_succ]; linarith [ih.1, ih.2]
    · rw [agmB_succ]; exact Real.sqrt_pos_of_pos (mul_pos ih.1 ih.2)

theorem agmA_pos (n : ℕ) : 0 < agmA a b n := (agm_pos_aux ha hb n).1

theorem agmB_pos (n : ℕ) : 0 < agmB a b n := (agm_pos_aux ha hb n).2

/-- **Sandwich property**: bₙ ≤ aₙ for all n.
    Proved by AM ≥ GM at each step. -/
theorem agmB_le_agmA : ∀ n, agmB a b n ≤ agmA a b n := by
  intro n
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [agmA_succ, agmB_succ]
    exact am_ge_gm _ _ (le_of_lt (agmA_pos ha hb n)) (le_of_lt (agmB_pos ha hb n))

/-- The a-sequence is decreasing: aₙ₊₁ ≤ aₙ. -/
theorem agmA_antitone : Antitone (agmA a b) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [agmA_succ]
  have := agmB_le_agmA ha hb hab n
  linarith

/-- The b-sequence is increasing: bₙ ≤ bₙ₊₁. -/
theorem agmB_monotone : Monotone (agmB a b) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [agmB_succ]
  have hbn_pos := agmB_pos ha hb n
  have han_pos := agmA_pos ha hb n
  have hbn_le_an := agmB_le_agmA ha hb hab n
  -- √(aₙ · bₙ) ≥ √(bₙ · bₙ) = bₙ (since aₙ ≥ bₙ)
  calc agmB a b n
      = Real.sqrt (agmB a b n * agmB a b n) := by
        rw [Real.sqrt_mul_self (le_of_lt hbn_pos)]
    _ ≤ Real.sqrt (agmA a b n * agmB a b n) := by
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hbn_le_an (le_of_lt hbn_pos))

-- ============================================================================
-- § 4. Gap Contraction
-- ============================================================================

/-- **Gap contraction**: aₙ₊₁ - bₙ₊₁ ≤ (aₙ - bₙ)/2.
    The gap halves at each step (at least). -/
theorem gap_contracts (n : ℕ) :
    agmA a b (n + 1) - agmB a b (n + 1) ≤ (agmA a b n - agmB a b n) / 2 := by
  rw [agmA_succ, agmB_succ]
  have hbn_pos := agmB_pos ha hb n
  have han_pos := agmA_pos ha hb n
  have hbn_le_an := agmB_le_agmA ha hb hab n
  -- Need: (aₙ+bₙ)/2 - √(aₙbₙ) ≤ (aₙ-bₙ)/2
  -- Equivalently: √(aₙbₙ) ≥ bₙ, which we proved in agmB_monotone
  have hgm_ge_b : Real.sqrt (agmA a b n * agmB a b n) ≥ agmB a b n := by
    calc agmB a b n
        = Real.sqrt (agmB a b n * agmB a b n) := by
          rw [Real.sqrt_mul_self (le_of_lt hbn_pos)]
      _ ≤ Real.sqrt (agmA a b n * agmB a b n) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hbn_le_an (le_of_lt hbn_pos))
  linarith

/-- The gap is bounded by (a-b)/2ⁿ. -/
theorem gap_bound (n : ℕ) :
    agmA a b n - agmB a b n ≤ (a - b) / 2 ^ n := by
  induction n with
  | zero => simp [agmA_zero, agmB_zero]
  | succ n ih =>
    calc agmA a b (n + 1) - agmB a b (n + 1)
        ≤ (agmA a b n - agmB a b n) / 2 := gap_contracts ha hb hab n
      _ ≤ ((a - b) / 2 ^ n) / 2 := by linarith
      _ = (a - b) / 2 ^ (n + 1) := by ring

-- ============================================================================
-- § 5. Convergence
-- ============================================================================

/-- The a-sequence is bounded below by b₀. -/
theorem agmA_bddBelow : BddBelow (range (agmA a b)) := by
  refine ⟨b, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  calc b = agmB a b 0 := (agmB_zero a b).symm
    _ ≤ agmB a b n := agmB_monotone ha hb hab (Nat.zero_le n)
    _ ≤ agmA a b n := agmB_le_agmA ha hb hab n

/-- The b-sequence is bounded above by a₀. -/
theorem agmB_bddAbove : BddAbove (range (agmB a b)) := by
  refine ⟨a, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  calc agmB a b n
      ≤ agmA a b n := agmB_le_agmA ha hb hab n
    _ ≤ agmA a b 0 := agmA_antitone ha hb hab (Nat.zero_le n)
    _ = a := agmA_zero a b

/-- The a-sequence converges (antitone + bounded below). -/
theorem agmA_tendsto :
    Tendsto (agmA a b) atTop (nhds (⨅ n, agmA a b n)) :=
  tendsto_atTop_ciInf (agmA_antitone ha hb hab) (agmA_bddBelow ha hb hab)

/-- The b-sequence converges (monotone + bounded above). -/
theorem agmB_tendsto :
    Tendsto (agmB a b) atTop (nhds (⨆ n, agmB a b n)) :=
  tendsto_atTop_ciSup (agmB_monotone ha hb hab) (agmB_bddAbove ha hb hab)

/-- The gap tends to 0. -/
theorem gap_tendsto_zero :
    Tendsto (fun n => agmA a b n - agmB a b n) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n; linarith [agmB_le_agmA ha hb hab n]
  · exact fun n => gap_bound ha hb hab n
  · -- (a-b)/2^n → 0 as n → ∞
    have : Tendsto (fun n : ℕ => (a - b) * ((1 : ℝ) / 2) ^ n) atTop (nhds ((a - b) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)).const_mul _
    simp only [mul_zero] at this
    convert this using 1
    ext n; ring

/-- **Both sequences converge to the same limit.** -/
theorem agm_common_limit :
    ⨅ n, agmA a b n = ⨆ n, agmB a b n := by
  -- The a-limit ≥ b-limit since aₙ ≥ bₙ for all n
  have h_le : ⨆ n, agmB a b n ≤ ⨅ n, agmA a b n := by
    apply ciSup_le (fun n => ?_)
    exact le_ciInf (fun m => by
      calc agmB a b n
          ≤ agmB a b (max n m) := agmB_monotone ha hb hab (le_max_left n m)
        _ ≤ agmA a b (max n m) := agmB_le_agmA ha hb hab (max n m)
        _ ≤ agmA a b m := agmA_antitone ha hb hab (le_max_right n m))
  -- The a-limit - b-limit = 0 since gap → 0
  have h_diff : ⨅ n, agmA a b n - ⨆ n, agmB a b n = 0 := by
    have htA := agmA_tendsto ha hb hab
    have htB := agmB_tendsto ha hb hab
    have htgap := gap_tendsto_zero ha hb hab
    have : Tendsto (fun n => agmA a b n - agmB a b n) atTop
        (nhds (⨅ n, agmA a b n - ⨆ n, agmB a b n)) :=
      htA.sub htB
    exact tendsto_nhds_unique this htgap
  linarith

-- ============================================================================
-- § 6. The AGM Value
-- ============================================================================

/-- The arithmetic-geometric mean M(a,b). -/
noncomputable def agm (a b : ℝ) : ℝ := ⨅ n, agmA a b n

/-- The AGM is the common limit of both sequences. -/
theorem agm_eq_limit_A : Tendsto (agmA a b) atTop (nhds (agm a b)) := by
  exact agmA_tendsto ha hb hab

theorem agm_eq_limit_B : Tendsto (agmB a b) atTop (nhds (agm a b)) := by
  rw [agm, agm_common_limit ha hb hab]
  exact agmB_tendsto ha hb hab

/-- The AGM lies between b and a. -/
theorem agm_bounds : b ≤ agm a b ∧ agm a b ≤ a := by
  constructor
  · -- agm ≥ b: since bₙ ≤ agm for all n, and b₀ = b
    have : agmB a b 0 ≤ agm a b := by
      rw [agm]
      calc agmB a b 0
          ≤ agmA a b 0 := agmB_le_agmA ha hb hab 0
        _ ≥ ⨅ n, agmA a b n := ciInf_le (agmA_bddBelow ha hb hab) 0
    rwa [agmB_zero] at this
  · -- agm ≤ a: since aₙ ≥ agm for all n, and a₀ = a
    have : agm a b ≤ agmA a b 0 :=
      ciInf_le (agmA_bddBelow ha hb hab) 0
    rwa [agmA_zero] at this

-- ============================================================================
-- § 7. Connection to Elliptic Integrals (Axiomatized)
-- ============================================================================

/-
Gauss's remarkable discovery (1799): The AGM is connected to elliptic integrals.

The complete elliptic integral of the first kind is:
  K(k) = ∫₀^{π/2} dθ / √(1 - k²sin²θ)

Gauss proved: M(a, b) = a · π / (2 · K(√(1 - (b/a)²)))

In particular: M(1, 1/√2) = π / (2K(1/√2))

This means the AGM provides an efficient algorithm for computing π via
elliptic integrals — the iteration converges quadratically.

These are axiomatized since Mathlib does not contain elliptic integrals.
-/

/-- Complete elliptic integral of the first kind K(k).
    Not yet in Mathlib — axiomatized. -/
axiom ellipticK : ℝ → ℝ

/-- K(0) = π/2 (degenerate case: integral of 1). -/
axiom ellipticK_zero : ellipticK 0 = π / 2

/-- **Gauss's AGM–Elliptic Integral Theorem:**
    M(a, b) = a · π / (2 · K(√(1 - (b/a)²)))
    for a ≥ b > 0 and complementary modulus k' = b/a. -/
axiom agm_ellipticK (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    agm a b = a * π / (2 * ellipticK (Real.sqrt (1 - (b / a) ^ 2)))

end AmgmInequalityOQ04
