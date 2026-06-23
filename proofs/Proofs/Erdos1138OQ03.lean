/-
  Erdős Problem #1138 — Prime Gap Bounds (OQ-03)

  Extends the formalization in Erdos1138Problem.lean with:
  1. prime_gap_le_prev_prime: proved via Bertrand's postulate (was axiom)
  2. maxPrimeGap_le_half: proved from (1) (was axiom)
  3. cramer_implies_gap_sublinear: proved (was sorry)
  4. Monotonicity, BddAbove, and empty-set properties
  5. Baker-Harman-Pintz bound (axiom — deep unconditional result)

  References:
  - Bertrand/Chebyshev: ∃ prime in (n, 2n] (Mathlib: Nat.bertrand)
  - Cramér (1936): On the order of the prime gaps
  - Baker-Harman-Pintz (2001): The difference between consecutive primes
-/

import Mathlib

set_option maxHeartbeats 400000

open Finset Set

namespace Erdos1138OQ03

noncomputable section

-- ============================================================================
-- Part I: Definitions
-- ============================================================================

/-- The set of prime gaps below x. -/
def primeGapSet (x : ℕ) : Set ℕ :=
  {d | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q ≤ x ∧
    (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ d = q - p}

/-- The maximal prime gap below x. -/
def maxPrimeGap (x : ℕ) : ℕ :=
  sSup (primeGapSet x)

-- ============================================================================
-- Part II: BddAbove and Basic Bounds
-- ============================================================================

/-- Every prime gap below x is at most x. -/
theorem primeGap_le_x {x d : ℕ} (hd : d ∈ primeGapSet x) : d ≤ x := by
  obtain ⟨p, q, _, _, _, hqx, _, hdeq⟩ := hd
  calc d = q - p := hdeq
    _ ≤ q := Nat.sub_le q p
    _ ≤ x := hqx

/-- The prime gap set below x is bounded above by x. -/
theorem primeGapSet_bddAbove (x : ℕ) : BddAbove (primeGapSet x) :=
  ⟨x, fun _ hd => primeGap_le_x hd⟩

/-- The maximal prime gap below x is at most x. -/
theorem maxPrimeGap_le (x : ℕ) : maxPrimeGap x ≤ x := by
  unfold maxPrimeGap
  by_cases h : (primeGapSet x).Nonempty
  · exact csSup_le h fun d hd => primeGap_le_x hd
  · rw [Set.not_nonempty_iff_eq_empty.mp h]; simp [csSup_empty]

-- ============================================================================
-- Part III: Prime Gap Set Properties
-- ============================================================================

/-- The prime gap set below 0 is empty. -/
theorem primeGapSet_zero : primeGapSet 0 = ∅ := by
  ext d; simp only [primeGapSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, q, _, _, _, hq, _, _⟩; omega

/-- The prime gap set below 1 is empty. -/
theorem primeGapSet_one : primeGapSet 1 = ∅ := by
  ext d; simp only [primeGapSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, q, _, hq_prime, _, hq_le, _, _⟩; have := hq_prime.two_le; omega

/-- The prime gap set below 2 is empty. -/
theorem primeGapSet_two : primeGapSet 2 = ∅ := by
  ext d; simp only [primeGapSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨p, q, hp, hq, hpq, hq2, _, _⟩; have := hp.two_le; have := hq.two_le; omega

/-- maxPrimeGap 2 = 0. -/
theorem maxPrimeGap_le_two : maxPrimeGap 2 = 0 := by
  unfold maxPrimeGap; rw [primeGapSet_two]; simp [csSup_empty (α := ℕ)]

-- ============================================================================
-- Part IV: Bertrand-Based Bounds (PROVED, was axiom)
-- ============================================================================

/-- Any prime gap d = q - p satisfies d ≤ p.
    Proved from Bertrand's postulate (Nat.bertrand): ∃ prime r, p < r ≤ 2p.
    Since q is the next prime after p, q ≤ r ≤ 2p, so q - p ≤ p. -/
theorem prime_gap_le_prev_prime (p q : ℕ) (hp : Nat.Prime p) (_hq : Nat.Prime q)
    (hpq : p < q) (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    q - p ≤ p := by
  have hp_pos : p ≠ 0 := hp.ne_zero
  obtain ⟨r, hr_prime, hpr, hr2p⟩ := Nat.bertrand p hp_pos
  have hqr := hcons r hr_prime hpr
  omega

/-- The maximal gap below x is at most x / 2 for x ≥ 25.
    Proved from prime_gap_le_prev_prime: each gap d = q-p ≤ p,
    so 2d ≤ d + p = q ≤ x, giving d ≤ x/2. -/
theorem maxPrimeGap_le_half (x : ℕ) (_hx : 25 ≤ x) :
    maxPrimeGap x ≤ x / 2 := by
  unfold maxPrimeGap
  by_cases h : (primeGapSet x).Nonempty
  · apply csSup_le h
    intro d ⟨p, q, hp, hq, hpq, hqx, hcons, hdeq⟩
    subst hdeq
    have hgap := prime_gap_le_prev_prime p q hp hq hpq hcons
    omega
  · rw [Set.not_nonempty_iff_eq_empty.mp h]; simp [csSup_empty (α := ℕ)]

-- ============================================================================
-- Part V: Monotonicity
-- ============================================================================

/-- The prime gap set is monotone in x. -/
theorem primeGapSet_mono {x y : ℕ} (hxy : x ≤ y) :
    primeGapSet x ⊆ primeGapSet y := by
  intro d ⟨p, q, hp, hq, hpq, hqx, hcons, hdeq⟩
  exact ⟨p, q, hp, hq, hpq, le_trans hqx hxy, hcons, hdeq⟩

/-- maxPrimeGap is monotone. -/
theorem maxPrimeGap_mono {x y : ℕ} (hxy : x ≤ y) :
    maxPrimeGap x ≤ maxPrimeGap y := by
  unfold maxPrimeGap
  by_cases h : (primeGapSet x).Nonempty
  · exact csSup_le_csSup (primeGapSet_bddAbove y) h (primeGapSet_mono hxy)
  · rw [Set.not_nonempty_iff_eq_empty.mp h]; simp [csSup_empty (α := ℕ)]

-- ============================================================================
-- Part VI: Cramér Sublinearity (PROVED, was sorry)
-- ============================================================================

/-- (log x)² = o(x): for any ε > 0 and C > 0, C·(log x)² ≤ ε·x eventually.

    Uses Real.log_le_rpow_div: log x ≤ x^δ/δ for x ≥ 0, δ > 0.
    With δ = 1/4: log x ≤ 4·x^(1/4), so (log x)² ≤ 16·x^(1/2).
    Then 16C·x^(1/2) ≤ ε·x when x ≥ (16C/ε)². -/
theorem cramer_implies_gap_sublinear :
    ∀ ε : ℝ, 0 < ε →
      ∀ C : ℝ, 0 < C →
        ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
          C * (Real.log x) ^ 2 ≤ ε * x := by
  intro ε hε C hC
  refine ⟨Nat.ceil ((16 * C / ε) ^ 2) + 1, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0; simp [Real.log_zero]
  have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx0)
  have hx_nn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx_pos
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx0
  -- Step 1: log x ≤ 4 · x^(1/4)
  have hlog : Real.log (x : ℝ) ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div hx_nn (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show (x : ℝ) ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) =
      4 * (x : ℝ) ^ ((1 : ℝ) / 4) from by ring]
  -- Step 2: (log x)² ≤ 16 · x^(1/2) (squaring, using rpow_mul)
  have hlog_sq : Real.log (x : ℝ) ^ 2 ≤ 16 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hlog_nn : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
    calc Real.log (x : ℝ) ^ 2
        ≤ (4 * (x : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := sq_le_sq' (by linarith) hlog
      _ = 16 * ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
      _ = 16 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
          congr 1
          rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 4)) 2,
              ← Real.rpow_mul hx_nn]
          norm_num
  -- Step 3: x^(1/2) · x^(1/2) = x
  have hrpow_sq : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
    rw [← Real.rpow_add hx_pos]; norm_num
  -- Step 4: (16C/ε)² ≤ x
  have hbound : (16 * C / ε) ^ 2 ≤ (x : ℝ) := by
    calc (16 * C / ε) ^ 2
        ≤ ↑(Nat.ceil ((16 * C / ε) ^ 2)) := Nat.le_ceil _
      _ ≤ ↑(Nat.ceil ((16 * C / ε) ^ 2) + 1) := by push_cast; linarith
      _ ≤ (x : ℝ) := by exact_mod_cast hx
  -- Step 5: 16C/ε ≤ x^(1/2) (from squaring inequality)
  have hCε_nn : 0 ≤ 16 * C / ε := by positivity
  have hrpow_nn : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx_nn _
  have hsqrt : 16 * C / ε ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have key : (16 * C / ε) ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
      rw [sq ((x : ℝ) ^ ((1 : ℝ) / 2)), hrpow_sq]; exact hbound
    nlinarith [sq_nonneg (((x : ℝ) ^ ((1 : ℝ) / 2)) - 16 * C / ε)]
  -- Step 6: 16C · x^(1/2) ≤ ε · x
  have h16C : 16 * C ≤ ε * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    calc 16 * C = ε * (16 * C / ε) := by field_simp
      _ ≤ ε * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hsqrt (le_of_lt hε)
  -- Final: C · (log x)² ≤ 16C · x^(1/2) ≤ ε · x^(1/2) · x^(1/2) = ε · x
  calc C * Real.log (x : ℝ) ^ 2
      ≤ C * (16 * (x : ℝ) ^ ((1 : ℝ) / 2)) := by nlinarith
    _ = 16 * C * (x : ℝ) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ ε * (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h16C hrpow_nn
    _ = ε * (x : ℝ) := by rw [mul_assoc, hrpow_sq]

-- ============================================================================
-- Part VII: Deep Unconditional Bound (axiom)
-- ============================================================================

/-- Baker-Harman-Pintz (2001): d ≤ x^{0.525} unconditionally. -/
axiom baker_harman_pintz (x : ℕ) (hx : 25 ≤ x) :
    (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ (0.525 : ℝ)

end

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Results

### Proved (0 sorries):
  1. primeGap_le_x: every gap ≤ x
  2. primeGapSet_bddAbove: BddAbove
  3. maxPrimeGap_le: sSup ≤ x
  4. prime_gap_le_prev_prime: gap ≤ prev prime (Bertrand) [was axiom]
  5. maxPrimeGap_le_half: gap ≤ x/2 for x ≥ 25 [was axiom]
  6. primeGapSet_mono, maxPrimeGap_mono: monotonicity
  7. cramer_implies_gap_sublinear: C·(log x)² = o(x) [was sorry]

### Axioms (deep results not in Mathlib):
  - baker_harman_pintz (BHP 2001 unconditional bound)
-/

end Erdos1138OQ03
