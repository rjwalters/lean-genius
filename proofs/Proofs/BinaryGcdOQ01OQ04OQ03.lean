/-
  Binary GCD Average-Case: an O(log N) ceiling on the mean step count
  Open Question OQ-01-OQ-04-OQ-03 from BinaryGcdOQ01OQ04

  Motivation (Brent 1976). On random inputs the expected number of binary-GCD
  steps grows like ≈ 0.7050 · log₂ max(a, b). Verifying that *constant* in Lean
  is a substantial program: the 0.7050 figure has no closed form and is obtained
  from a transfer-operator / dynamical-systems analysis of the Euclidean-type
  map (Brent 1976; Vallée, dynamical analysis of gcd algorithms). Mathlib 4.26
  has the measure theory but none of the spectral machinery needed to pin the
  leading constant, so the sharp average-case theorem is OUT OF REACH here.

  What IS provable — and what this file contributes — is the *order* of the
  average, i.e. the ceiling that Brent's constant sharpens:

      the mean of binaryGcdSteps a b over b ∈ [1, N] is O(log N).

  Concretely we bound the total step count summed over the range by N times the
  deterministic worst-case bound from BinaryGcdOQ01:

      ∑_{b=1}^{N} binaryGcdSteps a b ≤ N · (2·(log₂ a + log₂ N) + 2)

  so the average is ≤ 2·(log₂ a + log₂ N) + 2 = O(log N). This is the first
  verified average-case statement for the (1, 2^n − 1) worst-case family's
  gallery entry. It is an honest ceiling, not the Brent constant: the matching
  Ω(log N) average lower bound (which would give Θ(log N)) requires a density
  count over the range, and the sharp 0.7050 constant requires the dynamical
  analysis above — both remain open here.

  References:
  - Brent (1976), "Analysis of the binary Euclidean algorithm"
  - BinaryGcdOQ01.lean  (worst-case: binaryGcdSteps ≤ 2·(log₂ a + log₂ b) + 2)
  - BinaryGcdOQ01OQ04.lean  (worst-case tight family (1, 2^n − 1) takes n steps)
-/
import Mathlib
import Proofs.BinaryGcdOQ01

namespace BinaryGcdOQ01OQ04OQ03

open BinaryGcdOQ01 Nat

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE AVERAGE-CASE OBJECT
-- ═══════════════════════════════════════════════════════════════════

/-- Total binary-GCD step count summed over `b ∈ [1, N]`, for a fixed left
    argument `a`. Dividing by `N` gives the average step count of the Brent
    setup (uniform second argument in a range). -/
noncomputable def totalSteps (a N : ℕ) : ℕ :=
  ∑ b ∈ Finset.Icc 1 N, binaryGcdSteps a b

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE O(log N) AVERAGE-CASE CEILING
-- ═══════════════════════════════════════════════════════════════════

/-- **Total-sum bound.** For `a ≥ 1`, the total step count over `b ∈ [1, N]`
    is at most `N` times the deterministic worst-case bound at `b = N`:

      ∑_{b=1}^{N} binaryGcdSteps a b ≤ N · (2·(log₂ a + log₂ N) + 2).

    Each summand is bounded by the worst-case estimate `binaryGcdSteps_le_log`,
    and `log₂ b ≤ log₂ N` since `b ≤ N`; summing the constant bound over the
    `N`-element range `[1, N]` gives the factor `N`. -/
theorem totalSteps_le (a N : ℕ) (ha : 0 < a) :
    totalSteps a N ≤ N * (2 * (Nat.log 2 a + Nat.log 2 N) + 2) := by
  unfold totalSteps
  calc ∑ b ∈ Finset.Icc 1 N, binaryGcdSteps a b
      ≤ ∑ _b ∈ Finset.Icc 1 N, (2 * (Nat.log 2 a + Nat.log 2 N) + 2) := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.mem_Icc] at hb
        have hb0 : 0 < b := hb.1
        have hbN : Nat.log 2 b ≤ Nat.log 2 N := Nat.log_mono_right hb.2
        calc binaryGcdSteps a b
            ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2 := binaryGcdSteps_le_log a b ha hb0
          _ ≤ 2 * (Nat.log 2 a + Nat.log 2 N) + 2 := by omega
    _ = N * (2 * (Nat.log 2 a + Nat.log 2 N) + 2) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

/-- **Average-case ceiling (rational form).** For `a, N ≥ 1`, the average step
    count over `b ∈ [1, N]` is `O(log N)`:

      (∑_{b=1}^{N} binaryGcdSteps a b) / N ≤ 2·(log₂ a + log₂ N) + 2.

    This is the order that Brent's `≈ 0.7050 · log₂ max(a,b)` sharpens; the
    constant itself is not accessible from Mathlib (see file header). -/
theorem avgSteps_le (a N : ℕ) (ha : 0 < a) (hN : 0 < N) :
    (totalSteps a N : ℚ) / (N : ℚ) ≤ 2 * (Nat.log 2 a + Nat.log 2 N) + 2 := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  rw [div_le_iff₀ hNQ]
  have h : (totalSteps a N : ℚ)
      ≤ ((N * (2 * (Nat.log 2 a + Nat.log 2 N) + 2) : ℕ) : ℚ) := by
    exact_mod_cast totalSteps_le a N ha
  calc (totalSteps a N : ℚ)
      ≤ ((N * (2 * (Nat.log 2 a + Nat.log 2 N) + 2) : ℕ) : ℚ) := h
    _ = (2 * (Nat.log 2 a + Nat.log 2 N) + 2) * (N : ℚ) := by push_cast; ring

-- ═══════════════════════════════════════════════════════════════════
-- PART III: CONCRETE VERIFICATIONS
-- ═══════════════════════════════════════════════════════════════════

-- Small-range totals, computed directly (sanity checks on the definition):
example : totalSteps 1 1 = binaryGcdSteps 1 1 := by
  simp [totalSteps]
example : totalSteps 3 4
    = binaryGcdSteps 3 1 + binaryGcdSteps 3 2 + binaryGcdSteps 3 3 + binaryGcdSteps 3 4 := by
  simp [totalSteps, Finset.sum_Icc_succ_top]

-- The total-sum bound holds at a concrete point (a = 3, N = 4):
--   totalSteps 3 4 ≤ 4 · (2·(log₂ 3 + log₂ 4) + 2)
example : totalSteps 3 4 ≤ 4 * (2 * (Nat.log 2 3 + Nat.log 2 4) + 2) :=
  totalSteps_le 3 4 (by norm_num)

end BinaryGcdOQ01OQ04OQ03
