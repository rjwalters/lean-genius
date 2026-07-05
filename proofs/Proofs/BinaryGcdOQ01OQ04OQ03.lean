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

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE a = 1 ROW IS EXACTLY LOGARITHMIC  (tight Θ(log N))
-- ═══════════════════════════════════════════════════════════════════
--
-- The O(log N) ceiling above is matched exactly on the a = 1 row: for EVERY
-- b ≥ 1 (not just the sparse worst-case family 2^n − 1),
--     binaryGcdSteps 1 b = Nat.log 2 b + 1,
-- because from (1, b) the algorithm floor-halves b at every step
-- (b ↦ ⌊b/2⌋). Summing over b ∈ [1, N] pins the a = 1 average at
--     totalSteps 1 N = (∑_{b=1}^N log₂ b) + N = Θ(N log N),
-- so the a = 1 average step count is Θ(log N): the O(log N) ceiling is tight.
-- This strictly generalises the parent's binaryGcdSteps 1 (2^n − 1) = n
-- (BinaryGcdOQ01OQ04.lean) from the sparse family to the whole row.

/-- One binary-GCD step from `(1, 2k)`: the even branch sends `b = 2k ↦ k`. -/
private theorem binaryGcdSteps_one_two_mul (k : ℕ) (hk : 1 ≤ k) :
    binaryGcdSteps 1 (2 * k) = 1 + binaryGcdSteps 1 k := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, show 2 * k = (2 * k - 1) + 1 from by omega,
      binaryGcdSteps.eq_3]
  simp only [if_neg (show (0 + 1) % 2 ≠ 0 from by norm_num),
             if_pos (show ((2 * k - 1) + 1) % 2 = 0 from by omega),
             show (0 : ℕ) + 1 = 1 from rfl,
             show ((2 * k - 1) + 1) / 2 = k from by omega]

/-- One binary-GCD step from `(1, 2k+1)`: the odd branch sends `b = 2k+1 ↦ k`. -/
private theorem binaryGcdSteps_one_two_mul_add_one (k : ℕ) :
    binaryGcdSteps 1 (2 * k + 1) = 1 + binaryGcdSteps 1 k := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, binaryGcdSteps.eq_3]
  simp only [if_neg (show (0 + 1) % 2 ≠ 0 from by norm_num),
             if_neg (show (2 * k + 1) % 2 ≠ 0 from by omega),
             if_neg (show ¬(0 + 1 > 2 * k + 1) from by omega),
             show (0 : ℕ) + 1 = 1 from rfl,
             show (2 * k + 1 - 1) / 2 = k from by omega]

/-- Unified one-step reduction: from `(1, b)` with `b ≥ 1` the algorithm takes
    one step to `(1, ⌊b/2⌋)`, regardless of the parity of `b`. -/
theorem binaryGcdSteps_one_step (b : ℕ) (hb : 1 ≤ b) :
    binaryGcdSteps 1 b = 1 + binaryGcdSteps 1 (b / 2) := by
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hd : b / 2 = k := by omega
    have hkpos : 1 ≤ k := by omega
    rw [hd, show b = 2 * k from by omega, binaryGcdSteps_one_two_mul k hkpos]
  · have hd : b / 2 = k := by omega
    rw [hd, hk, binaryGcdSteps_one_two_mul_add_one k]

private theorem binaryGcdSteps_one_eq_log_aux :
    ∀ b, 1 ≤ b → binaryGcdSteps 1 b = Nat.log 2 b + 1 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    rcases Nat.lt_or_ge b 2 with hb1 | hb2
    · have hb11 : b = 1 := by omega
      subst hb11
      rw [binaryGcdSteps_one_step 1 le_rfl]
      simp [Nat.log_one_right]
    · have hstep := binaryGcdSteps_one_step b (by omega)
      have hhalf1 : 1 ≤ b / 2 := by omega
      have hhalflt : b / 2 < b := by omega
      have hih := ih (b / 2) hhalflt hhalf1
      have hlogpos : 0 < Nat.log 2 b := Nat.log_pos (by norm_num) hb2
      have hlog : Nat.log 2 (b / 2) = Nat.log 2 b - 1 := Nat.log_div_base 2 b
      rw [hstep, hih]; omega

/-- **Exact `a = 1` step count.** For every `b ≥ 1`,
    `binaryGcdSteps 1 b = Nat.log 2 b + 1`. The algorithm floor-halves `b`
    each step, so it runs for exactly `⌊log₂ b⌋ + 1` steps. This generalises
    the parent's `binaryGcdSteps 1 (2^n − 1) = n` from the sparse worst-case
    family to *every* second argument. -/
theorem binaryGcdSteps_one_eq_log (b : ℕ) (hb : 1 ≤ b) :
    binaryGcdSteps 1 b = Nat.log 2 b + 1 :=
  binaryGcdSteps_one_eq_log_aux b hb

/-- **Exact `a = 1` average.** The total step count over `b ∈ [1, N]` on the
    `a = 1` row is `(∑_{b=1}^N log₂ b) + N`. Since `∑_{b=1}^N log₂ b = Θ(N log N)`,
    the `a = 1` average step count is `Θ(log N)` — the `O(log N)` ceiling of
    `avgSteps_le` is tight, matching the order of Brent's average-case result. -/
theorem totalSteps_one_eq (N : ℕ) :
    totalSteps 1 N = (∑ b ∈ Finset.Icc 1 N, Nat.log 2 b) + N := by
  unfold totalSteps
  rw [Finset.sum_congr rfl
        (fun b hb => binaryGcdSteps_one_eq_log b (Finset.mem_Icc.mp hb).1),
      Finset.sum_add_distrib]
  congr 1
  simp [Nat.card_Icc]

end BinaryGcdOQ01OQ04OQ03
