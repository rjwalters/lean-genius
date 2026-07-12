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
  gallery entry. It is an honest ceiling, not the Brent constant.

  On the a = 1 row this ceiling is now shown TIGHT: `totalSteps_one_eq` gives the
  exact total `(∑_{b=1}^N log₂ b) + N`, and `totalSteps_one_ge` supplies the
  matching `Ω(N·log N)` lower bound `(N − ⌊N/2⌋)·(log₂ N − 1) ≤ totalSteps 1 N`
  (obtained by an elementary upper-half density count over the range), so the
  a = 1 average step count is a genuine `Θ(log N)` — the order of Brent's result.
  The sharp `0.7050` leading constant still requires the dynamical (transfer-
  operator) analysis above and remains out of reach here.

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

-- ═══════════════════════════════════════════════════════════════════
-- PART V: THE MATCHING Ω(N·log N) LOWER BOUND  (a = 1 row)  ⇒  Θ
-- ═══════════════════════════════════════════════════════════════════
--
-- `totalSteps_one_eq` gives an *exact* total, but only over the abstract sum
-- `∑ log₂ b`. To make the `Ω(N log N)` order explicit — and hence pin the
-- `a = 1` average at a genuine `Θ(log N)`, matching the ORDER of Brent's
-- average-case result — we bound the total below by restricting the sum to the
-- upper half of the range. For every `b` in `(N/2, N]` we have
-- `log₂ b ≥ log₂ ⌊N/2⌋ = log₂ N − 1`, and there are `⌈N/2⌉ = N − ⌊N/2⌋` such
-- terms, giving `∑_{b=1}^N log₂ b ≥ (N − ⌊N/2⌋)·(log₂ N − 1)`.

/-- **Matching Ω(N·log N) lower bound (a = 1 row).**  The total step count over
    `b ∈ [1, N]` on the `a = 1` row is at least `(N − ⌊N/2⌋)·(log₂ N − 1)`.
    Together with the `O(log N)` ceiling (`avgSteps_le`) and the exact form
    (`totalSteps_one_eq`) this pins the `a = 1` average at `Θ(log N)`, closing the
    file header's stated open sub-goal (the matching averaged lower bound).

    Proof: restrict the sum `∑_{b=1}^N log₂ b` to the upper half `b ∈ (⌊N/2⌋, N]`.
    Each such `b ≥ ⌊N/2⌋`, so `log₂ b ≥ log₂ ⌊N/2⌋ = log₂ N − 1`
    (`Nat.log_mono_right`, `Nat.log_div_base`); the sub-range has
    `N − ⌊N/2⌋` elements. -/
theorem totalSteps_one_ge (N : ℕ) :
    (N - N / 2) * (Nat.log 2 N - 1) ≤ totalSteps 1 N := by
  rw [totalSteps_one_eq]
  refine le_trans ?_ (Nat.le_add_right _ N)
  have hsub : Finset.Icc (N / 2 + 1) N ⊆ Finset.Icc 1 N := by
    intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  calc (N - N / 2) * (Nat.log 2 N - 1)
      = ∑ _b ∈ Finset.Icc (N / 2 + 1) N, (Nat.log 2 N - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]; congr 1; omega
    _ ≤ ∑ b ∈ Finset.Icc (N / 2 + 1) N, Nat.log 2 b := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.mem_Icc] at hb
        have hmono : Nat.log 2 (N / 2) ≤ Nat.log 2 b :=
          Nat.log_mono_right (by omega)
        rw [Nat.log_div_base] at hmono
        exact hmono
    _ ≤ ∑ b ∈ Finset.Icc 1 N, Nat.log 2 b :=
        Finset.sum_le_sum_of_subset hsub

/-- **Average-level Ω(log N) lower bound (a = 1 row).** Dividing the total lower
    bound `totalSteps_one_ge` by `N` and using `N ≤ 2·(N − ⌊N/2⌋)` (i.e. the upper
    half `(⌊N/2⌋, N]` is at least half of `[1, N]`) gives an average-case lower
    bound with an `N`-independent coefficient:

      (∑_{b=1}^{N} binaryGcdSteps 1 b) / N ≥ (log₂ N − 1) / 2.

    This is the rational-form counterpart of the integer total bound
    `totalSteps_one_ge`, matching the *rational* `O(log N)` ceiling `avgSteps_le`
    (which at `a = 1` reads `≤ 2·log₂ N + 2`). Together they sandwich the `a = 1`
    average between `(log₂ N − 1)/2` and `2·log₂ N + 2` — an explicit `Θ(log N)` at
    the average level, matching the *order* of Brent's average-case result. The
    sharp `0.7050` leading constant remains out of reach (see file header). -/
theorem avgSteps_one_ge (N : ℕ) (hN : 0 < N) :
    ((Nat.log 2 N : ℚ) - 1) / 2 ≤ (totalSteps 1 N : ℚ) / (N : ℚ) := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  -- clear both denominators: goal becomes  (log₂ N − 1)·N ≤ (totalSteps 1 N)·2
  rw [le_div_iff₀ hNQ, div_mul_eq_mul_div,
    div_le_iff₀ (show (0 : ℚ) < 2 by norm_num)]
  -- reduce to the ℕ inequality  N · (log₂ N − 1) ≤ 2 · totalSteps 1 N
  have key : N * (Nat.log 2 N - 1) ≤ 2 * totalSteps 1 N := by
    have h2 : N ≤ 2 * (N - N / 2) := by omega
    have hge := totalSteps_one_ge N
    calc N * (Nat.log 2 N - 1)
        ≤ (2 * (N - N / 2)) * (Nat.log 2 N - 1) := by gcongr
      _ = 2 * ((N - N / 2) * (Nat.log 2 N - 1)) := by ring
      _ ≤ 2 * totalSteps 1 N := by omega
  have keyQ : (N : ℚ) * ((Nat.log 2 N - 1 : ℕ) : ℚ) ≤ 2 * (totalSteps 1 N : ℚ) := by
    exact_mod_cast key
  -- bridge the ℕ truncated subtraction `log₂ N − 1` up to the ℚ subtraction
  have hle : (Nat.log 2 N : ℚ) - 1 ≤ ((Nat.log 2 N - 1 : ℕ) : ℚ) := by
    rcases Nat.eq_zero_or_pos (Nat.log 2 N) with h0 | h1
    · rw [h0]; norm_num
    · rw [Nat.cast_sub h1]; norm_num
  have hNnn : (0 : ℚ) ≤ (N : ℚ) := le_of_lt hNQ
  calc ((Nat.log 2 N : ℚ) - 1) * (N : ℚ)
      ≤ ((Nat.log 2 N - 1 : ℕ) : ℚ) * (N : ℚ) := mul_le_mul_of_nonneg_right hle hNnn
    _ = (N : ℚ) * ((Nat.log 2 N - 1 : ℕ) : ℚ) := by ring
    _ ≤ 2 * (totalSteps 1 N : ℚ) := keyQ
    _ = (totalSteps 1 N : ℚ) * 2 := by ring

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: EXACT CLOSED FORM AT DYADIC ENDPOINTS  (a = 1 row)
-- ═══════════════════════════════════════════════════════════════════
--
-- `totalSteps_one_eq` gives the exact total only as the abstract sum
-- `(∑_{b=1}^N log₂ b) + N`. At the dyadic endpoints `N = 2^n` that sum has a
-- genuine closed form, so the `a = 1` total is pinned exactly:
--
--     totalSteps 1 (2^n) = (n − 1)·2^n + n + 2
--       (subtraction-free:  totalSteps 1 (2^n) + 2^n = n·2^n + n + 2).
--
-- The leading term `(n − 1)·2^n = N·log₂N − N` fixes the exact constant `1` on
-- the `N·log₂N` term of the a = 1 total — the elementary, fully-verified
-- analogue of Brent's (Mathlib-inaccessible) 0.7050 average constant. The proof
-- decomposes `[1, 2^n)` into the dyadic blocks `[2^k, 2^{k+1})` on each of which
-- `binaryGcdSteps 1 b` is the constant `k + 1`.

/-- One dyadic block `[2^n, 2^{n+1})` contributes exactly `(n+1)·2^n` to the
    `a = 1` total: it has `2^n` elements and `binaryGcdSteps 1 b = log₂ b + 1
    = n + 1` throughout (every `b` in the block has `log₂ b = n`). -/
private theorem block_sum_one (n : ℕ) :
    ∑ b ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), binaryGcdSteps 1 b = (n + 1) * 2 ^ n := by
  have hval : ∀ b ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), binaryGcdSteps 1 b = n + 1 := by
    intro b hb
    rw [Finset.mem_Ico] at hb
    have hb1 : 1 ≤ b := le_trans Nat.one_le_two_pow hb.1
    have hlog : Nat.log 2 b = n := Nat.log_eq_of_pow_le_of_lt_pow hb.1 hb.2
    rw [binaryGcdSteps_one_eq_log b hb1, hlog]
  have hp : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Ico, hp, smul_eq_mul]
  have hc : 2 * 2 ^ n - 2 ^ n = 2 ^ n := by omega
  rw [hc]; ring

/-- Accumulated `a = 1` total over the half-open dyadic prefix `[1, 2^n)`:
    `(∑_{b=1}^{2^n − 1} binaryGcdSteps 1 b) + 2^n = n·2^n + 1`
    (subtraction-free form of `∑ = (n−1)·2^n + 1`). Proved by induction on `n`,
    each step absorbing one dyadic block via `block_sum_one`. -/
private theorem sum_Ico_one_pow_two (n : ℕ) :
    (∑ b ∈ Finset.Ico 1 (2 ^ n), binaryGcdSteps 1 b) + 2 ^ n = n * 2 ^ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ b ∈ Finset.Ico 1 (2 ^ (n + 1)), binaryGcdSteps 1 b
        = (∑ b ∈ Finset.Ico 1 (2 ^ n), binaryGcdSteps 1 b)
          + ∑ b ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), binaryGcdSteps 1 b :=
      (Finset.sum_Ico_consecutive _ Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))).symm
    have hp : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    rw [hsplit, block_sum_one n, hp]
    zify at ih ⊢
    linear_combination ih

/-- **Exact `a = 1` total at dyadic endpoints (`N = 2^n`).**
    `totalSteps 1 (2^n) + 2^n = n·2^n + n + 2`, i.e.
    `totalSteps 1 (2^n) = (n − 1)·2^n + n + 2`. This replaces the abstract
    `∑ log₂ b` of `totalSteps_one_eq` by a closed form on the dyadic subsequence,
    exhibiting the exact leading constant `1` on the `N·log₂N = n·2^n` term of the
    `a = 1` average-case total. -/
theorem totalSteps_one_pow_two (n : ℕ) :
    totalSteps 1 (2 ^ n) + 2 ^ n = n * 2 ^ n + n + 2 := by
  unfold totalSteps
  have hlog2 : Nat.log 2 (2 ^ n) = n :=
    Nat.log_eq_of_pow_le_of_lt_pow (le_refl _)
      (by rw [pow_succ]; have hp : 0 < 2 ^ n := pow_pos (by norm_num) n; omega)
  have hins : Finset.Icc 1 (2 ^ n) = insert (2 ^ n) (Finset.Ico 1 (2 ^ n)) :=
    (Finset.Ico_insert_right Nat.one_le_two_pow).symm
  rw [hins, Finset.sum_insert (by simp), binaryGcdSteps_one_eq_log (2 ^ n) Nat.one_le_two_pow,
      hlog2]
  have hIco := sum_Ico_one_pow_two n
  omega

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: EXACT CLOSED FORM AT EVERY N  (a = 1 row)
-- ═══════════════════════════════════════════════════════════════════
--
-- `totalSteps_one_pow_two` pins the a = 1 total only on the dyadic subsequence
-- N = 2^n.  Extending across the partial final block `(2^n, N]` — on which
-- `binaryGcdSteps 1 b = n + 1` is constant — pins the a = 1 total EXACTLY at
-- EVERY N, subsuming both `totalSteps_one_eq` (removes the abstract ∑ log₂ b) and
-- `totalSteps_one_pow_two` (its dyadic special case):
--
--     totalSteps 1 N + 2^{n+1} = (N + 1)·n + N + 2,   n = ⌊log₂ N⌋.

/-- **Exact `a = 1` total at every `N ≥ 1`.**  With `n = ⌊log₂ N⌋`,

      totalSteps 1 N + 2^{n+1} = (N+1)·n + N + 2,

    i.e. `totalSteps 1 N = (N+1)·⌊log₂N⌋ − 2^{⌊log₂N⌋+1} + N + 2`.  This is the
    exact average-case total for the `a = 1` row at *every* `N` (not merely the
    dyadic `N = 2^n` of `totalSteps_one_pow_two`), and it removes the abstract
    `∑ log₂ b` left standing in `totalSteps_one_eq`.  It is the fully elementary,
    closed-form counterpart of Brent's `≈ 0.7050 · log₂ N` average — the latter's
    transcendental leading constant stays out of reach (see file header).

    Proof: split `[1,N] = [1, 2^n] ⊍ (2^n, N]`.  The head is the dyadic total
    `totalSteps_one_pow_two`; on the partial tail every `b` satisfies
    `2^n ≤ b < 2^{n+1}`, so `⌊log₂ b⌋ = n` and `binaryGcdSteps 1 b = n+1`, giving
    the constant contribution `(N − 2^n)·(n+1)`.  A single `linear_combination`
    with the dyadic total closes the resulting polynomial identity in `N`, `n`,
    `2^n`. -/
theorem totalSteps_one_closed (N : ℕ) (hN : 1 ≤ N) :
    totalSteps 1 N + 2 ^ (Nat.log 2 N + 1) = (N + 1) * Nat.log 2 N + N + 2 := by
  set n := Nat.log 2 N with hn
  have hpow_le : 2 ^ n ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow : N < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hdisj : Disjoint (Finset.Icc 1 (2 ^ n)) (Finset.Ioc (2 ^ n) N) :=
    Finset.disjoint_left.mpr (fun x hx hx' => by
      rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega)
  have hunion : Finset.Icc 1 (2 ^ n) ∪ Finset.Ioc (2 ^ n) N = Finset.Icc 1 N := by
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  -- the partial tail (2^n, N] contributes the constant (N − 2^n)·(n+1)
  have htail : ∑ b ∈ Finset.Ioc (2 ^ n) N, binaryGcdSteps 1 b = (N - 2 ^ n) * (n + 1) := by
    have hval : ∀ b ∈ Finset.Ioc (2 ^ n) N, binaryGcdSteps 1 b = n + 1 := by
      intro b hb
      rw [Finset.mem_Ioc] at hb
      have hb1 : 1 ≤ b := le_trans Nat.one_le_two_pow (le_of_lt hb.1)
      have hlogb : Nat.log 2 b = n :=
        Nat.log_eq_of_pow_le_of_lt_pow (le_of_lt hb.1) (lt_of_le_of_lt hb.2 hlt_pow)
      rw [binaryGcdSteps_one_eq_log b hb1, hlogb]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Ioc, smul_eq_mul]
  -- split the total at the dyadic point 2^n
  have hsum : totalSteps 1 N
      = totalSteps 1 (2 ^ n) + ∑ b ∈ Finset.Ioc (2 ^ n) N, binaryGcdSteps 1 b := by
    unfold totalSteps
    rw [← Finset.sum_union hdisj, hunion]
  have hdya : totalSteps 1 (2 ^ n) + 2 ^ n = n * 2 ^ n + n + 2 := totalSteps_one_pow_two n
  rw [hsum, htail]
  zify [hpow_le] at hdya ⊢
  have hp : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [hp]
  linear_combination hdya

-- Concrete check of the closed form (a = 1, N = 100): n = ⌊log₂100⌋ = 6,
--   totalSteps 1 100 + 2^7 = 101·6 + 100 + 2 = 708.
example : totalSteps 1 100 + 2 ^ (Nat.log 2 100 + 1) = (100 + 1) * Nat.log 2 100 + 100 + 2 :=
  totalSteps_one_closed 100 (by norm_num)

-- ═══════════════════════════════════════════════════════════════════
-- PART VIII: THE EXACT a = 1 AVERAGE AT DYADIC ENDPOINTS  (leading constant = 1)
-- ═══════════════════════════════════════════════════════════════════
--
-- Dividing the exact dyadic total `totalSteps_one_pow_two` by `N = 2^n` gives the
-- a = 1 *average* in closed rational form:
--
--     avg(a=1, N=2^n) = (n − 1) + (n + 2)/2^n = log₂N − 1 + (log₂N + 2)/N.
--
-- As `n → ∞` the correction `(n+2)/2^n → 0`, so the a = 1 average is
-- `log₂N − 1 + o(1)`: its leading constant on `log₂N` is EXACTLY 1. This is the
-- fully-elementary analogue of Brent's transcendental `0.7050` average constant
-- (which is for the harder `max(a,b)` model and stays out of reach; see header).
-- Unlike the sandwich `avgSteps_one_ge ≤ avg ≤ avgSteps_le`, this pins the average
-- exactly on the dyadic subsequence.

/-- **Exact `a = 1` average at dyadic endpoints (`N = 2^n`).**  Dividing the exact
    total `totalSteps_one_pow_two` by `N = 2^n`,

      (totalSteps 1 (2^n)) / 2^n = (n − 1) + (n + 2) / 2^n.

    Since `(n + 2)/2^n → 0`, the `a = 1` average is `log₂N − 1 + o(1)`: the leading
    constant on `log₂N` is exactly `1`.  This is the elementary, fully-verified
    counterpart of Brent's `≈ 0.7050` average constant (for the harder `max(a,b)`
    model, out of reach here — see file header); here the exact leading constant is
    pinned to `1` on the `a = 1` row.  Proved from `totalSteps_one_pow_two` by a
    single `field_simp`/`ring` over `ℚ` (`2^n ≠ 0`). -/
theorem avgSteps_one_pow_two (n : ℕ) :
    (totalSteps 1 (2 ^ n) : ℚ) / (2 ^ n : ℚ)
      = ((n : ℚ) - 1) + ((n : ℚ) + 2) / (2 ^ n : ℚ) := by
  have hne : (2 : ℚ) ^ n ≠ 0 := by positivity
  have hkeyQ : (totalSteps 1 (2 ^ n) : ℚ)
      = (n : ℚ) * (2 : ℚ) ^ n + (n : ℚ) + 2 - (2 : ℚ) ^ n := by
    have hkey := totalSteps_one_pow_two n
    have hcast : (totalSteps 1 (2 ^ n) : ℚ) + (2 : ℚ) ^ n
        = (n : ℚ) * (2 : ℚ) ^ n + (n : ℚ) + 2 := by exact_mod_cast hkey
    linarith
  rw [hkeyQ]
  field_simp
  ring

-- Concrete check of the exact average (a = 1, N = 2^6 = 64): n = 6,
--   avg = (6 − 1) + (6 + 2)/64 = 5 + 1/8 = 41/8.
example : (totalSteps 1 (2 ^ 6) : ℚ) / (2 ^ 6 : ℚ) = ((6 : ℚ) - 1) + ((6 : ℚ) + 2) / (2 ^ 6 : ℚ) :=
  avgSteps_one_pow_two 6

-- ═══════════════════════════════════════════════════════════════════
-- PART IX: THE EXACT a = 1 AVERAGE AT EVERY N  +  A TIGHT log₂N − 1 FLOOR
-- ═══════════════════════════════════════════════════════════════════
--
-- `avgSteps_one_pow_two` pins the a = 1 average in closed rational form only on
-- the dyadic subsequence `N = 2^n`. Dividing the *every-N* exact total
-- `totalSteps_one_closed` by `N` extends this to a closed rational form at EVERY
-- `N ≥ 1` (with `n = ⌊log₂N⌋`):
--
--     avg(a=1, N) = (n + 1) + (n + 2 − 2^{n+1}) / N.
--
-- This subsumes `avgSteps_one_pow_two`: at `N = 2^n` the correction is
-- `(n + 2 − 2^{n+1})/2^n = (n + 2)/2^n − 2`, recovering `(n − 1) + (n + 2)/2^n`.
--
-- The closed form also sharpens the averaged lower bound: because
-- `2^{n+1} = 2·2^n ≤ 2N`, the correction obeys `(n + 2 − 2^{n+1})/N > −2`, so the
-- a = 1 average exceeds `log₂N − 1` at EVERY `N` — a factor-2 improvement over the
-- `(log₂N − 1)/2` floor of `avgSteps_one_ge`, and matching (to the additive `−1`)
-- the leading constant `1` established on the dyadic subsequence.

/-- **Exact `a = 1` average at every `N ≥ 1`.**  With `n = ⌊log₂ N⌋`,

      (totalSteps 1 N) / N = (n + 1) + (n + 2 − 2^{n+1}) / N.

    This extends `avgSteps_one_pow_two` (dyadic `N = 2^n` only) to an exact closed
    rational form for the `a = 1` average at *every* `N`, obtained by dividing the
    every-`N` total `totalSteps_one_closed` by `N`.  Proved by clearing the
    denominator `N ≠ 0` against the cast of `totalSteps_one_closed`. -/
theorem avgSteps_one_closed (N : ℕ) (hN : 1 ≤ N) :
    (totalSteps 1 N : ℚ) / (N : ℚ)
      = ((Nat.log 2 N : ℚ) + 1)
        + ((Nat.log 2 N : ℚ) + 2 - (2 : ℚ) ^ (Nat.log 2 N + 1)) / (N : ℚ) := by
  set n := Nat.log 2 N with hn
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hne : (N : ℚ) ≠ 0 := ne_of_gt hNQ
  -- cast the every-N total identity to ℚ and solve for totalSteps 1 N
  have hcast : (totalSteps 1 N : ℚ) + (2 : ℚ) ^ (n + 1)
      = ((N : ℚ) + 1) * (n : ℚ) + (N : ℚ) + 2 := by
    have := totalSteps_one_closed N hN
    rw [← hn] at this
    exact_mod_cast this
  have hT : (totalSteps 1 N : ℚ)
      = ((N : ℚ) + 1) * (n : ℚ) + (N : ℚ) + 2 - (2 : ℚ) ^ (n + 1) := by linarith
  rw [hT]
  field_simp
  ring

/-- **Tight `log₂N − 1` floor for the `a = 1` average (every `N`).**  For every
    `N ≥ 1`,

      log₂ N − 1  <  (totalSteps 1 N) / N.

    This strengthens `avgSteps_one_ge`'s `(log₂N − 1)/2` floor by a factor of two,
    and matches — up to the additive `−1` — the exact dyadic leading constant `1`
    of `avgSteps_one_pow_two`, now at *every* `N`.  Proof: from the exact average
    `avgSteps_one_closed`, the correction `(n + 2 − 2^{n+1})/N` exceeds `−2` because
    `2^{n+1} = 2·2^n ≤ 2N` (`Nat.pow_log_le_self`), so the average exceeds
    `(n + 1) − 2 = n − 1`. -/
theorem avgSteps_one_gt (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℚ) - 1 < (totalSteps 1 N : ℚ) / (N : ℚ) := by
  set n := Nat.log 2 N with hn
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  -- 2^{n+1} = 2·2^n ≤ 2·N  (since 2^n ≤ N)
  have hpow_le : (2 : ℕ) ^ n ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hpowQ : (2 : ℚ) ^ (n + 1) ≤ 2 * (N : ℚ) := by
    have h : ((2 ^ n : ℕ) : ℚ) ≤ (N : ℚ) := by exact_mod_cast hpow_le
    push_cast at h
    calc (2 : ℚ) ^ (n + 1) = 2 * (2 : ℚ) ^ n := by rw [pow_succ]; ring
      _ ≤ 2 * (N : ℚ) := by linarith
  -- cast of the exact every-N total (relates totalSteps 1 N to 2^{n+1})
  have hcast : (totalSteps 1 N : ℚ) + (2 : ℚ) ^ (n + 1)
      = ((N : ℚ) + 1) * (n : ℚ) + (N : ℚ) + 2 := by
    have h := totalSteps_one_closed N hN
    rw [← hn] at h
    exact_mod_cast h
  -- clear the denominator: goal becomes  (n − 1)·N < totalSteps 1 N
  rw [lt_div_iff₀ hNQ]
  -- (n−1)·N < (N+1)·n + N + 2 − 2^{n+1}  ⟸  2^{n+1} ≤ 2N and n ≥ 0
  nlinarith [hcast, hpowQ, hn0]

-- Concrete check of the exact every-N average (a = 1, N = 100): n = 6,
--   avg = (6 + 1) + (6 + 2 − 2^7)/100 = 7 − 120/100 = 7 − 6/5 = 29/5.
example : (totalSteps 1 100 : ℚ) / (100 : ℚ)
    = ((Nat.log 2 100 : ℚ) + 1)
      + ((Nat.log 2 100 : ℚ) + 2 - (2 : ℚ) ^ (Nat.log 2 100 + 1)) / (100 : ℚ) :=
  avgSteps_one_closed 100 (by norm_num)

-- ═══════════════════════════════════════════════════════════════════
-- PART X: THE MATCHING TIGHT log₂N + 1 CEILING  (a = 1 row)  ⇒  SANDWICH
-- ═══════════════════════════════════════════════════════════════════
--
-- PART IX pinned the a = 1 average's *floor* at every N to `log₂N − 1`
-- (`avgSteps_one_gt`), a factor-2 sharpening of `avgSteps_one_ge`'s
-- `(log₂N − 1)/2`. The only ceiling at every N so far is the loose
-- `avgSteps_le`, which at a = 1 reads `≤ 2·log₂N + 2` — leading constant 2.
-- The symmetric, matching *tight* ceiling has leading constant 1:
--
--     (totalSteps 1 N) / N ≤ log₂N + 1     at every N ≥ 1.
--
-- It is immediate from the exact per-b value: every summand
-- `binaryGcdSteps 1 b = log₂ b + 1 ≤ log₂ N + 1` (as `b ≤ N ⟹ log₂ b ≤ log₂ N`),
-- so the total is `≤ N·(log₂N + 1)`. Combined with `avgSteps_one_gt` this
-- sandwiches the a = 1 average in an additive band of width 2 about `log₂N` at
-- EVERY N — pinning its leading `log₂N` constant to exactly 1 without needing the
-- dyadic restriction of `avgSteps_one_pow_two`.

/-- **Total upper bound (a = 1 row), tight leading constant.** For every `N`,
    `totalSteps 1 N ≤ N · (log₂ N + 1)`. Each summand equals `log₂ b + 1`
    (`binaryGcdSteps_one_eq_log`) and `log₂ b ≤ log₂ N` since `b ≤ N`, so the
    `N`-element sum is bounded by `N·(log₂N + 1)`. This is the exact-value
    counterpart of the worst-case `totalSteps_le`, halving its leading constant on
    the `a = 1` row. -/
theorem totalSteps_one_le_nat (N : ℕ) : totalSteps 1 N ≤ N * (Nat.log 2 N + 1) := by
  unfold totalSteps
  calc ∑ b ∈ Finset.Icc 1 N, binaryGcdSteps 1 b
      ≤ ∑ _b ∈ Finset.Icc 1 N, (Nat.log 2 N + 1) := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.mem_Icc] at hb
        rw [binaryGcdSteps_one_eq_log b hb.1]
        have hbN : Nat.log 2 b ≤ Nat.log 2 N := Nat.log_mono_right hb.2
        omega
    _ = N * (Nat.log 2 N + 1) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp

/-- **Tight `log₂N + 1` ceiling for the `a = 1` average (every `N`).** For every
    `N ≥ 1`,

      (totalSteps 1 N) / N ≤ log₂ N + 1.

    This is the matching upper bound to `avgSteps_one_gt`'s `log₂N − 1` floor:
    it has leading constant `1` on `log₂N` (versus the loose `2` of `avgSteps_le`),
    obtained directly from `totalSteps_one_le_nat`. -/
theorem avgSteps_one_le (N : ℕ) (hN : 1 ≤ N) :
    (totalSteps 1 N : ℚ) / (N : ℚ) ≤ (Nat.log 2 N : ℚ) + 1 := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  rw [div_le_iff₀ hNQ]
  have h : (totalSteps 1 N : ℚ) ≤ ((N * (Nat.log 2 N + 1) : ℕ) : ℚ) := by
    exact_mod_cast totalSteps_one_le_nat N
  calc (totalSteps 1 N : ℚ)
      ≤ ((N * (Nat.log 2 N + 1) : ℕ) : ℚ) := h
    _ = ((Nat.log 2 N : ℚ) + 1) * (N : ℚ) := by push_cast; ring

/-- **Two-sided `Θ(log N)` sandwich for the `a = 1` average (every `N`).** For
    every `N ≥ 1`,

      log₂ N − 1  <  (totalSteps 1 N) / N  ≤  log₂ N + 1.

    The average step count on the `a = 1` row sits in an additive band of width `2`
    about `log₂ N` at *every* `N` (not merely the dyadic subsequence of
    `avgSteps_one_pow_two`), so its leading constant on `log₂N` is pinned to exactly
    `1`. This is the elementary, fully-verified analogue of Brent's average-case
    order; the sharp `0.7050` constant (for the harder `max(a,b)` model) remains out
    of reach (see file header). Combines `avgSteps_one_gt` and `avgSteps_one_le`. -/
theorem avgSteps_one_sandwich (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℚ) - 1 < (totalSteps 1 N : ℚ) / (N : ℚ) ∧
    (totalSteps 1 N : ℚ) / (N : ℚ) ≤ (Nat.log 2 N : ℚ) + 1 :=
  ⟨avgSteps_one_gt N hN, avgSteps_one_le N hN⟩

-- Concrete check of the sandwich (a = 1, N = 100): n = 6, avg = 29/5 = 5.8,
--   and log₂100 − 1 = 5 < 5.8 ≤ 7 = log₂100 + 1.
example : (Nat.log 2 100 : ℚ) - 1 < (totalSteps 1 100 : ℚ) / (100 : ℚ) ∧
    (totalSteps 1 100 : ℚ) / (100 : ℚ) ≤ (Nat.log 2 100 : ℚ) + 1 :=
  avgSteps_one_sandwich 100 (by norm_num)

-- ═══════════════════════════════════════════════════════════════════
-- PART XI: THE CEILING IS STRICT  ⇒  TWO-SIDED STRICT SANDWICH  (a = 1 row)
-- ═══════════════════════════════════════════════════════════════════
--
-- `avgSteps_one_sandwich` bounds the a = 1 average by `log₂N − 1 < avg ≤ log₂N + 1`,
-- with a NON-strict ceiling. The ceiling is in fact strict for every `N ≥ 2`: the
-- summand at `b = 1` is `binaryGcdSteps 1 1 = log₂1 + 1 = 1`, strictly below the
-- per-term ceiling `log₂N + 1 ≥ 2` (as `log₂N ≥ 1` once `N ≥ 2`). A single strict
-- summand makes the whole sum strict (`Finset.sum_lt_sum`), so
--     totalSteps 1 N < N·(log₂N + 1),
-- and dividing by `N` gives `avg < log₂N + 1`. Together with the floor
-- `avgSteps_one_gt` this upgrades the headline `avgSteps_one_sandwich` to a genuine
-- TWO-SIDED STRICT band `log₂N − 1 < avg < log₂N + 1` at every `N ≥ 2`.

/-- **Strict total upper bound (a = 1 row).** For every `N ≥ 2`,
    `totalSteps 1 N < N · (log₂ N + 1)`. The `b = 1` summand is
    `binaryGcdSteps 1 1 = 1`, strictly below the per-term ceiling `log₂N + 1 ≥ 2`,
    so the sum is strict (`Finset.sum_lt_sum`). This is the strict sharpening of
    `totalSteps_one_le_nat`. -/
theorem totalSteps_one_lt_nat (N : ℕ) (hN : 2 ≤ N) :
    totalSteps 1 N < N * (Nat.log 2 N + 1) := by
  have hlogN : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN
  unfold totalSteps
  calc ∑ b ∈ Finset.Icc 1 N, binaryGcdSteps 1 b
      < ∑ _b ∈ Finset.Icc 1 N, (Nat.log 2 N + 1) := by
        apply Finset.sum_lt_sum
        · intro b hb
          rw [Finset.mem_Icc] at hb
          rw [binaryGcdSteps_one_eq_log b hb.1]
          have hbN : Nat.log 2 b ≤ Nat.log 2 N := Nat.log_mono_right hb.2
          omega
        · refine ⟨1, by rw [Finset.mem_Icc]; omega, ?_⟩
          rw [binaryGcdSteps_one_eq_log 1 le_rfl, Nat.log_one_right]
          omega
    _ = N * (Nat.log 2 N + 1) := by
        rw [Finset.sum_const, Nat.card_Icc]; simp

/-- **Strict `log₂N + 1` ceiling for the `a = 1` average (every `N ≥ 2`).**
    `(totalSteps 1 N) / N < log₂ N + 1`. The strict counterpart of `avgSteps_one_le`,
    obtained from `totalSteps_one_lt_nat` by clearing the denominator `N > 0`. -/
theorem avgSteps_one_lt (N : ℕ) (hN : 2 ≤ N) :
    (totalSteps 1 N : ℚ) / (N : ℚ) < (Nat.log 2 N : ℚ) + 1 := by
  have hNpos : 0 < N := by omega
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  rw [div_lt_iff₀ hNQ]
  have h : (totalSteps 1 N : ℚ) < ((N * (Nat.log 2 N + 1) : ℕ) : ℚ) := by
    exact_mod_cast totalSteps_one_lt_nat N hN
  calc (totalSteps 1 N : ℚ)
      < ((N * (Nat.log 2 N + 1) : ℕ) : ℚ) := h
    _ = ((Nat.log 2 N : ℚ) + 1) * (N : ℚ) := by push_cast; ring

/-- **Two-sided STRICT `Θ(log N)` sandwich for the `a = 1` average (every `N ≥ 2`).**

      log₂ N − 1  <  (totalSteps 1 N) / N  <  log₂ N + 1.

    Upgrades `avgSteps_one_sandwich` (whose ceiling is non-strict) to a genuinely
    strict two-sided band: the `a = 1` average lies *strictly inside* the width-2
    window about `log₂ N` at every `N ≥ 2`. Combines `avgSteps_one_gt` (floor) with
    `avgSteps_one_lt` (strict ceiling). -/
theorem avgSteps_one_sandwich_strict (N : ℕ) (hN : 2 ≤ N) :
    (Nat.log 2 N : ℚ) - 1 < (totalSteps 1 N : ℚ) / (N : ℚ) ∧
    (totalSteps 1 N : ℚ) / (N : ℚ) < (Nat.log 2 N : ℚ) + 1 :=
  ⟨avgSteps_one_gt N (by omega), avgSteps_one_lt N hN⟩

-- Concrete check of the strict sandwich (a = 1, N = 100): avg = 29/5 = 5.8,
--   and log₂100 − 1 = 5 < 5.8 < 7 = log₂100 + 1.
example : (Nat.log 2 100 : ℚ) - 1 < (totalSteps 1 100 : ℚ) / (100 : ℚ) ∧
    (totalSteps 1 100 : ℚ) / (100 : ℚ) < (Nat.log 2 100 : ℚ) + 1 :=
  avgSteps_one_sandwich_strict 100 (by norm_num)

-- ═══════════════════════════════════════════════════════════════════
-- PART XII: MONOTONICITY STRUCTURE OF THE a = 1 TOTAL
-- ═══════════════════════════════════════════════════════════════════
--
-- The exact-log form `binaryGcdSteps_one_eq_log` gives the a = 1 row a clean
-- one-term recurrence in `N`: passing from `N` to `N + 1` appends the single
-- summand `binaryGcdSteps 1 (N+1) = log₂(N+1) + 1`. Since that increment is
-- always `≥ 1 > 0`, the running total `N ↦ totalSteps 1 N` is *strictly*
-- increasing — a structural fact none of the earlier size bounds record. This
-- pins down the qualitative shape of the total-work curve underlying the
-- `Θ(N·log N)` estimates above.

/-- **Per-step recurrence for the `a = 1` total.** Extending the range from
    `[1, N]` to `[1, N+1]` appends exactly the summand
    `binaryGcdSteps 1 (N+1) = log₂(N+1) + 1`:

      totalSteps 1 (N+1) = totalSteps 1 N + (log₂(N+1) + 1).

    Immediate from `Finset.sum_Icc_succ_top` together with the exact step count
    `binaryGcdSteps_one_eq_log`. This is the discrete recurrence that drives the
    monotonicity results below. -/
theorem totalSteps_one_succ (N : ℕ) :
    totalSteps 1 (N + 1) = totalSteps 1 N + (Nat.log 2 (N + 1) + 1) := by
  unfold totalSteps
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      binaryGcdSteps_one_eq_log (N + 1) (by omega)]

/-- **The `a = 1` total is strictly increasing in `N`.** Each new argument
    `N + 1` contributes `log₂(N+1) + 1 ≥ 1 > 0` extra steps, so
    `totalSteps 1 N < totalSteps 1 (N+1)` for every `N`. Consequently `N ↦
    totalSteps 1 N` is `StrictMono` — the running work count never plateaus. -/
theorem totalSteps_one_strictMono : StrictMono (totalSteps 1) := by
  apply strictMono_nat_of_lt_succ
  intro N
  rw [totalSteps_one_succ]
  omega

/-- **The `a = 1` total is monotone in `N`.** The `Monotone` weakening of
    `totalSteps_one_strictMono`: `M ≤ N ⟹ totalSteps 1 M ≤ totalSteps 1 N`. -/
theorem totalSteps_one_mono : Monotone (totalSteps 1) :=
  totalSteps_one_strictMono.monotone

-- Concrete check of the per-step recurrence (a = 1, N = 7):
--   totalSteps 1 8 = totalSteps 1 7 + (log₂ 8 + 1) = totalSteps 1 7 + 4.
example : totalSteps 1 8 = totalSteps 1 7 + (Nat.log 2 8 + 1) :=
  totalSteps_one_succ 7

-- ═══════════════════════════════════════════════════════════════════
-- PART XIV: THE AVERAGE IS UNBOUNDED  (a = 1 row)
-- ═══════════════════════════════════════════════════════════════════
--
-- The strict sandwich `avgSteps_one_sandwich_strict` places the a = 1 average in the
-- width-2 window `log₂N − 1 < avg < log₂N + 1`. Its lower edge `log₂N − 1` is itself
-- unbounded, so the average grows without bound: binary GCD is NOT `O(1)` on average.
-- We record this as an explicit ∃-statement (the honest form, since the average is not
-- monotone in `N`, so a `Tendsto _ atTop atTop` would need the sandwich rather than
-- monotonicity anyway): every target `M` is exceeded, witnessed on the dyadic
-- subsequence `N = 2ⁿ` where the floor `log₂(2ⁿ) − 1 = n − 1` is driven past `M` by the
-- Archimedean property.

/-- **The `a = 1` average step count is unbounded.**  For every target `M : ℚ` there is an
    argument `N ≥ 1` whose average `a = 1` step count `(totalSteps 1 N) / N` exceeds `M`.
    Equivalently the binary Euclidean algorithm is *not* `O(1)` on average — its cost grows
    without bound.  Witnessed on the dyadic subsequence `N = 2 ^ n`: there
    `avgSteps_one_gt` gives `avg > log₂(2ⁿ) − 1 = n − 1` (using `Nat.log_pow`), and choosing
    `n > M + 1` by the Archimedean property of `ℚ` (`exists_nat_gt`) forces `avg > M`.  This
    is the elementary, fully-verified lower shadow of the `Θ(log N)` growth captured by
    `avgSteps_one_sandwich_strict`. -/
theorem avgSteps_one_unbounded (M : ℚ) :
    ∃ N : ℕ, 1 ≤ N ∧ M < (totalSteps 1 N : ℚ) / (N : ℚ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  have hNpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  refine ⟨2 ^ n, hNpos, ?_⟩
  have hlog : Nat.log 2 (2 ^ n) = n := Nat.log_pow (by norm_num) n
  have hgt := avgSteps_one_gt (2 ^ n) hNpos
  rw [hlog] at hgt
  have hMn : M < (n : ℚ) - 1 := by linarith
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: GENERAL-`a` STRUCTURE OF THE RUNNING TOTAL
-- ═══════════════════════════════════════════════════════════════════

/-- **Per-argument recurrence of the running total (general `a`).** Extending the
    range by one argument adds exactly that argument's step count:
    `totalSteps a (N+1) = totalSteps a N + binaryGcdSteps a (N+1)`. This is the
    general-`a` companion of `totalSteps_one_succ` (which specialises the last
    term to `log₂(N+1) + 1` via `binaryGcdSteps_one_eq_log`). Immediate from
    `Finset.sum_Icc_succ_top`. -/
theorem totalSteps_succ (a N : ℕ) :
    totalSteps a (N + 1) = totalSteps a N + binaryGcdSteps a (N + 1) := by
  unfold totalSteps
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- **The running total is monotone in `N` (general `a`).** For every fixed left
    argument `a`, `N ↦ totalSteps a N` is `Monotone`: each new argument contributes
    a nonnegative step count, so the running work count never decreases. This is the
    general-`a` companion of `totalSteps_one_mono` (the `a = 1` total is in fact
    *strictly* monotone since its increment `log₂(N+1)+1 ≥ 1` is positive; for
    general `a` a single argument may cost `0` steps, e.g. `binaryGcdSteps a a`, so
    only monotonicity holds unconditionally). -/
theorem totalSteps_mono (a : ℕ) : Monotone (totalSteps a) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [totalSteps_succ]
  omega

/-- **Range-monotonicity in `≤` form (general `a`).** The citable inequality form of
    `totalSteps_mono`: `M ≤ N ⟹ totalSteps a M ≤ totalSteps a N`. -/
theorem totalSteps_le_of_le {a M N : ℕ} (h : M ≤ N) : totalSteps a M ≤ totalSteps a N :=
  totalSteps_mono a h

end BinaryGcdOQ01OQ04OQ03
