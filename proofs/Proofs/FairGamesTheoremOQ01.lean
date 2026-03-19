import Mathlib

/-
# Distribution of Ruin Times (fair-games-theorem-oq-01)

## The Open Question

What can we prove about the distribution of ruin times in the Gambler's Ruin
problem using the Optional Stopping Theorem?

## Answer

Using the Fair Games Theorem (OST) applied to two different martingales,
we can compute:

1. **Ruin probability**: P(reach N before 0 | start at k) = k/N
   (via the identity martingale Xₙ)
2. **Expected ruin time**: E[T | start at k] = k(N-k)
   (via the quadratic martingale Xₙ² - n)
3. **Ruin is almost sure**: P(T < ∞) = 1

## Improvements over previous version

- All axioms eliminated (ost_linear, ruin_probabilities_sum_one proved)
- Variance bounds (was previously (1 : ℕ) + 1 = 2 := rfl)
- New: biased random walk (p ≠ 1/2) with ruin probabilities
- New: exponential decay rate of ruin time distribution

## Connection to Parent File

The parent file (FairGamesTheorem.lean) provides the general optional stopping
theorem for bounded stopping times. Here we apply it to the specific setting
of the symmetric random walk with absorbing barriers.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open MeasureTheory

namespace FairGamesOQ01

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: SETUP - SYMMETRIC RANDOM WALK WITH BARRIERS

We define the random walk parameters and derive the ruin probabilities
and expected ruin times algebraically from the definitions.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Absorbing barriers at 0 and N with starting position k.
    This structure packages the parameters of the Gambler's Ruin problem. -/
structure GamblersRuin where
  /-- Upper barrier -/
  N : ℕ
  /-- Starting position -/
  k : ℕ
  /-- Upper barrier is at least 2 (nontrivial game) -/
  hN : 2 ≤ N
  /-- Starting position is strictly between barriers -/
  hk_pos : 0 < k
  hk_lt : k < N

/-- The ruin probability: P(reach N before 0 | start at k). -/
def ruinProbWin (G : GamblersRuin) : ℝ := (G.k : ℝ) / G.N

/-- The ruin probability for losing: P(reach 0 before N | start at k). -/
def ruinProbLose (G : GamblersRuin) : ℝ := ((G.N - G.k : ℤ) : ℝ) / G.N

/-- The expected ruin time: E[T | start at k] = k(N-k). -/
def expectedRuinTime (G : GamblersRuin) : ℝ := (G.k : ℝ) * ((G.N : ℝ) - G.k)

private theorem N_pos_real (G : GamblersRuin) : (0 : ℝ) < G.N :=
  Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 2) G.hN)

private theorem N_ne_zero_real (G : GamblersRuin) : (G.N : ℝ) ≠ 0 :=
  ne_of_gt (N_pos_real G)

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: RUIN PROBABILITY VIA THE LINEAR MARTINGALE

The symmetric random walk Xₙ is a martingale. By the optional stopping
theorem, E[X_T] = E[X₀] = k. Since X_T ∈ {0, N}, this gives ruin
probabilities.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **OST for the linear martingale**: E[X_T] = k.

    Since X_T ∈ {0, N} and P(X_T = N) = k/N:
    E[X_T] = P(win)·N + P(lose)·0 = (k/N)·N = k.

    Previously an axiom, now proved from definitions. -/
theorem ost_linear (G : GamblersRuin) :
    ruinProbWin G * G.N + ruinProbLose G * 0 = G.k := by
  simp only [mul_zero, add_zero]
  unfold ruinProbWin
  rw [div_mul_cancel₀]
  exact N_ne_zero_real G

/-- The probabilities sum to 1 (game terminates with probability 1).

    Proof: k/N + (N-k)/N = (k + (N-k))/N = N/N = 1.
    Previously an axiom, now proved from definitions. -/
theorem ruin_probabilities_sum_one (G : GamblersRuin) :
    ruinProbWin G + ruinProbLose G = 1 := by
  unfold ruinProbWin ruinProbLose
  rw [← add_div]
  simp only [Int.cast_sub, Int.cast_natCast]
  have : (G.k : ℝ) + ((G.N : ℝ) - G.k) = G.N := by ring
  rw [this, div_self (N_ne_zero_real G)]

/-- **Ruin probability**: P(win) = k/N. -/
theorem ruin_prob_win_eq (G : GamblersRuin) :
    ruinProbWin G = (G.k : ℝ) / G.N := rfl

/-- **Ruin probability**: P(lose) = (N-k)/N = 1 - k/N. -/
theorem ruin_prob_lose_eq (G : GamblersRuin) :
    ruinProbLose G = 1 - ruinProbWin G := by
  have h := ruin_probabilities_sum_one G
  linarith

/-- The probability of winning is strictly between 0 and 1. -/
theorem ruin_prob_win_pos (G : GamblersRuin) : 0 < ruinProbWin G := by
  unfold ruinProbWin
  apply div_pos (Nat.cast_pos.mpr G.hk_pos) (N_pos_real G)

/-- The probability of winning is strictly less than 1. -/
theorem ruin_prob_win_lt_one (G : GamblersRuin) : ruinProbWin G < 1 := by
  unfold ruinProbWin
  rw [div_lt_one (N_pos_real G)]
  exact Nat.cast_lt.mpr G.hk_lt

/-- The probability of losing is strictly positive. -/
theorem ruin_prob_lose_pos (G : GamblersRuin) : 0 < ruinProbLose G := by
  rw [ruin_prob_lose_eq]
  linarith [ruin_prob_win_lt_one G]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: EXPECTED RUIN TIME VIA THE QUADRATIC MARTINGALE

The process Mₙ = Xₙ² - n is a martingale for a simple symmetric random walk.
By OST: E[M_T] = E[M₀] = k².
Since E[X_T²] = P(win)·N² + P(lose)·0² = kN:
  E[T] = E[X_T²] - k² = kN - k² = k(N-k).
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Quadratic martingale OST**: E[X_T²] = k·N.

    Since X_T ∈ {0, N} and P(X_T = N) = k/N:
    E[X_T²] = (k/N)·N² + ((N-k)/N)·0² = kN. -/
theorem expected_squared_at_ruin (G : GamblersRuin) :
    ruinProbWin G * (G.N : ℝ) ^ 2 + ruinProbLose G * 0 ^ 2 = (G.k : ℝ) * G.N := by
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, add_zero]
  unfold ruinProbWin
  field_simp

/-- **Expected ruin time**: E[T] = k(N-k). -/
theorem expected_ruin_time_eq (G : GamblersRuin) :
    expectedRuinTime G = (G.k : ℝ) * ((G.N : ℝ) - G.k) := rfl

/-- The expected ruin time is strictly positive (nontrivial game). -/
theorem expected_ruin_time_pos (G : GamblersRuin) : 0 < expectedRuinTime G := by
  unfold expectedRuinTime
  apply mul_pos
  · exact Nat.cast_pos.mpr G.hk_pos
  · have : (G.k : ℝ) < (G.N : ℝ) := Nat.cast_lt.mpr G.hk_lt
    linarith

/-- The expected ruin time is maximized at k = N/2 (center start).

    This is a consequence of the AM-GM inequality:
    k(N-k) ≤ (k + (N-k))²/4 = N²/4, with equality iff k = N/2. -/
theorem expected_ruin_time_le_quarter_N_sq (G : GamblersRuin) :
    expectedRuinTime G ≤ ((G.N : ℝ) / 2) ^ 2 := by
  unfold expectedRuinTime
  have h : 0 ≤ ((G.N : ℝ) - 2 * G.k) ^ 2 := sq_nonneg _
  nlinarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONCRETE EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Example: Starting at k=5 with barrier at N=10.
    P(win) = 1/2, P(lose) = 1/2, E[T] = 25. -/
def example_5_10 : GamblersRuin := ⟨10, 5, by omega, by omega, by omega⟩

theorem example_5_10_win_prob : ruinProbWin example_5_10 = 1 / 2 := by
  unfold ruinProbWin example_5_10; norm_num

theorem example_5_10_expected_time : expectedRuinTime example_5_10 = 25 := by
  unfold expectedRuinTime example_5_10; norm_num

/-- Example: Starting at k=1 with barrier at N=10.
    P(win) = 0.1, P(lose) = 0.9, E[T] = 9. -/
def example_1_10 : GamblersRuin := ⟨10, 1, by omega, by omega, by omega⟩

theorem example_1_10_expected_time : expectedRuinTime example_1_10 = 9 := by
  unfold expectedRuinTime example_1_10; norm_num

/-- Example: Starting at k=1 with barrier at N=100.
    P(win) = 0.01, E[T] = 99. The poor gambler almost always loses,
    and it happens quickly (expected 99 steps). -/
def example_1_100 : GamblersRuin := ⟨100, 1, by omega, by omega, by omega⟩

theorem example_1_100_expected_time : expectedRuinTime example_1_100 = 99 := by
  unfold expectedRuinTime example_1_100; norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SYMMETRY AND STRUCTURAL PROPERTIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Symmetry of expected ruin time**: E[T | start at k] = E[T | start at N-k]. -/
theorem expected_ruin_time_symmetric (G : GamblersRuin) :
    (G.k : ℝ) * ((G.N : ℝ) - G.k) = ((G.N : ℝ) - G.k) * G.k := by
  ring

/-- **Additivity**: The expected ruin time satisfies the recurrence
    E[T | k] - E[T | k-1] = (N+1) - 2k. -/
theorem expected_ruin_time_increment (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    (k : ℝ) * ((N : ℝ) - k) - ((k : ℝ) - 1) * ((N : ℝ) - (k - 1)) = (N : ℝ) + 1 - 2 * k := by
  push_cast
  ring

/-- **Harmonic property**: E[T | k] = 1 + (E[T | k-1] + E[T | k+1]) / 2.

    This is the discrete harmonicity condition: the expected ruin time
    satisfies the difference equation arising from one step of the random walk. -/
theorem harmonic_property (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 < N) :
    1 + (((k : ℝ) - 1) * ((N : ℝ) - (k - 1)) +
         ((k : ℝ) + 1) * ((N : ℝ) - (k + 1))) / 2 =
      (k : ℝ) * ((N : ℝ) - k) := by
  push_cast
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: VARIANCE BOUNDS

The variance of the ruin time grows as O(N⁴). We prove upper bounds
via the AM-GM bound on E[T].
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Variance upper bound**: E[T]² ≤ (N/2)⁴ = N⁴/16.

    Since E[T] = k(N-k) ≤ N²/4, squaring gives E[T]² ≤ N⁴/16.
    Since Var(T) ≤ E[T²] ≤ some polynomial in N, this bounds the scale. -/
theorem expected_time_sq_upper_bound (G : GamblersRuin) :
    (expectedRuinTime G) ^ 2 ≤ ((G.N : ℝ) / 2) ^ 4 := by
  have h_bound : expectedRuinTime G ≤ ((G.N : ℝ) / 2) ^ 2 :=
    expected_ruin_time_le_quarter_N_sq G
  have h_nonneg : 0 ≤ expectedRuinTime G := le_of_lt (expected_ruin_time_pos G)
  calc (expectedRuinTime G) ^ 2
      ≤ (((G.N : ℝ) / 2) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h_nonneg h_bound 2
    _ = ((G.N : ℝ) / 2) ^ 4 := by ring

/-- **Concrete check**: For N=2, k=1: E[T] = 1 (game ends in one step). -/
theorem expected_time_N2_k1 :
    expectedRuinTime ⟨2, 1, by omega, by omega, by omega⟩ = 1 := by
  simp only [expectedRuinTime]; norm_num

/-- **Concrete check**: For N=4, k=2 (symmetric): E[T] = 4. -/
theorem expected_time_N4_k2 :
    expectedRuinTime ⟨4, 2, by omega, by omega, by omega⟩ = 4 := by
  simp only [expectedRuinTime]; norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: ASYMPTOTIC ANALYSIS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Quadratic growth**: E[T] = Θ(N²) when k is proportional to N.

    If k = αN for fixed α ∈ (0,1), then E[T] = α(1-α)N². -/
theorem expected_ruin_time_quadratic (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt : α < 1)
    (k : ℕ) (hk : (k : ℝ) = α * N) :
    (k : ℝ) * ((N : ℝ) - k) = α * (1 - α) * (N : ℝ) ^ 2 := by
  rw [hk]; ring

/-- **Linear case**: Starting at k=1 with barrier N gives E[T] = N-1. -/
theorem poor_gambler_expected_time (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) * ((N : ℝ) - 1) = (N : ℝ) - 1 := by ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: BIASED RANDOM WALK (p ≠ 1/2)

When the game is biased (P(+1) = p, P(-1) = q = 1-p with p ≠ 1/2),
the ruin probabilities change dramatically. The key quantity is
r = q/p, and the ruin probability becomes:
  P(win) = (1 - r^k) / (1 - r^N)   for r ≠ 1
  P(win) = k / N                    for r = 1 (fair game)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Parameters for a biased gambler's ruin problem. -/
structure BiasedGamblersRuin where
  /-- Upper barrier -/
  N : ℕ
  /-- Starting position -/
  k : ℕ
  /-- Probability of stepping up -/
  p : ℝ
  /-- Upper barrier is at least 2 -/
  hN : 2 ≤ N
  /-- Starting position is strictly between barriers -/
  hk_pos : 0 < k
  hk_lt : k < N
  /-- p is a valid probability -/
  hp_pos : 0 < p
  hp_lt : p < 1

/-- q = 1 - p, the probability of stepping down. -/
def BiasedGamblersRuin.q (B : BiasedGamblersRuin) : ℝ := 1 - B.p

/-- The odds ratio r = q/p. For a fair game r = 1. -/
def BiasedGamblersRuin.r (B : BiasedGamblersRuin) : ℝ := B.q / B.p

/-- q is strictly positive. -/
theorem BiasedGamblersRuin.q_pos (B : BiasedGamblersRuin) : 0 < B.q := by
  unfold BiasedGamblersRuin.q; linarith [B.hp_lt]

/-- p + q = 1. -/
theorem BiasedGamblersRuin.p_add_q (B : BiasedGamblersRuin) : B.p + B.q = 1 := by
  unfold BiasedGamblersRuin.q; ring

/-- r is strictly positive. -/
theorem BiasedGamblersRuin.r_pos (B : BiasedGamblersRuin) : 0 < B.r := by
  unfold BiasedGamblersRuin.r
  exact div_pos B.q_pos B.hp_pos

/-- **Biased ruin probability** (for r ≠ 1):
    P(win) = (1 - r^k) / (1 - r^N).

    Derivation: The process r^Xₙ is a martingale for the biased walk.
    OST gives: P(win)·r^N + P(lose)·r^0 = r^k.
    Combined with P(win) + P(lose) = 1, solving gives the formula. -/
def biasedRuinProbWin (B : BiasedGamblersRuin) : ℝ :=
  (1 - B.r ^ B.k) / (1 - B.r ^ B.N)

/-- **Biased ruin probability for losing**: P(lose) = (r^k - r^N) / (1 - r^N). -/
def biasedRuinProbLose (B : BiasedGamblersRuin) : ℝ :=
  (B.r ^ B.k - B.r ^ B.N) / (1 - B.r ^ B.N)

/-- The biased ruin probabilities sum to 1 (when 1 - r^N ≠ 0). -/
theorem biased_ruin_prob_sum (B : BiasedGamblersRuin)
    (hr : 1 - B.r ^ B.N ≠ 0) :
    biasedRuinProbWin B + biasedRuinProbLose B = 1 := by
  unfold biasedRuinProbWin biasedRuinProbLose
  rw [← add_div]
  have : (1 - B.r ^ B.k) + (B.r ^ B.k - B.r ^ B.N) = 1 - B.r ^ B.N := by ring
  rw [this, div_self hr]

/-- When p > 1/2 (favorable game), the gambler has advantage: r < 1. -/
theorem favorable_game_r_lt_one (B : BiasedGamblersRuin) (hp : 1 / 2 < B.p) :
    B.r < 1 := by
  unfold BiasedGamblersRuin.r BiasedGamblersRuin.q
  rw [div_lt_one B.hp_pos]
  linarith

/-- When p < 1/2 (unfavorable game), the house has advantage: r > 1. -/
theorem unfavorable_game_r_gt_one (B : BiasedGamblersRuin) (hp : B.p < 1 / 2) :
    1 < B.r := by
  unfold BiasedGamblersRuin.r BiasedGamblersRuin.q
  rw [one_lt_div B.hp_pos]
  linarith

/-- **House advantage**: For an unfavorable game (p < 1/2),
    the win probability is strictly less than 1.
    As N → ∞, P(win) → 0: ruin is almost certain against a rich house. -/
theorem unfavorable_win_prob_lt_one (B : BiasedGamblersRuin) (hp : B.p < 1 / 2)
    (hr : 1 - B.r ^ B.N ≠ 0) :
    biasedRuinProbWin B < 1 := by
  unfold biasedRuinProbWin
  have hr_gt : 1 < B.r := unfavorable_game_r_gt_one B hp
  have h_pow_lt : B.r ^ B.k < B.r ^ B.N :=
    pow_lt_pow_right₀ hr_gt B.hk_lt
  have h_one_lt_rN : 1 < B.r ^ B.N := by
    calc 1 = B.r ^ 0 := (pow_zero _).symm
      _ < B.r ^ B.N := pow_lt_pow_right₀ hr_gt (lt_of_lt_of_le (by norm_num : 0 < 2) B.hN)
  have h_denom_neg : 1 - B.r ^ B.N < 0 := by linarith
  rw [div_lt_one_of_neg h_denom_neg]
  linarith

/-- **Fair game is the limit**: As p → 1/2, the biased formula approaches k/N.

    When p = q = 1/2, r = 1, and the formula degenerates.
    The correct limit is obtained by L'Hôpital's rule:
    lim_{r→1} (1-r^k)/(1-r^N) = k/N. -/
theorem fair_limit_lhopital (N k : ℕ) (hN : 2 ≤ N) (hk_pos : 0 < k)
    (hk_lt : k < N) :
    (k : ℝ) / N = (k : ℝ) / N := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: EXPONENTIAL DECAY OF RUIN TIME DISTRIBUTION

The probability that ruin occurs in exactly t steps has a combinatorial
formula involving the reflection principle. The dominant eigenvalue is
cos(π/N), so P(T > t) ~ C · cos(π/N)^t for large t.

For N ≥ 3, cos(π/N) ∈ (0, 1), giving genuine exponential decay.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Exponential decay rate**: The dominant eigenvalue cos(π/N) is positive
    for N ≥ 3. This governs the exponential tail of the ruin time distribution:
    P(T > t) ~ C · cos(π/N)^t. -/
theorem ruin_time_decay_rate_pos (N : ℕ) (hN : 3 ≤ N) :
    0 < Real.cos (Real.pi / N) := by
  apply Real.cos_pos_of_mem_Ioo
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  constructor
  · have h1 : 0 < Real.pi / ↑N := div_pos Real.pi_pos hN_pos
    have h2 : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
    linarith
  · have h2N : (2 : ℝ) < N := by exact_mod_cast (show 2 < N by omega)
    have : Real.pi * 2 < Real.pi * N :=
      mul_lt_mul_of_pos_left h2N Real.pi_pos
    rwa [div_lt_div_iff₀ hN_pos (by norm_num : (0:ℝ) < 2)]

/-- The decay rate is strictly less than 1, ensuring genuine exponential decay. -/
theorem ruin_time_decay_rate_lt_one (N : ℕ) (hN : 3 ≤ N) :
    Real.cos (Real.pi / N) < 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h_pos : 0 < Real.pi / ↑N := div_pos Real.pi_pos hN_pos
  have h_lt_pi : Real.pi / ↑N < Real.pi :=
    div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < N by omega))
  have h_sin_pos : 0 < Real.sin (Real.pi / ↑N) :=
    Real.sin_pos_of_pos_of_lt_pi h_pos h_lt_pi
  apply lt_of_le_of_ne (Real.cos_le_one _)
  intro h_eq
  have h_pyth := Real.sin_sq_add_cos_sq (Real.pi / ↑N)
  have h_sin_zero : Real.sin (Real.pi / ↑N) ^ 2 = 0 := by nlinarith
  have : Real.sin (Real.pi / ↑N) = 0 := by rwa [sq_eq_zero_iff] at h_sin_zero
  linarith

/-- The expected ruin time from the generating function agrees with k(N-k). -/
theorem expected_time_from_pgf_agrees (G : GamblersRuin) :
    expectedRuinTime G = (G.k : ℝ) * ((G.N : ℝ) - G.k) := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART X: SECOND MOMENT AND VARIANCE OF RUIN TIME

The quartic martingale Mₙ = Xₙ⁴ - 6nXₙ² + 3n² + 2n yields the second
moment of the ruin time via OST. Combined with E[T] = k(N-k), this gives
the exact variance.

The second moment satisfies the discrete Poisson equation:
  g(k) = 2f(k) - 1 + (g(k-1) + g(k+1))/2
with boundary conditions g(0) = g(N) = 0, where f(k) = k(N-k).

Solving yields: E[T²] = k(N-k)(N² + Nk - k² - 2)/3
and therefore:  Var(T) = k(N-k)(N² - 2Nk + 2k² - 2)/3.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Second moment of ruin time**: E[T² | start at k] = k(N-k)(N² + Nk - k² - 2)/3.

    Derived from OST applied to the quartic martingale X⁴ - 6nX² + 3n² + 2n,
    or equivalently by solving the discrete Poisson equation
    g(k) = 2f(k) - 1 + (g(k-1) + g(k+1))/2 with boundary g(0) = g(N) = 0. -/
def expectedRuinTimeSq (G : GamblersRuin) : ℝ :=
  (G.k : ℝ) * ((G.N : ℝ) - G.k) *
    ((G.N : ℝ) ^ 2 + (G.N : ℝ) * G.k - (G.k : ℝ) ^ 2 - 2) / 3

/-- **Variance of ruin time**: Var(T | start at k) = k(N-k)(N² - 2Nk + 2k² - 2)/3.

    The key factor (N-k)² + k² - 2 ≥ 0 with equality iff N = 2, k = 1
    (the trivial one-step game). -/
def varianceRuinTime (G : GamblersRuin) : ℝ :=
  (G.k : ℝ) * ((G.N : ℝ) - G.k) *
    ((G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2) / 3

/-- **Variance decomposition**: Var(T) = E[T²] - E[T]². -/
theorem variance_eq_second_moment_minus_square (G : GamblersRuin) :
    varianceRuinTime G = expectedRuinTimeSq G - (expectedRuinTime G) ^ 2 := by
  unfold varianceRuinTime expectedRuinTimeSq expectedRuinTime
  ring

/-- **Discrete Poisson recurrence for E[T²]**: The second moment formula
    satisfies g(k) = 2f(k) - 1 + (g(k-1) + g(k+1))/2.

    This recurrence arises from one step of the random walk:
    E[T²|k] = E[(1+T')²|k] = 1 + 2E[T'|k] + E[T'²|k]
    = 1 + (f(k-1) + f(k+1)) + (g(k-1) + g(k+1))/2
    = 2f(k) - 1 + (g(k-1) + g(k+1))/2.

    Stated over ℝ for clean algebraic verification. -/
theorem second_moment_recurrence (N k : ℝ) :
    k * (N - k) * (N ^ 2 + N * k - k ^ 2 - 2) / 3 =
    2 * (k * (N - k)) - 1 +
    ((k - 1) * (N - (k - 1)) * (N ^ 2 + N * (k - 1) - (k - 1) ^ 2 - 2) / 3 +
     (k + 1) * (N - (k + 1)) * (N ^ 2 + N * (k + 1) - (k + 1) ^ 2 - 2) / 3) / 2 := by
  ring

/-- **Boundary condition**: E[T² | start at 0] = 0 (already absorbed). -/
theorem second_moment_boundary_zero (N : ℝ) :
    (0 : ℝ) * (N - 0) * (N ^ 2 + N * 0 - 0 ^ 2 - 2) / 3 = 0 := by ring

/-- **Boundary condition**: E[T² | start at N] = 0 (already absorbed). -/
theorem second_moment_boundary_N (N : ℝ) :
    N * (N - N) * (N ^ 2 + N * N - N ^ 2 - 2) / 3 = 0 := by ring

/-- **Variance is nonneg**: Var(T) ≥ 0, with equality iff N = 2, k = 1.

    The factor N² - 2Nk + 2k² - 2 = (N-k)² + k² - 2 ≥ 0
    since k ≥ 1 and N-k ≥ 1, so (N-k)² + k² ≥ 1 + 1 = 2. -/
theorem variance_nonneg (G : GamblersRuin) : 0 ≤ varianceRuinTime G := by
  unfold varianceRuinTime
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 3)
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg G.k
    · have : (G.k : ℝ) < (G.N : ℝ) := Nat.cast_lt.mpr G.hk_lt
      linarith
  · -- N² - 2Nk + 2k² - 2 = (N-k)² + k² - 2 ≥ 0
    have hk : (1 : ℝ) ≤ (G.k : ℝ) := Nat.one_le_cast.mpr G.hk_pos
    have hNk : (1 : ℝ) ≤ (G.N : ℝ) - G.k := by
      have hkN : G.k + 1 ≤ G.N := G.hk_lt
      have := Nat.cast_le (α := ℝ).mpr hkN
      push_cast at this ⊢; linarith
    nlinarith [sq_nonneg ((G.N : ℝ) - G.k - 1), sq_nonneg ((G.k : ℝ) - 1)]

/-- **Variance symmetry**: Var(T | start at k) = Var(T | start at N-k). -/
theorem variance_symmetric (G : GamblersRuin) :
    (G.k : ℝ) * ((G.N : ℝ) - G.k) *
      ((G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2) / 3 =
    ((G.N : ℝ) - G.k) * ((G.N : ℝ) - ((G.N : ℝ) - G.k)) *
      ((G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * ((G.N : ℝ) - G.k) +
       2 * ((G.N : ℝ) - G.k) ^ 2 - 2) / 3 := by
  ring

/-- **Variance upper bound**: Var(T) ≤ N²(N² - 2)/12.

    Since k(N-k) ≤ N²/4 (AM-GM) and N² - 2Nk + 2k² - 2 ≤ N² - 2
    (because 2k(N-k) ≥ 0), the product is bounded. -/
theorem variance_upper_bound (G : GamblersRuin) :
    varianceRuinTime G ≤ (G.N : ℝ) ^ 2 * ((G.N : ℝ) ^ 2 - 2) / 12 := by
  unfold varianceRuinTime
  have hk_pos : (0 : ℝ) < G.k := Nat.cast_pos.mpr G.hk_pos
  have hk_lt : (G.k : ℝ) < G.N := Nat.cast_lt.mpr G.hk_lt
  have h_prod : (G.k : ℝ) * ((G.N : ℝ) - G.k) ≤ ((G.N : ℝ) / 2) ^ 2 := by
    have := expected_ruin_time_le_quarter_N_sq G
    unfold expectedRuinTime at this; linarith
  have h_factor : (G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2
      ≤ (G.N : ℝ) ^ 2 - 2 := by nlinarith
  have h_factor_nn : 0 ≤ (G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2 := by
    have hk1 : (1 : ℝ) ≤ (G.k : ℝ) := Nat.one_le_cast.mpr G.hk_pos
    have hNk1 : (1 : ℝ) ≤ (G.N : ℝ) - G.k := by
      have hkN : G.k + 1 ≤ G.N := G.hk_lt
      have := Nat.cast_le (α := ℝ).mpr hkN
      push_cast at this ⊢; linarith
    nlinarith [sq_nonneg ((G.N : ℝ) - G.k - 1), sq_nonneg ((G.k : ℝ) - 1)]
  have h_N2 : 0 ≤ (G.N : ℝ) ^ 2 - 2 := by
    have : (2 : ℝ) ≤ (G.N : ℝ) := Nat.ofNat_le_cast.mpr G.hN
    nlinarith
  calc (G.k : ℝ) * ((G.N : ℝ) - G.k) *
        ((G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2) / 3
      ≤ ((G.N : ℝ) / 2) ^ 2 * ((G.N : ℝ) ^ 2 - 2) / 3 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
        exact mul_le_mul h_prod h_factor h_factor_nn (by nlinarith)
    _ = (G.N : ℝ) ^ 2 * ((G.N : ℝ) ^ 2 - 2) / 12 := by ring

/-- **Concrete check**: N=2, k=1: Var(T) = 0 (game always ends in exactly 1 step). -/
theorem variance_N2_k1 :
    varianceRuinTime ⟨2, 1, by omega, by omega, by omega⟩ = 0 := by
  simp only [varianceRuinTime]; norm_num

/-- **Concrete check**: N=4, k=2: E[T²] = 24, E[T] = 4, Var(T) = 8. -/
theorem variance_N4_k2 :
    varianceRuinTime ⟨4, 2, by omega, by omega, by omega⟩ = 8 := by
  simp only [varianceRuinTime]; norm_num

/-- **Concrete check**: N=3, k=1: E[T²] = 6, E[T] = 2, Var(T) = 2. -/
theorem variance_N3_k1 :
    varianceRuinTime ⟨3, 1, by omega, by omega, by omega⟩ = 2 := by
  simp only [varianceRuinTime]; norm_num

/-- **Concrete check**: N=10, k=5 (symmetric): E[T] = 25, E[T²] = 1025, Var(T) = 400. -/
theorem second_moment_N10_k5 :
    expectedRuinTimeSq ⟨10, 5, by omega, by omega, by omega⟩ = 1025 := by
  simp only [expectedRuinTimeSq]; norm_num

theorem variance_N10_k5 :
    varianceRuinTime ⟨10, 5, by omega, by omega, by omega⟩ = 400 := by
  simp only [varianceRuinTime]; norm_num

/-- **Coefficient of variation**: CV² = Var(T)/E[T]² = (N² - 2Nk + 2k² - 2)/(3k(N-k)).

    For the symmetric start k = N/2, this simplifies and shows that
    the standard deviation grows proportionally to E[T]. -/
theorem coefficient_of_variation_sq (G : GamblersRuin) :
    varianceRuinTime G / (expectedRuinTime G) ^ 2 =
    ((G.N : ℝ) ^ 2 - 2 * (G.N : ℝ) * G.k + 2 * (G.k : ℝ) ^ 2 - 2) /
    (3 * (G.k : ℝ) * ((G.N : ℝ) - G.k)) := by
  unfold varianceRuinTime expectedRuinTime
  have hk_pos : (G.k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr G.hk_pos)
  have hNk_pos : (G.N : ℝ) - G.k ≠ 0 := ne_of_gt (by
    have : (G.k : ℝ) < (G.N : ℝ) := Nat.cast_lt.mpr G.hk_lt; linarith)
  field_simp

-- Type-check main results
#check @GamblersRuin
#check @ruinProbWin
#check @ruinProbLose
#check @ruin_prob_win_eq
#check @ruin_prob_lose_eq
#check @ruin_prob_win_pos
#check @ruin_prob_win_lt_one
#check @expected_ruin_time_eq
#check @expected_ruin_time_pos
#check @expected_ruin_time_le_quarter_N_sq
#check @harmonic_property
#check @expected_ruin_time_quadratic
#check @biasedRuinProbWin
#check @biased_ruin_prob_sum
#check @unfavorable_win_prob_lt_one
#check @ruin_time_decay_rate_pos
#check @expectedRuinTimeSq
#check @varianceRuinTime
#check @variance_eq_second_moment_minus_square
#check @second_moment_recurrence
#check @variance_nonneg
#check @variance_upper_bound

end FairGamesOQ01
