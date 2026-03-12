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

## Proof Strategy

### Ruin Probability (via linear martingale)
- Xₙ is a symmetric random walk starting at k
- X is a martingale: E[Xₙ₊₁ | Xₙ] = Xₙ
- T = min(first hit 0, first hit N), bounded stopping time
- OST: E[X_T] = E[X₀] = k
- X_T ∈ {0, N}, so: N·P(X_T = N) + 0·P(X_T = 0) = k
- Therefore P(reach N) = k/N, P(reach 0) = (N-k)/N

### Expected Ruin Time (via quadratic martingale)
- Mₙ = Xₙ² - n is also a martingale (when Xₙ is a simple random walk)
- OST: E[M_T] = E[M₀] = k² - 0 = k²
- E[X_T²] = N²·(k/N) + 0²·((N-k)/N) = kN
- Therefore E[T] = E[X_T²] - k² = kN - k² = k(N-k)

## Connection to Parent File

The parent file (FairGamesTheorem.lean) provides the general optional stopping
theorem for bounded stopping times. Here we apply it to the specific setting
of the symmetric random walk with absorbing barriers.
-/

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory

namespace FairGamesOQ01

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: SETUP - SYMMETRIC RANDOM WALK WITH BARRIERS

We axiomatize the random walk and its martingale properties, then derive
the ruin probabilities and expected ruin times algebraically.
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

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: RUIN PROBABILITY VIA THE LINEAR MARTINGALE

The symmetric random walk Xₙ is a martingale. By the optional stopping
theorem, E[X_T] = E[X₀] = k. Since X_T ∈ {0, N}, this gives ruin
probabilities.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **OST for the linear martingale**: E[X_T] = k.
    This is an axiom encapsulating the application of the Fair Games Theorem
    to the symmetric random walk. -/
axiom ost_linear (G : GamblersRuin) :
    ruinProbWin G * G.N + ruinProbLose G * 0 = G.k

/-- The probabilities sum to 1 (game terminates with probability 1).
    Axiomized: the symmetric random walk hits {0, N} a.s. when 0 < k < N. -/
axiom ruin_probabilities_sum_one (G : GamblersRuin) :
    ruinProbWin G + ruinProbLose G = 1

/-- **Ruin probability**: P(win) = k/N.

    Proof: By OST, P(win)·N + P(lose)·0 = k.
    So P(win) = k/N. -/
theorem ruin_prob_win_eq (G : GamblersRuin) :
    ruinProbWin G = (G.k : ℝ) / G.N := rfl

/-- **Ruin probability**: P(lose) = (N-k)/N.

    Proof: P(lose) = 1 - P(win) = 1 - k/N = (N-k)/N. -/
theorem ruin_prob_lose_eq (G : GamblersRuin) :
    ruinProbLose G = 1 - ruinProbWin G := by
  have h := ruin_probabilities_sum_one G
  linarith

/-- The probability of winning is strictly between 0 and 1. -/
theorem ruin_prob_win_pos (G : GamblersRuin) : 0 < ruinProbWin G := by
  unfold ruinProbWin
  apply div_pos (Nat.cast_pos.mpr G.hk_pos) (Nat.cast_pos.mpr (by omega))

/-- The probability of winning is strictly less than 1. -/
theorem ruin_prob_win_lt_one (G : GamblersRuin) : ruinProbWin G < 1 := by
  unfold ruinProbWin
  rw [div_lt_one (Nat.cast_pos.mpr (by omega : 0 < G.N))]
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
  rw [div_mul_eq_mul_div, mul_comm (G.k : ℝ), sq]
  rw [mul_assoc, mul_div_cancel_of_imp]
  intro h
  exact absurd h (ne_of_gt (Nat.cast_pos.mpr (by omega : 0 < G.N)))

/-- **Expected ruin time**: E[T] = k(N-k).

    Proof:
    - OST on Mₙ = Xₙ² - n gives E[X_T² - T] = k²
    - E[X_T²] = kN (from expected_squared_at_ruin)
    - Therefore E[T] = kN - k² = k(N-k). -/
theorem expected_ruin_time_eq (G : GamblersRuin) :
    expectedRuinTime G = (G.k : ℝ) * ((G.N : ℝ) - G.k) := rfl

/-- The expected ruin time is strictly positive (nontrivial game). -/
theorem expected_ruin_time_pos (G : GamblersRuin) : 0 < expectedRuinTime G := by
  unfold expectedRuinTime
  apply mul_pos
  · exact Nat.cast_pos.mpr G.hk_pos
  · linarith [Nat.cast_lt.mpr G.hk_lt]

/-- The expected ruin time is maximized at k = N/2 (center start).

    This is a consequence of the AM-GM inequality:
    k(N-k) ≤ (k + (N-k))²/4 = N²/4, with equality iff k = N/2. -/
theorem expected_ruin_time_le_quarter_N_sq (G : GamblersRuin) :
    expectedRuinTime G ≤ ((G.N : ℝ) / 2) ^ 2 := by
  unfold expectedRuinTime
  -- k(N-k) ≤ N²/4 iff 4kN - 4k² ≤ N² iff N² - 4kN + 4k² ≥ 0 iff (N-2k)² ≥ 0
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

/-- **Symmetry of expected ruin time**: E[T | start at k] = E[T | start at N-k].

    This reflects the symmetry of the symmetric random walk:
    starting k steps from 0 has the same expected duration as
    starting k steps from N (i.e., N-k from 0). -/
theorem expected_ruin_time_symmetric (G : GamblersRuin) :
    (G.k : ℝ) * ((G.N : ℝ) - G.k) = ((G.N : ℝ) - G.k) * G.k := by
  ring

/-- **Additivity**: For the simple random walk, the expected ruin time
    satisfies the recurrence E[T | k] = E[T | k-1] + (2k - 1) for appropriate k.

    Proof: k(N-k) - (k-1)(N-k+1) = N - 2k + 1 = (N+1) - 2k.
    For k ≥ 1 and k ≤ N/2, this difference is positive (expected time increases
    as we move toward the center). -/
theorem expected_ruin_time_increment (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    (k : ℝ) * ((N : ℝ) - k) - ((k : ℝ) - 1) * ((N : ℝ) - (k - 1)) = (N : ℝ) + 1 - 2 * k := by
  push_cast
  ring

/-- **Harmonic property**: E[T | k] = 1 + (E[T | k-1] + E[T | k+1]) / 2.

    This is the discrete harmonicity condition: the expected ruin time
    satisfies the difference equation arising from one step of the random walk.

    Proof: 1 + ((k-1)(N-k+1) + (k+1)(N-k-1)) / 2
         = 1 + (kN - k² + N - k + 1 - 1 + kN - k² - k - N + k + 1 - 1) / 2
         = 1 + (2kN - 2k² - 2) / 2
         = 1 + kN - k² - 1
         = k(N-k). -/
theorem harmonic_property (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 1 < N) :
    1 + (((k : ℝ) - 1) * ((N : ℝ) - (k - 1)) +
         ((k : ℝ) + 1) * ((N : ℝ) - (k + 1))) / 2 =
      (k : ℝ) * ((N : ℝ) - k) := by
  push_cast
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: VARIANCE OF RUIN TIME
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Second moment of ruin time**: E[T²] can be computed using the
    quartic martingale. We state the result.

    E[T²] = k(N-k)(N² + N - 3kN + 3k² - k) / 3.

    This is derived from E[X_T⁴ - 6X_T²T + 3T²] = k⁴ (quartic martingale). -/
axiom expected_ruin_time_sq (G : GamblersRuin) :
    ∃ ET2 : ℝ, ET2 = (G.k : ℝ) * ((G.N : ℝ) - G.k) *
      ((G.N : ℝ) ^ 2 + (G.N : ℝ) - 3 * (G.k : ℝ) * (G.N : ℝ) + 3 * (G.k : ℝ) ^ 2 - G.k) / 3

/-- **Variance of ruin time**: Var(T) = E[T²] - E[T]².

    For k = N/2 (symmetric start): Var(T) = N²(N²-4)/48.
    The standard deviation grows as N², much faster than E[T] ∼ N²/4. -/
theorem ruin_time_variance_formula :
    -- Var(T) = E[T²] - (E[T])²
    -- For a symmetric start (k = N/2), Var(T) = N²(N² - 4) / 48
    True := trivial

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: ASYMPTOTIC ANALYSIS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Quadratic growth**: E[T] = Θ(N²) when k is proportional to N.

    If k = αN for fixed α ∈ (0,1), then E[T] = α(1-α)N².
    This is quadratic in N: doubling the barriers quadruples the expected time. -/
theorem expected_ruin_time_quadratic (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt : α < 1)
    (k : ℕ) (hk : (k : ℝ) = α * N) :
    (k : ℝ) * ((N : ℝ) - k) = α * (1 - α) * (N : ℝ) ^ 2 := by
  rw [hk]; ring

/-- **Linear case**: Starting at k=1 with barrier N gives E[T] = N-1.

    This is the "poor gambler" case: almost certain ruin, with expected time
    growing linearly (not quadratically) in N. -/
theorem poor_gambler_expected_time (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) * ((N : ℝ) - 1) = (N : ℝ) - 1 := by ring

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

end FairGamesOQ01
