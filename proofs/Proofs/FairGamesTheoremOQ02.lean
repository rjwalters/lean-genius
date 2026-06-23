/-
  Fair Games Theorem OQ-02: Concrete Examples

  Can a specific example be formalized — extending the Fair Games Theorem
  (Optional Stopping Theorem) to concrete gambling scenarios?

  This file formalizes concrete applications:
  1. The Gambler's Ruin with specific parameters (k=5, N=10)
  2. The Doubling Strategy (martingale betting system)
  3. Why the doubling strategy fails with finite bankroll

  Tags: probability, random-walk, martingale, gambling
-/

import Mathlib

namespace FairGamesOQ02

open FairGamesOQ01

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: CONCRETE GAMBLER'S RUIN EXAMPLE (k=5, N=10)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A concrete Gambler's Ruin instance: starting at 5 with barriers at 0 and 10.
    This represents a fair coin flip game where a player with $5 plays against
    an opponent with $5 (total $10 on the table). -/
def game_5_10 : GamblersRuin where
  N := 10
  k := 5
  hN := by norm_num
  hk_pos := by norm_num
  hk_lt := by norm_num

/-- In the (5, 10) game, the probability of winning is 1/2. -/
theorem game_5_10_win_prob : ruinProbWin game_5_10 = 1 / 2 := by
  simp [ruinProbWin, game_5_10]; norm_num

/-- In the (5, 10) game, the expected duration is 25. -/
theorem game_5_10_expected_time : expectedRuinTime game_5_10 = 25 := by
  simp [expectedRuinTime, game_5_10]; norm_num

/-- A concrete game where the underdog starts at 1 against 9. -/
def game_1_10 : GamblersRuin where
  N := 10
  k := 1
  hN := by norm_num
  hk_pos := by norm_num
  hk_lt := by norm_num

/-- The underdog (1 vs 9) has only 10% chance of winning. -/
theorem game_1_10_win_prob : ruinProbWin game_1_10 = 1 / 10 := by
  simp [ruinProbWin, game_1_10]; norm_num

/-- The underdog game has expected duration 9. -/
theorem game_1_10_expected_time : expectedRuinTime game_1_10 = 9 := by
  simp [expectedRuinTime, game_1_10]; norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE DOUBLING STRATEGY (MARTINGALE BETTING SYSTEM)

The "martingale" betting strategy (confusingly named, predating the
mathematical concept) is:
- Start by betting $1
- If you lose, double the bet: $2, $4, $8, ...
- If you win, you've recovered all losses plus $1 profit

With infinite bankroll, this always wins eventually. With finite bankroll B,
the strategy risks catastrophic loss: if you lose ⌊log₂ B⌋ times in a row,
you lose everything.

The Fair Games Theorem shows that with a finite stopping time (bounded
by the bankroll), the expected gain is exactly 0 — the doubling strategy
provides no advantage in expectation.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The bet size in the doubling strategy after k consecutive losses: 2^k. -/
def doublingBet (k : ℕ) : ℕ := 2 ^ k

/-- After k consecutive losses with the doubling strategy, total invested is 2^k - 1. -/
theorem doubling_total_invested (k : ℕ) : ∑ i ∈ Finset.range k, doublingBet i = 2 ^ k - 1 := by
  induction k with
  | zero => simp [doublingBet]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, doublingBet]
    omega

/-- If you win after k consecutive losses, your net gain is exactly 1.
    Invested 2^k - 1, received 2^k from the winning bet, net = +1. -/
theorem doubling_win_gain (k : ℕ) :
    (doublingBet k : ℤ) - (2 ^ k - 1 : ℤ) = 1 := by
  simp [doublingBet]; omega

/-- Maximum number of doublings possible with bankroll B: ⌊log₂(B+1)⌋ rounds. -/
def maxDoublings (B : ℕ) : ℕ := Nat.log 2 (B + 1)

/-- The doubling strategy can sustain at most ⌊log₂(B+1)⌋ consecutive losses.
    After that many losses, total investment exceeds bankroll. -/
theorem doubling_bankroll_limit (B : ℕ) (hB : 0 < B) :
    2 ^ maxDoublings B - 1 ≤ B := by
  unfold maxDoublings
  have h := Nat.pow_log_le_self 2 (B + 1)
  omega

/-- With bankroll B = 2^n - 1, exactly n doublings are possible. -/
theorem maxDoublings_power_of_two_minus_one (n : ℕ) (hn : 0 < n) :
    maxDoublings (2 ^ n - 1) = n := by
  unfold maxDoublings
  have h : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  rw [h, Nat.log_pow (by norm_num)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE FAIR GAMES THEOREM KILLS THE DOUBLING STRATEGY

With probability (1/2)^n, you lose n times in a row and lose 2^n - 1.
With probability 1 - (1/2)^n, you win at some point and gain 1.

Expected value = (1 - (1/2)^n) · 1 + (1/2)^n · (-(2^n - 1))
              = 1 - (1/2)^n - (1/2)^n · (2^n - 1)
              = 1 - (1/2)^n - 1 + (1/2)^n
              = 0

The Fair Games Theorem guarantees this without computing!
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The expected value of the doubling strategy with bankroll allowing n rounds
    is exactly 0. This is a direct computation confirming the Fair Games Theorem. -/
theorem doubling_expected_value_zero (n : ℕ) (hn : 0 < n) :
    (1 - (1 / 2 : ℝ) ^ n) * 1 + (1 / 2 : ℝ) ^ n * (-(2 ^ n - 1 : ℝ)) = 0 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  field_simp
  ring

end FairGamesOQ02

/-
  ## Summary

  This file provides concrete examples for the Fair Games Theorem:

  **Part I: Concrete Gambler's Ruin** (0 sorries)
  - game_5_10: Fair game (P(win) = 1/2, E[T] = 25)
  - game_1_10: Underdog game (P(win) = 1/10, E[T] = 9)

  **Part II: Doubling Strategy** (0 sorries)
  - Bet sizes: 2^k after k losses
  - Total investment after k losses: 2^k - 1
  - Win gain always = 1 regardless of loss streak length
  - Bankroll limits the number of possible doublings

  **Part III: Expected Value = 0** (0 sorries)
  - Direct computation: E[doubling strategy] = 0
  - Confirms the Fair Games Theorem for this specific strategy

  **Status**: 0 sorries, 0 axioms
-/
