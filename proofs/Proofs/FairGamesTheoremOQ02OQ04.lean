/-
# Biased Gambler's Ruin: Concrete Examples and Structural Properties

## Research Problem: fair-games-theorem-oq-02-oq-04

The `BiasedGamblersRuin` structure and `biasedRuinProbWin` formula are already defined
in `FairGamesTheoremOQ01.lean`. This file answers the open question by:

1. **Concrete examples**: Favorable (p=2/3) and unfavorable (p=1/3) games with k=2, N=4.
   Win probabilities computed exactly: P(win) = 4/5 and P(win) = 1/5.

2. **Win probability is in (0,1)**: For favorable games (r < 1), biasedRuinProbWin ∈ (0,1).

3. **Monotonicity in k**: More starting wealth → higher win probability.

4. **Favorable game beats the fair case**: For p > 1/2 (r < 1): `biasedRuinProbWin B > k/N`.
   Proof: The difference k * (1-r^N) - B.N * (1-r^k) is negative, proved by bounding the
   tail sum ∑_{j ∈ Ico k N} r^j ≤ (N-k)*r^k and the prefix sum ∑_{i<k} r^i ≥ k*r^{k-1},
   then using r^k < r^{k-1} (strict since r < 1 and k ≥ 1).

5. **Duality check**: P(win | p=2/3, k=2, N=4) + P(win | p=1/3, k=2, N=4) = 1.

**Status**: Complete (0 sorries, 0 axioms).
-/

import Mathlib
import Proofs.FairGamesTheoremOQ01

set_option linter.unusedVariables false

namespace FairGamesOQ02OQ04

open FairGamesOQ01 Finset

noncomputable section

/-
════════════════════════════════════════════════════════════════════════════
PART I: CONCRETE FAVORABLE GAME (p = 2/3, k = 2, N = 4)
════════════════════════════════════════════════════════════════════════════ -/

/-- **Favorable game**: step-up probability p = 2/3, starting at k = 2, barrier N = 4.
    The gambler has the edge: odds ratio r = q/p = (1/3)/(2/3) = 1/2 < 1. -/
def favorableGame : BiasedGamblersRuin where
  N := 4
  k := 2
  p := 2 / 3
  hN := by norm_num
  hk_pos := by norm_num
  hk_lt := by norm_num
  hp_pos := by norm_num
  hp_lt := by norm_num

/-- The odds ratio for the favorable game is 1/2. -/
theorem favorableGame_r : favorableGame.r = 1 / 2 := by
  unfold BiasedGamblersRuin.r BiasedGamblersRuin.q favorableGame
  norm_num

/-- **Win probability in the favorable game**: P(win) = 4/5.
    Computation: (1 - (1/2)²) / (1 - (1/2)⁴) = (3/4) / (15/16) = 4/5. -/
theorem favorableGame_win_prob : biasedRuinProbWin favorableGame = 4 / 5 := by
  unfold biasedRuinProbWin
  rw [favorableGame_r, show favorableGame.k = 2 from rfl, show favorableGame.N = 4 from rfl]
  norm_num

/-- In the favorable game, the win probability exceeds the fair-game benchmark k/N = 1/2. -/
theorem favorableGame_beats_fair_concrete : (1 : ℝ) / 2 < biasedRuinProbWin favorableGame := by
  rw [favorableGame_win_prob]; norm_num

/-
════════════════════════════════════════════════════════════════════════════
PART II: CONCRETE UNFAVORABLE GAME (p = 1/3, k = 2, N = 4)
════════════════════════════════════════════════════════════════════════════ -/

/-- **Unfavorable game**: step-up probability p = 1/3, starting at k = 2, barrier N = 4.
    The house has the edge: odds ratio r = q/p = (2/3)/(1/3) = 2 > 1. -/
def unfavorableGame : BiasedGamblersRuin where
  N := 4
  k := 2
  p := 1 / 3
  hN := by norm_num
  hk_pos := by norm_num
  hk_lt := by norm_num
  hp_pos := by norm_num
  hp_lt := by norm_num

/-- The odds ratio for the unfavorable game is 2. -/
theorem unfavorableGame_r : unfavorableGame.r = 2 := by
  unfold BiasedGamblersRuin.r BiasedGamblersRuin.q unfavorableGame
  norm_num

/-- **Win probability in the unfavorable game**: P(win) = 1/5.
    Computation: (1 − 4) / (1 − 16) = (−3) / (−15) = 1/5. -/
theorem unfavorableGame_win_prob : biasedRuinProbWin unfavorableGame = 1 / 5 := by
  unfold biasedRuinProbWin
  rw [unfavorableGame_r, show unfavorableGame.k = 2 from rfl, show unfavorableGame.N = 4 from rfl]
  norm_num

/-- In the unfavorable game, win probability is below the fair-game benchmark. -/
theorem unfavorableGame_below_fair_concrete : biasedRuinProbWin unfavorableGame < (1 : ℝ) / 2 := by
  rw [unfavorableGame_win_prob]; norm_num

/-- **Duality**: These two concrete games (with swapped p ↔ q and k ↔ N-k) are complementary.
    P(win | p=2/3, k=2, N=4) + P(win | p=1/3, k=2, N=4) = 1. -/
theorem dual_games_sum_to_one :
    biasedRuinProbWin favorableGame + biasedRuinProbWin unfavorableGame = 1 := by
  rw [favorableGame_win_prob, unfavorableGame_win_prob]; norm_num

/-
════════════════════════════════════════════════════════════════════════════
PART III: WIN PROBABILITY IS IN (0, 1) FOR FAVORABLE GAMES
════════════════════════════════════════════════════════════════════════════ -/

/-- For a favorable game (r < 1), the win probability is strictly positive. -/
theorem biasedRuinProbWin_pos (B : BiasedGamblersRuin) (hr_lt : B.r < 1) :
    0 < biasedRuinProbWin B := by
  unfold biasedRuinProbWin
  apply div_pos
  · exact sub_pos.mpr (pow_lt_one₀ (le_of_lt B.r_pos) hr_lt
      (Nat.pos_iff_ne_zero.mp B.hk_pos))
  · exact sub_pos.mpr (pow_lt_one₀ (le_of_lt B.r_pos) hr_lt
      (by have := B.hN; omega))

/-- For a favorable game (r < 1), the win probability is strictly less than 1.
    The gambler still has a positive probability of ruin. -/
theorem biasedRuinProbWin_lt_one (B : BiasedGamblersRuin) (hr_lt : B.r < 1) :
    biasedRuinProbWin B < 1 := by
  unfold biasedRuinProbWin
  have hd : 0 < 1 - B.r ^ B.N :=
    sub_pos.mpr (pow_lt_one₀ (le_of_lt B.r_pos) hr_lt (by have := B.hN; omega))
  rw [div_lt_one hd]
  -- r^N < r^k since r < 1 and k < N (larger exponent → smaller value)
  have hrNk : B.r ^ B.N < B.r ^ B.k := by
    have hm : B.r ^ B.N = B.r ^ B.k * B.r ^ (B.N - B.k) := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt B.hk_lt)]
    have hlt : B.r ^ (B.N - B.k) < 1 :=
      pow_lt_one₀ (le_of_lt B.r_pos) hr_lt
        (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt B.hk_lt))
    have h := mul_lt_mul_of_pos_left hlt (pow_pos B.r_pos B.k)
    simp only [mul_one] at h; linarith [hm]
  linarith

/-
════════════════════════════════════════════════════════════════════════════
PART IV: MONOTONICITY — MORE STARTING WEALTH HELPS IN FAVORABLE GAMES
════════════════════════════════════════════════════════════════════════════ -/

/-- **Monotonicity**: Win probability increases strictly with starting wealth in favorable games.
    For r < 1 and k₁ < k₂ < N, the formula (1−rᵏ)/(1−rᴺ) is strictly increasing in k
    because rᵏ decreases as k increases (so 1−rᵏ increases). -/
theorem biasedRuinProbWin_strictMono (r : ℝ) (hr_pos : 0 < r) (hr_lt : r < 1)
    (k₁ k₂ N : ℕ) (hk₁k₂ : k₁ < k₂) (hk₂N : k₂ < N) :
    (1 - r ^ k₁) / (1 - r ^ N) < (1 - r ^ k₂) / (1 - r ^ N) := by
  have hd_pos : 0 < 1 - r ^ N :=
    sub_pos.mpr (pow_lt_one₀ (le_of_lt hr_pos) hr_lt (by omega))
  rw [div_lt_div_iff₀ hd_pos hd_pos]
  -- r^k₂ < r^k₁ since r < 1 and k₁ < k₂ (larger exponent → smaller value)
  have hrk₂k₁ : r ^ k₂ < r ^ k₁ := by
    have hm : r ^ k₂ = r ^ k₁ * r ^ (k₂ - k₁) := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hk₁k₂)]
    have hlt : r ^ (k₂ - k₁) < 1 :=
      pow_lt_one₀ (le_of_lt hr_pos) hr_lt
        (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hk₁k₂))
    have h := mul_lt_mul_of_pos_left hlt (pow_pos hr_pos k₁)
    simp only [mul_one] at h; linarith [hm]
  exact mul_lt_mul_of_pos_right (by linarith) hd_pos

/-
════════════════════════════════════════════════════════════════════════════
PART V: FAVORABLE GAME BEATS THE FAIR CASE

Key lemma: for r ∈ (0,1), k ∈ (0,N): B.k * (∑_{i<N} rⁱ) < B.N * (∑_{i<k} rⁱ)

Proof using sum bounds:
  - ∑_{i<k} rⁱ ≥ k · r^{k-1}  (each term rⁱ ≥ r^{k-1} for i ≤ k-1, since r < 1)
  - ∑_{j ∈ Ico k N} rʲ ≤ (N-k) · rᵏ (each term rʲ ≤ rᵏ for j ≥ k, since r < 1)
  - k · (N-k) · rᵏ < (N-k) · k · r^{k-1} (since r^{k-1} > rᵏ for r < 1, k ≥ 1)
════════════════════════════════════════════════════════════════════════════ -/

/-- **Key sum inequality**: For r ∈ (0,1) and 0 < k < N,
    the average of the first k powers exceeds the average of all N powers.
    Equivalently: k * ∑_{i<N} rⁱ < N * ∑_{i<k} rⁱ. -/
private lemma key_sum_ineq (r : ℝ) (hr_pos : 0 < r) (hr_lt : r < 1)
    (k N : ℕ) (hk : 0 < k) (hkN : k < N) :
    (k : ℝ) * ∑ i ∈ range N, r ^ i < (N : ℝ) * ∑ i ∈ range k, r ^ i := by
  -- Lower bound on prefix sum: ∑_{i<k} rⁱ ≥ k · r^{k-1}
  -- Each i < k satisfies i ≤ k-1, so r^i ≥ r^{k-1} since r < 1
  have hA_lower : (k : ℝ) * r ^ (k - 1) ≤ ∑ i ∈ range k, r ^ i :=
    calc (k : ℝ) * r ^ (k - 1)
        = ∑ _i ∈ range k, r ^ (k - 1) := by
            rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range k, r ^ i :=
          Finset.sum_le_sum (fun i hi =>
            pow_le_pow_of_le_one (le_of_lt hr_pos) (le_of_lt hr_lt)
              (by have := mem_range.mp hi; omega))
  -- Upper bound on tail sum: ∑_{j ∈ Ico k N} rʲ ≤ (N-k) · rᵏ
  -- Each j ≥ k satisfies r^j ≤ r^k since r < 1
  have hC_upper : ∑ j ∈ Ico k N, r ^ j ≤ ((N - k : ℕ) : ℝ) * r ^ k :=
    calc ∑ j ∈ Ico k N, r ^ j
        ≤ ∑ _j ∈ Ico k N, r ^ k :=
            Finset.sum_le_sum (fun j hj =>
              pow_le_pow_of_le_one (le_of_lt hr_pos) (le_of_lt hr_lt)
                (mem_Ico.mp hj).1)
      _ = ((N - k : ℕ) : ℝ) * r ^ k := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  -- Strict inequality: rᵏ < r^{k-1} for r < 1 and k ≥ 1
  have hrk_lt : r ^ k < r ^ (k - 1) := by
    have hm : r ^ k = r ^ (k - 1) * r ^ (k - (k - 1)) := by
      rw [← pow_add]; congr 1; omega
    have hlt : r ^ (k - (k - 1)) < 1 :=
      pow_lt_one₀ (le_of_lt hr_pos) hr_lt (by omega)
    have h := mul_lt_mul_of_pos_left hlt (pow_pos hr_pos (k - 1))
    simp only [mul_one] at h; linarith [hm]
  -- Positivity helpers
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hNk_pos' : (0 : ℝ) < (N - k : ℕ) := by exact_mod_cast (show 0 < N - k by omega)
  -- Split: ∑_{i<N} rⁱ = ∑_{i<k} rⁱ + ∑_{j ∈ Ico k N} rʲ
  have hSplit : ∑ i ∈ range N, r ^ i =
      ∑ i ∈ range k, r ^ i + ∑ j ∈ Ico k N, r ^ j := by
    have h := Finset.sum_range_add_sum_Ico (f := fun i => r ^ i) (Nat.le_of_lt hkN)
    linarith
  -- Reformulate: suffices to show k * ∑ Ico < (N-k) * ∑ range k
  rw [hSplit, mul_add]
  suffices h : (k : ℝ) * ∑ j ∈ Ico k N, r ^ j < ((N - k : ℕ) : ℝ) * ∑ i ∈ range k, r ^ i by
    have hA_nn : 0 ≤ ∑ i ∈ range k, r ^ i :=
      sum_nonneg (fun i _ => pow_nonneg (le_of_lt hr_pos) i)
    have : ((N : ℝ) - k) = ((N - k : ℕ) : ℝ) := (Nat.cast_sub (Nat.le_of_lt hkN)).symm
    -- Bridge: N * ∑k = k * ∑k + (N-k) * ∑k  (nonlinear, must provide explicitly)
    have hN_split : (N : ℝ) * ∑ i ∈ range k, r ^ i =
        (k : ℝ) * ∑ i ∈ range k, r ^ i + ((N - k : ℕ) : ℝ) * ∑ i ∈ range k, r ^ i := by
      rw [← add_mul]; congr 1; linarith
    linarith [mul_nonneg hk_pos'.le hA_nn]
  -- Prove the key inequality via the sum bounds chain
  calc (k : ℝ) * ∑ j ∈ Ico k N, r ^ j
      ≤ k * (((N - k : ℕ) : ℝ) * r ^ k) := by
          apply mul_le_mul_of_nonneg_left hC_upper (Nat.cast_nonneg _)
    _ < k * (((N - k : ℕ) : ℝ) * r ^ (k - 1)) := by
          apply mul_lt_mul_of_pos_left _ hk_pos'
          exact mul_lt_mul_of_pos_left hrk_lt hNk_pos'
    _ = ((N - k : ℕ) : ℝ) * ((k : ℝ) * r ^ (k - 1)) := by ring
    _ ≤ ((N - k : ℕ) : ℝ) * ∑ i ∈ range k, r ^ i := by
          exact mul_le_mul_of_nonneg_left hA_lower hNk_pos'.le

/-- **Favorable beats fair**: For p > 1/2, the biased win probability exceeds k/N.

    When the gambler has an edge (p > 1/2), the biased formula gives strictly more
    than the fair-game k/N. Uses the key sum inequality and geometric series factoring. -/
theorem favorable_beats_fair (B : BiasedGamblersRuin) (hp : 1 / 2 < B.p) :
    (B.k : ℝ) / B.N < biasedRuinProbWin B := by
  have hr_lt : B.r < 1 := favorable_game_r_lt_one B hp
  have hr_pos := B.r_pos
  have hN_pos : (0 : ℝ) < B.N := Nat.cast_pos.mpr (by have := B.hN; omega)
  have hd_pos : 0 < 1 - B.r ^ B.N :=
    sub_pos.mpr (pow_lt_one₀ (le_of_lt hr_pos) hr_lt (by have := B.hN; omega))
  rw [biasedRuinProbWin, div_lt_div_iff₀ hN_pos hd_pos]
  -- Goal: B.k * (1 - B.r^B.N) < B.N * (1 - B.r^B.k)
  -- Factor using geometric sum: 1 - r^m = (1 - r) * ∑_{i<m} rⁱ
  have h1r : 0 < 1 - B.r := sub_pos.mpr hr_lt
  have geomN : 1 - B.r ^ B.N = (1 - B.r) * ∑ i ∈ range B.N, B.r ^ i :=
    (mul_neg_geom_sum B.r B.N).symm
  have geomk : 1 - B.r ^ B.k = (1 - B.r) * ∑ i ∈ range B.k, B.r ^ i :=
    (mul_neg_geom_sum B.r B.k).symm
  rw [geomN, geomk]
  -- Factor out (1 - B.r) and cancel
  calc (B.k : ℝ) * ((1 - B.r) * ∑ i ∈ range B.N, B.r ^ i)
      = (1 - B.r) * ((B.k : ℝ) * ∑ i ∈ range B.N, B.r ^ i) := by ring
    _ < (1 - B.r) * ((B.N : ℝ) * ∑ i ∈ range B.k, B.r ^ i) := by
        apply mul_lt_mul_of_pos_left _ h1r
        exact key_sum_ineq B.r hr_pos hr_lt B.k B.N B.hk_pos B.hk_lt
    _ = ((1 - B.r) * ∑ i ∈ range B.k, B.r ^ i) * (B.N : ℝ) := by ring

/-
════════════════════════════════════════════════════════════════════════════
PART VI: ALTERNATIVE FORMULA VIA RECIPROCAL ODDS RATIO
════════════════════════════════════════════════════════════════════════════

The standard formula uses r = q/p (odds ratio ≥ 1 for the house). An equivalent
form uses s = p/q = r⁻¹ (the gambler's reciprocal odds):

  P(lose | k, N, p) = (s^(N−k) − 1) / (s^N − 1)

Proof: s = r⁻¹, so s^n = (r^n)⁻¹. Substituting and clearing denominators:
  (s^(N-k) − 1) / (s^N − 1)
  = ((r^(N-k))⁻¹ − 1) / ((r^N)⁻¹ − 1)
  = r^k · (1 − r^(N-k)) / (1 − r^N)    [multiply num/denom by r^N]
  = (r^k − r^N) / (1 − r^N)              [factor r^k out of numerator]
  = biasedRuinProbLose                    ✓
════════════════════════════════════════════════════════════════════════════ -/

/-- **Alternative formula for losing ruin probability**: When p ≠ 1/2, the
    probability of ruin starting at k can be written using the reciprocal
    odds ratio s = p/q:

    P(lose | k, N, p) = (s^(N−k) − 1) / (s^N − 1)

    This is algebraically equivalent to the standard formula
    `biasedRuinProbLose B = (r^k − r^N) / (1 − r^N)` via r = q/p ↔ s = r⁻¹. -/
theorem biasedRuinProbLose_alt_formula (B : BiasedGamblersRuin) (hp_ne : B.p ≠ 1 / 2) :
    biasedRuinProbLose B =
    ((B.p / B.q) ^ (B.N - B.k) - 1) / ((B.p / B.q) ^ B.N - 1) := by
  have hr_pos : 0 < B.r := B.r_pos
  have hr_ne : B.r ≠ 0 := hr_pos.ne'
  -- r ≠ 1 (equivalent to p ≠ 1/2)
  have hr_ne_one : B.r ≠ 1 := by
    intro hr
    apply hp_ne
    have : B.q / B.p = 1 := hr
    rw [div_eq_iff B.hp_pos.ne'] at this
    linarith [B.p_add_q]
  -- r^N ≠ 1 (since r ≠ 1 and N ≥ 2 > 0)
  have hN_ne : B.N ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num) B.hN)
  have hrN_ne_one : B.r ^ B.N ≠ 1 := by
    rcases lt_or_gt_of_ne hr_ne_one with hr_lt | hr_gt
    · exact (pow_lt_one₀ (le_of_lt hr_pos) hr_lt hN_ne).ne
    · have : 1 < B.r ^ B.N :=
        calc (1 : ℝ) = B.r ^ 0 := (pow_zero _).symm
          _ < B.r ^ B.N := pow_lt_pow_right₀ hr_gt
              (Nat.pos_of_ne_zero hN_ne)
      linarith
  -- p/q = r⁻¹ (since r = q/p by definition, so (q/p)⁻¹ = p/q)
  have hpq_eq : B.p / B.q = (B.r)⁻¹ := by
    unfold BiasedGamblersRuin.r; rw [inv_div]
  -- k + (N − k) = N as natural numbers (since k < N)
  have hm : B.k + (B.N - B.k) = B.N := Nat.add_sub_cancel' (Nat.le_of_lt B.hk_lt)
  -- Nonzero helpers for r^k and r^(N-k)
  have hrk_ne : B.r ^ B.k ≠ 0 := (pow_pos hr_pos _).ne'
  have hrm_ne : B.r ^ (B.N - B.k) ≠ 0 := (pow_pos hr_pos _).ne'
  -- r^N = r^k · r^(N−k) via pow_add
  have hrN_eq : B.r ^ B.N = B.r ^ B.k * B.r ^ (B.N - B.k) := by
    rw [← pow_add, hm]
  -- r^k · r^(N−k) ≠ 1 (same as r^N ≠ 1)
  have hab_ne_one : B.r ^ B.k * B.r ^ (B.N - B.k) ≠ 1 := hrN_eq ▸ hrN_ne_one
  -- 1 − r^k · r^(N−k) ≠ 0 (the LHS denominator)
  have hd_lhs : (1 : ℝ) - B.r ^ B.k * B.r ^ (B.N - B.k) ≠ 0 :=
    sub_ne_zero.mpr hab_ne_one.symm
  -- Main proof: unfold, substitute p/q = r⁻¹, then algebraic identity
  unfold biasedRuinProbLose
  rw [hpq_eq]
  simp only [inv_pow]   -- (r⁻¹)^n = (r^n)⁻¹
  rw [hrN_eq]           -- r^N → r^k * r^(N-k) everywhere
  field_simp [hrk_ne, hrm_ne, mul_ne_zero hrk_ne hrm_ne, hd_lhs, hab_ne_one]

end

end FairGamesOQ02OQ04
