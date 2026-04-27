/-
  Aristotle targets for Erdős Problem #263 (Irrationality Sequences)
  Helper lemmas for the integer-gap proof of doubleExp_sum_irrational.
  See Stubs/Erdos263Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main doubleExp_sum_irrational theorem (OPEN problem)
  - Supporting lemmas for the integer-gap argument that should be decidable
  - No definition sorries
  - No axioms

  Included targets (3):
  - doubleExp_tail_pos: Tail ∑' k, 1/2^{2^(k+N+1)} is positive
  - doubleExp_tail_bound: 2^{2^N} * tail < 1 / (2^{2^N} - 1)
  - tsum_split_at: ∑' n, f n = ∑ n < N, f n + f N + ∑' n, f (n + N + 1)

  Session 2026-04-24: Proved doubleExp_tail_pos and doubleExp_tail_bound by
  porting proofs from Stubs/Erdos263Problem.lean (where they were proved in
  sessions 5-8). All 3 Aristotle targets now 0-sorry.
-/
import Mathlib

open Real

namespace Erdos263Aristotle

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    calc m + 1 ≤ 2 ^ m + 1 := by linarith
      _ ≤ 2 ^ m * 2 := by linarith [Nat.one_le_pow m 2 (by norm_num)]
      _ = 2 ^ (m + 1) := by ring

-- Positive tail: each term 1/2^{2^(k+N+1)} is positive, so the tsum is positive.
-- Proof: compare with geometric series (1/2)^k via k ≤ 2^(k+N+1).
theorem doubleExp_tail_pos (N : ℕ) :
    0 < ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) := by
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))) := by
    apply Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => show (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) ≤ (1 / 2) ^ k from ?_)
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · have hexp : k ≤ 2 ^ (k + N + 1) :=
        (nat_le_two_pow k).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h_pow_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 ^ (k + N + 1)) :=
        pow_le_pow_right (by norm_num) hexp
      calc (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))
          ≤ 1 / (2 : ℝ) ^ k :=
              one_div_le_one_div_of_le (pow_pos (by norm_num) k) h_pow_le
        _ = (1 / 2) ^ k := by simp [div_pow, one_div]
  exact hsum.tsum_pos (fun k => by positivity) 0 (by positivity)

-- Tail bound: 2^{2^N} * Σ_{k≥0} 1/2^{2^(k+N+1)} < 1 / (2^{2^N} - 1).
-- Geometric bound: each term 1/D^{2^{k+1}} ≤ (1/D²)^{k+1} via 2*(k+1) ≤ 2^{k+1}.
-- So D*T ≤ D*Σ(1/D²)^{k+1} = D/(D²-1) < 1/(D-1).
theorem doubleExp_tail_bound (N : ℕ) :
    (2 : ℝ) ^ (2 ^ N) * ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) <
    1 / ((2 : ℝ) ^ (2 ^ N) - 1) := by
  set D := (2 : ℝ) ^ (2 ^ N) with hD_def
  have hD_pos : (0 : ℝ) < D := by positivity
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have h1 : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ N) := pow_le_pow_right (by norm_num) (by exact_mod_cast h1)
  have hD_ge1 : (1 : ℝ) ≤ D := by linarith
  have hD1_pos : (0 : ℝ) < D - 1 := by linarith
  have hD2_pos : (0 : ℝ) < D ^ 2 - 1 := by nlinarith
  -- Geometric ratio r = 1/D², with 0 ≤ r < 1
  set r := (1 : ℝ) / D ^ 2 with hr_def
  have hr_nn : (0 : ℝ) ≤ r := by positivity
  have hr_lt1 : r < 1 := by
    unfold_let r; rw [div_lt_one (by positivity)]; nlinarith
  -- Rewrite each term: 1/2^{2^{k+N+1}} = 1/D^{2^{k+1}}
  have hterm : ∀ k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) = 1 / D ^ (2 ^ (k + 1)) := by
    intro k; congr 1; rw [hD_def, ← pow_mul]; congr 1
    have : k + N + 1 = N + (k + 1) := by omega
    rw [this, pow_add]
  -- Key arithmetic: 2*(k+1) ≤ 2^{k+1}, proved via k+1 ≤ 2^k
  have key_arith : ∀ k : ℕ, 2 * (k + 1) ≤ 2 ^ (k + 1) := by
    intro k
    have h : k + 1 ≤ 2 ^ k := by
      induction k with
      | zero => norm_num
      | succ m ih =>
        calc m + 1 + 1 ≤ 2 ^ m + 1 := by linarith
          _ ≤ 2 ^ m + 2 ^ m := by linarith [Nat.one_le_pow m 2 (by norm_num)]
          _ = 2 ^ (m + 1) := by ring
    calc 2 * (k + 1) ≤ 2 * 2 ^ k := by linarith
      _ = 2 ^ (k + 1) := by ring
  -- Term bound: 1/D^{2^{k+1}} ≤ r^{k+1} = (1/D²)^{k+1}
  have hterm_bound : ∀ k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1)) ≤ r ^ (k + 1) := by
    intro k
    calc (1 : ℝ) / D ^ (2 ^ (k + 1))
        ≤ 1 / D ^ (2 * (k + 1)) :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_right hD_ge1 (key_arith k))
      _ = r ^ (k + 1) := by
            unfold_let r; rw [div_pow, one_pow, ← pow_mul]
  -- Summability
  have hTsumm : Summable (fun k : ℕ => r ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr_nn hr_lt1)
  have hTsumm' : Summable (fun k : ℕ => (1 : ℝ) / D ^ (2 ^ (k + 1))) :=
    hTsumm.of_nonneg_of_le (fun k => by positivity) hterm_bound
  -- Geometric series: ∑ r^{k+1} = r/(1-r) = 1/(D²-1)
  have hgeo : ∑' k : ℕ, r ^ (k + 1) = 1 / (D ^ 2 - 1) := by
    rw [show (fun k : ℕ => r ^ (k + 1)) = (fun k => r * r ^ k) from funext (fun k => by ring)]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nn hr_lt1]
    unfold_let r
    have hD2_ne : D ^ 2 ≠ 0 := by positivity
    have h1r_pos : (0 : ℝ) < 1 - 1 / D ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]; nlinarith
    field_simp [hD2_ne, h1r_pos.ne']
    ring
  -- Rewrite tsum in goal using hterm, then bound
  rw [show (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1))) =
          (fun k => 1 / D ^ (2 ^ (k + 1))) from funext hterm]
  have hT_le : ∑' k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1)) ≤ 1 / (D ^ 2 - 1) := by
    rw [← hgeo]; exact tsum_le_tsum hterm_bound hTsumm' hTsumm
  calc D * ∑' k : ℕ, (1 : ℝ) / D ^ (2 ^ (k + 1))
      ≤ D * (1 / (D ^ 2 - 1)) := mul_le_mul_of_nonneg_left hT_le hD_pos.le
    _ = D / (D ^ 2 - 1) := by ring
    _ < 1 / (D - 1) := by
          rw [div_lt_div_iff hD2_pos hD1_pos]; nlinarith

-- Sum splitting: ∑' n, f n = (∑ n in range N, f n) + f N + ∑' n, f (n + N + 1).
-- This is a standard Mathlib result (tsum_eq_zero_add, sum_add_tsum_compl, etc.).
theorem tsum_split_at (f : ℕ → ℝ) (hf : Summable f) (N : ℕ) :
    ∑' n, f n = (∑ n ∈ Finset.range N, f n) + f N + ∑' n, f (n + N + 1) := by
  -- hshift: ∑' n, f (n + k) = f k + ∑' n, f (n + k + 1)
  have hshift : ∀ k, ∑' n, f (n + k) = f k + ∑' n, f (n + k + 1) := fun k => by
    have h := tsum_eq_zero_add ((summable_nat_add_iff k).mpr hf)
    simp only [zero_add] at h
    rw [h]
    congr 1
    apply tsum_congr
    intro n; ring
  -- hsplit: ∑' n, f n = ∑ n < k, f n + ∑' n, f (n + k)
  have hsplit : ∀ k, ∑' n, f n = ∑ n ∈ Finset.range k, f n + ∑' n, f (n + k) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, hshift k, ← add_assoc]
      congr 1
      apply tsum_congr
      intro n; ring
  linarith [hsplit N, hshift N]

end Erdos263Aristotle
