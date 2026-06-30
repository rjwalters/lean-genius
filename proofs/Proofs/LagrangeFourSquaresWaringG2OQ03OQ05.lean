import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ03OQ04

/-!
# The natural density of the non-three-square integers is `1/6`

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-05`)**, a companion to the
parent `oq-03` entry *"Legendre's three-square theorem — the if direction"* and a direct
sequel to `oq-03-oq-04` (the 2-adic normal form of the excluded family).

By Legendre's three-square theorem the integers that are **not** sums of three squares are
exactly the *excluded family*

  `E = { 4^a (8b+7) : a, b ≥ 0 }`.

These are precisely the integers that require the full **four** squares in Lagrange's
theorem, i.e. the extremal numbers for Waring's problem `g(2) = 4`.  A natural quantitative
question — not addressed anywhere in the gallery — is: *how rare are they?*

This file answers it: the excluded family has **natural density `1/6`**.

## What is new here

* **A 4-descent counting recursion** (`excludedCount_rec`):
  `excludedCount N = N / 8 + excludedCount ⌈N/4⌉`,
  where `excludedCount N = #{ n < N : n ∈ E }`.  An excluded number is either odd and
  `≡ 7 (mod 8)` (there are exactly `⌊N/8⌋` of those below `N`) or divisible by `4` with
  quotient again excluded — a clean self-similar decomposition.

* **An explicit logarithmic error bound** (`excludedCount_error_bound`):
  `|6·excludedCount N − N| ≤ 6·(log₂ N + 1)`, proved by strong induction directly from the
  recursion.  The constant `1/6` is pinned by summing the geometric series implicit in the
  recursion, but the proof never forms an infinite sum — the bound is a single inductive
  invariant.

* **The density theorem** (`excludedCount_density`):
  `excludedCount N / N → 1/6`  as `N → ∞`.
  Equivalently, asymptotically one integer in six is *not* a sum of three squares.

The only nontrivial number-theoretic inputs are the elementary `2`-adic facts about `E`
(re-derived here from the `oq-03-oq-04` definition); the rest is finite combinatorics plus a
standard `log N / N → 0` squeeze.  All proofs are axiom-free.
-/

open Finset Filter
open scoped Topology
open LagrangeFourSquaresWaringG2OQ03OQ04

namespace LagrangeFourSquaresWaringG2OQ03OQ05

/-! ## Elementary 2-adic structure of the excluded family

We reuse `IsExcludedForm` and its computable `Decidable` instance from `oq-03-oq-04`, and
record the two descent facts needed for the counting recursion. -/

/-- A number `≡ 7 (mod 8)` is excluded (take `a = 0`, `b = n / 8`). -/
theorem mod8_seven_excluded {n : ℕ} (h : n % 8 = 7) : IsExcludedForm n :=
  ⟨0, n / 8, by rw [pow_zero, one_mul]; omega⟩

/-- **The multiply-by-4 descent.** `4·k` is excluded iff `k` is: the factor `4` only shifts
the exponent `a` in `4^a(8b+7)`. -/
theorem four_mul_excluded_iff (k : ℕ) : IsExcludedForm (4 * k) ↔ IsExcludedForm k := by
  constructor
  · rintro ⟨a, b, h⟩
    cases a with
    | zero => rw [pow_zero, one_mul] at h; omega
    | succ a' =>
      refine ⟨a', b, ?_⟩
      have h4 : 4 * k = 4 * (4 ^ a' * (8 * b + 7)) := by rw [h, pow_succ]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  · rintro ⟨a, b, rfl⟩
    exact ⟨a + 1, b, by rw [pow_succ]; ring⟩

/-- For a number not divisible by `4`, being excluded is the same as being `≡ 7 (mod 8)`. -/
theorem excluded_not_dvd_four_iff {n : ℕ} (h : ¬ 4 ∣ n) :
    IsExcludedForm n ↔ n % 8 = 7 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    cases a with
    | zero => rw [pow_zero, one_mul]; omega
    | succ a' =>
      exact absurd ⟨4 ^ a' * (8 * b + 7), by rw [pow_succ]; ring⟩ h
  · intro hm; exact mod8_seven_excluded hm

/-! ## The counting function and its 4-descent recursion -/

/-- `excludedCount N` counts the excluded integers below `N` — the size of the exceptional
set for the three-square theorem in `[0, N)`. -/
def excludedCount (N : ℕ) : ℕ := ((range N).filter IsExcludedForm).card

/-- No excluded number is `< 7`, so the count vanishes for small `N`. -/
theorem excludedCount_zero_of_le {N : ℕ} (h : N ≤ 7) : excludedCount N = 0 := by
  rw [excludedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn he
  rw [Finset.mem_range] at hn
  have := excludedForm_ge_seven he
  omega

/-- There are exactly `⌊N/8⌋` numbers `≡ 7 (mod 8)` below `N`. -/
theorem card_mod8_seven (N : ℕ) :
    ((range N).filter (fun n => n % 8 = 7)).card = N / 8 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hk : k % 8 = 7
    · rw [if_pos hk, Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [if_neg hk, ih]; omega

/-- The not-divisible-by-`4` part of the excluded set below `N` is exactly the `≡ 7 (mod 8)`
part of `[0, N)`. -/
theorem filter_notdvd_eq_mod8 (N : ℕ) :
    ((range N).filter IsExcludedForm).filter (fun n => ¬ 4 ∣ n)
      = (range N).filter (fun n => n % 8 = 7) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hlt, he⟩, h4⟩
    exact ⟨hlt, (excluded_not_dvd_four_iff h4).mp he⟩
  · rintro ⟨hlt, hm⟩
    exact ⟨⟨hlt, mod8_seven_excluded hm⟩, by omega⟩

/-- The divisible-by-`4` part of the excluded set below `N` is in bijection (via `n ↦ n/4`)
with the excluded set below `⌈N/4⌉ = (N+3)/4`. -/
theorem excludedCount_dvd_part (N : ℕ) :
    (((range N).filter IsExcludedForm).filter (fun n => 4 ∣ n)).card
      = excludedCount ((N + 3) / 4) := by
  rw [excludedCount]
  refine Finset.card_bij' (fun n _ => n / 4) (fun k _ => 4 * k) ?hi ?hj ?linv ?rinv
  case hi =>
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨⟨hlt, he⟩, h4⟩ := hn
    refine ⟨by omega, ?_⟩
    have hnn : 4 * (n / 4) = n := Nat.mul_div_cancel' h4
    rw [← hnn] at he
    exact (four_mul_excluded_iff (n / 4)).mp he
  case hj =>
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hlt, he⟩ := hk
    exact ⟨⟨by omega, (four_mul_excluded_iff k).mpr he⟩, dvd_mul_right 4 k⟩
  case linv =>
    intro n hn
    rw [Finset.mem_filter] at hn
    have h4 := hn.2
    show 4 * (n / 4) = n
    omega
  case rinv =>
    intro k _hk
    show 4 * k / 4 = k
    omega

/-- **The 4-descent counting recursion.** -/
theorem excludedCount_rec (N : ℕ) :
    excludedCount N = N / 8 + excludedCount ((N + 3) / 4) := by
  have hsplit :
      (((range N).filter IsExcludedForm).filter (fun n => 4 ∣ n)).card
        + (((range N).filter IsExcludedForm).filter (fun n => ¬ 4 ∣ n)).card
        = ((range N).filter IsExcludedForm).card :=
    Finset.filter_card_add_filter_neg_card_eq_card (fun n => 4 ∣ n)
  rw [filter_notdvd_eq_mod8, card_mod8_seven, excludedCount_dvd_part] at hsplit
  rw [excludedCount]
  omega

/-! ## The logarithmic error bound -/

/-- **Explicit error bound.** `|6·excludedCount N − N| ≤ 6·(log₂ N + 1)`.  Proved by strong
induction: each descent step changes the error by a bounded amount, and the number of steps
is `log₂`-controlled. -/
theorem excludedCount_error_bound (N : ℕ) :
    |6 * (excludedCount N : ℤ) - (N : ℤ)| ≤ 6 * ((Nat.log 2 N : ℤ) + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 4 with hN | hN
    · have h0 : excludedCount N = 0 := excludedCount_zero_of_le (by omega)
      rw [h0, abs_le]
      refine ⟨by push_cast; omega, by push_cast; omega⟩
    · set M := (N + 3) / 4 with hM
      have hMlt : M < N := by omega
      have hM1 : 1 ≤ M := by omega
      have hrec : excludedCount N = N / 8 + excludedCount M := excludedCount_rec N
      have ihM := ih M hMlt
      -- the per-step error `δ = 6*(N/8) + M - N` is bounded in absolute value by 6
      have hδ : |6 * ((N / 8 : ℕ) : ℤ) + (M : ℤ) - (N : ℤ)| ≤ 6 := by
        have e8 : 8 * (N / 8) + N % 8 = N := Nat.div_add_mod N 8
        have e8' : N % 8 < 8 := Nat.mod_lt N (by norm_num)
        have e4 : 4 * M + (N + 3) % 4 = N + 3 := by rw [hM]; exact Nat.div_add_mod (N + 3) 4
        have e4' : (N + 3) % 4 < 4 := Nat.mod_lt (N + 3) (by norm_num)
        rw [abs_le]; refine ⟨by push_cast; omega, by push_cast; omega⟩
      -- the descent depth decreases the log
      have hlog : Nat.log 2 M + 1 ≤ Nat.log 2 N := by
        have hMle : M ≤ N / 2 := by omega
        have h1 : Nat.log 2 M ≤ Nat.log 2 (N / 2) := Nat.log_mono_right hMle
        have h2 : Nat.log 2 (N / 2) = Nat.log 2 N - 1 := Nat.log_div_base 2 N
        have h3 : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) (by omega)
        omega
      have hcombine : 6 * (excludedCount N : ℤ) - (N : ℤ)
          = (6 * (excludedCount M : ℤ) - (M : ℤ))
            + (6 * ((N / 8 : ℕ) : ℤ) + (M : ℤ) - (N : ℤ)) := by
        rw [hrec]; push_cast; ring
      rw [hcombine]
      refine le_trans (abs_add_le _ _) ?_
      refine le_trans (add_le_add ihM hδ) ?_
      have : (Nat.log 2 M : ℤ) + 1 ≤ (Nat.log 2 N : ℤ) := by exact_mod_cast hlog
      linarith

/-! ## The density theorem -/

/-- `(Nat.log 2 N : ℝ) ≤ log N / log 2` for `N ≥ 1`. -/
private theorem natLog2_le_realLog (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    have h := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    calc (2 : ℝ) ^ (Nat.log 2 N) = ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) := by exact_mod_cast h
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log ((2 : ℝ) ^ (Nat.log 2 N)) ≤ Real.log N :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at h1
  rw [le_div_iff₀ hlog2pos]
  linarith

/-- `(log₂ N + 1) / N → 0`. -/
private theorem tendsto_logBound_zero :
    Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hN : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    hlogdiv.comp tendsto_natCast_atTop_atTop
  have hUpper :
      Tendsto (fun N : ℕ => (1 / Real.log 2) * (Real.log (N : ℝ) / (N : ℝ)) + 1 / (N : ℝ))
        atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / Real.log 2) * (Real.log (N : ℝ) / (N : ℝ)))
        atTop (𝓝 0) := by simpa using hN.const_mul (1 / Real.log 2)
    have h2 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hUpper
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hb : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := natLog2_le_realLog N hN1
    have key : (Nat.log 2 N : ℝ) / N ≤ (1 / Real.log 2) * (Real.log N / N) := by
      rw [show (1 / Real.log 2) * (Real.log N / N) = (Real.log N / Real.log 2) / N from by ring]
      gcongr
    rw [add_div]
    linarith

/-- **The natural density of the non-three-square integers is `1/6`.**

`excludedCount N / N → 1/6`: asymptotically, exactly one integer in six fails to be a sum of
three squares (equivalently, requires all four squares of Lagrange's theorem). -/
theorem excludedCount_density :
    Tendsto (fun N : ℕ => (excludedCount N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / 6)) := by
  -- It suffices that `excludedCount N / N − 1/6 → 0`.
  have hd0 : Tendsto (fun N : ℕ => (excludedCount N : ℝ) / N - 1 / 6) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      tendsto_logBound_zero
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
    -- cast the integer error bound to ℝ
    have herrZ := excludedCount_error_bound N
    have herr : |6 * (excludedCount N : ℝ) - (N : ℝ)| ≤ 6 * ((Nat.log 2 N : ℝ) + 1) := by
      rw [abs_le] at herrZ ⊢
      constructor
      · exact_mod_cast herrZ.1
      · exact_mod_cast herrZ.2
    -- rewrite the deviation as a single fraction
    have hd : (excludedCount N : ℝ) / N - 1 / 6 = (6 * (excludedCount N : ℝ) - N) / (6 * N) := by
      field_simp
    rw [Real.norm_eq_abs, hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 6 * N)]
    rw [div_le_div_iff₀ (by positivity) hNR]
    -- |6 E - N| * N ≤ (log₂ N + 1) * (6 N)
    have h6N : (0 : ℝ) ≤ N := le_of_lt hNR
    nlinarith [herr, h6N, hNR]
  have hfin : Tendsto (fun N : ℕ => ((excludedCount N : ℝ) / N - 1 / 6) + 1 / 6) atTop
      (𝓝 (0 + 1 / 6)) := hd0.add tendsto_const_nhds
  rw [zero_add] at hfin
  exact hfin.congr (fun N => by ring)

/-! ## Sanity checks -/

/-- `excludedCount 8 = 1`: only `7` is excluded below `8` (`8 = 8/8 + excludedCount 2`). -/
example : excludedCount 8 = 1 := by
  rw [excludedCount_rec, excludedCount_zero_of_le (by norm_num : (8 + 3) / 4 ≤ 7)]

/-- `excludedCount 16 = 2`: `7` and `15` (`16/8 + excludedCount 4 = 2 + 0`). -/
example : excludedCount 16 = 2 := by
  rw [excludedCount_rec, excludedCount_zero_of_le (by norm_num : (16 + 3) / 4 ≤ 7)]

/-- `excludedCount 32 = 5`: `7, 15, 23, 28, 31` (`32/8 + excludedCount 8 = 4 + 1`). -/
example : excludedCount 32 = 5 := by
  have h8 : excludedCount 8 = 1 := by
    rw [excludedCount_rec, excludedCount_zero_of_le (by norm_num : (8 + 3) / 4 ≤ 7)]
  rw [excludedCount_rec, show (32 + 3) / 4 = 8 from rfl, h8]

/-- The recursion checks out at `N = 32`: `5 = 32/8 + excludedCount 8 = 4 + 1`. -/
example : excludedCount 32 = 32 / 8 + excludedCount ((32 + 3) / 4) := excludedCount_rec 32

end LagrangeFourSquaresWaringG2OQ03OQ05
