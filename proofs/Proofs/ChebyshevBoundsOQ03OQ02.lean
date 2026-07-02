import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-
# Chebyshev bounds OQ-03 → OQ-02: the prime-power correction is `O(√x)`

The parent entry (`chebyshev-bounds-oq-03`) shows the second Chebyshev function
`ψ(x) = Σ_{pᵏ ≤ x} log p` is asymptotically equivalent to the first,
`θ(x) = Σ_{p ≤ x} log p`, using Mathlib's estimate

  `|ψ(x) − θ(x)| ≤ 2·√x·log x`   (`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).

That bound carries a spurious `log x` factor; indeed Mathlib annotates the lemma with
"*a more careful argument could remove the `log x` in the following with a worse constant.*"
This file carries out that careful argument, answering the parent's second open question:

  **`ψ(x) − θ(x) = O(√x)`**   (no `log` factor).

## Proof architecture (elementary prime-power count)

Mathlib's `Chebyshev.psi_eq_theta_add_sum_theta` gives, for `x ≥ 2`,

  `ψ(x) − θ(x) = Σ_{n = 2}^{K} θ(x^{1/n})`,     `K = ⌊log x / log 2⌋`.

The naive bound `θ(x^{1/n}) ≤ log 4 · x^{1/n} ≤ log 4 · √x` for every `n ≥ 2`, summed over
the `≈ log x / log 2` terms, reproduces the `√x·log x` estimate.  The `log` factor is removed
by splitting off the single dominant term `n = 2`:

* **`n = 2`.**  `θ(√x) ≤ log 4 · √x`  (`Chebyshev.theta_le_log4_mul_x`).
* **`n ≥ 3`.**  Here `x^{1/n} ≤ x^{1/3}`, so each term is `≤ log 4 · x^{1/3}`, and there are
  at most `K ≤ log x / log 2` of them.  Their total is
  `≤ (log 4 / log 2) · (log x · x^{1/3})`.  The elementary decay bound
  `log x ≤ 6 · x^{1/6}`  (`Real.log_le_rpow_div` at `ε = 1/6`) turns `log x · x^{1/3}` into
  `6 · x^{1/2} = 6·√x`, and `log 4 / log 2 = 2`, so the whole tail is `≤ 12·√x`.

Adding the two pieces gives `ψ(x) − θ(x) ≤ (log 4 + 12)·√x`, an explicit `O(√x)` bound.
The `log`-free error term is exactly what distinguishes the second Chebyshev function's
prime-power correction from the trivial `√x·log x` estimate.

## Main results

* `psi_sub_theta_le_const_mul_sqrt` : `ψ(x) − θ(x) ≤ (log 4 + 12)·√x` for `x ≥ 2`.
* `psi_sub_theta_isBigO_sqrt` : `(ψ − θ) =O[atTop] √`  — the `O(√x)` statement itself.
-/

namespace ChebyshevBoundsOQ03OQ02

open Filter Asymptotics Finset
open Chebyshev
open scoped Topology

/-- Elementary decay bound `log x ≤ 6·x^{1/6}` for `x > 0`, the special case of
`Real.log_le_rpow_div` at exponent `1/6` that turns `log x · x^{1/3}` into `6·√x`. -/
theorem log_le_six_mul_rpow {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 6 * x ^ ((1 : ℝ) / 6) := by
  have h := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 6)
  rw [div_div_eq_mul_div, one_mul] at h  -- x ^ (1/6) / (1/6)
  simpa using h

/-- `log x · x^{1/3} ≤ 6·√x` for `x > 0`: the key `log`-eating step. -/
theorem logx_mul_rpow_third_le {x : ℝ} (hx : 0 < x) :
    Real.log x * x ^ ((1 : ℝ) / 3) ≤ 6 * Real.sqrt x := by
  have h13 : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx.le _
  calc
    Real.log x * x ^ ((1 : ℝ) / 3)
        ≤ (6 * x ^ ((1 : ℝ) / 6)) * x ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right (log_le_six_mul_rpow hx) h13
    _ = 6 * (x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 3)) := by ring
    _ = 6 * x ^ ((1 : ℝ) / 6 + (1 : ℝ) / 3) := by rw [← Real.rpow_add hx]
    _ = 6 * x ^ ((1 : ℝ) / 2) := by norm_num
    _ = 6 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]

/-- **The prime-power correction is `O(√x)` with an explicit constant.**
For `x ≥ 2`, `ψ(x) − θ(x) ≤ (log 4 + 12)·√x`. -/
theorem psi_sub_theta_le_const_mul_sqrt {x : ℝ} (hx : 2 ≤ x) :
    ψ x - θ x ≤ (Real.log 4 + 12) * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set K : ℕ := ⌊Real.log x / Real.log 2⌋₊ with hKdef
  -- ψ x - θ x = Σ_{n = 2}^{K} θ (x ^ (1/n))
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  rcases Nat.lt_or_ge K 2 with hK | hK
  · -- K < 2 : the sum is empty
    rw [Finset.Icc_eq_empty (by omega : ¬ 2 ≤ K), Finset.sum_empty]
    positivity
  · -- 2 ≤ K : peel off the dominant n = 2 term
    have h2mem : (2 : ℕ) ∈ Finset.Icc 2 K := by rw [Finset.mem_Icc]; omega
    rw [← Finset.add_sum_erase _ (fun n => θ (x ^ ((1 : ℝ) / (n : ℝ)))) h2mem,
      Finset.Icc_erase_left]
    -- goal: θ (x ^ (1/2)) + Σ_{n ∈ Ioc 2 K} θ (x ^ (1/n)) ≤ (log 4 + 12) √x
    -- bound the n = 2 term: θ(√x) ≤ log 4 · √x
    have hn2 : θ (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ≤ Real.log 4 * Real.sqrt x := by
      have e2 : x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]; norm_num
      rw [e2]
      exact theta_le_log4_mul_x hsx
    -- bound the tail n ≥ 3 by 12·√x
    have htail : ∑ n ∈ Finset.Ioc 2 K, θ (x ^ ((1 : ℝ) / (n : ℝ))) ≤ 12 * Real.sqrt x := by
      -- each term ≤ log 4 · x^{1/3}
      have hterm : ∀ n ∈ Finset.Ioc 2 K,
          θ (x ^ ((1 : ℝ) / (n : ℝ))) ≤ Real.log 4 * x ^ ((1 : ℝ) / 3) := by
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
        calc θ (x ^ ((1 : ℝ) / (n : ℝ)))
            ≤ Real.log 4 * x ^ ((1 : ℝ) / (n : ℝ)) :=
              theta_le_log4_mul_x (Real.rpow_nonneg hx0.le _)
          _ ≤ Real.log 4 * x ^ ((1 : ℝ) / 3) := by
              apply mul_le_mul_of_nonneg_left _ hlog4
              apply Real.rpow_le_rpow_of_exponent_le hx1
              apply one_div_le_one_div_of_le (by norm_num) hn3
      calc ∑ n ∈ Finset.Ioc 2 K, θ (x ^ ((1 : ℝ) / (n : ℝ)))
          ≤ ∑ _n ∈ Finset.Ioc 2 K, Real.log 4 * x ^ ((1 : ℝ) / 3) :=
            Finset.sum_le_sum hterm
        _ = (K - 2 : ℕ) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by
            rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        _ ≤ (Real.log x / Real.log 2) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_right _
              (mul_nonneg hlog4 (Real.rpow_nonneg hx0.le _))
            -- (K - 2 : ℕ) ≤ K ≤ log x / log 2
            have hKle : (K : ℝ) ≤ Real.log x / Real.log 2 :=
              Nat.floor_le (by positivity)
            have : ((K - 2 : ℕ) : ℝ) ≤ (K : ℝ) := by
              exact_mod_cast Nat.sub_le K 2
            linarith
        _ = (Real.log 4 / Real.log 2) * (Real.log x * x ^ ((1 : ℝ) / 3)) := by ring
        _ = 2 * (Real.log x * x ^ ((1 : ℝ) / 3)) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            have hl2 : Real.log 2 ≠ 0 := by
              have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
              linarith
            field_simp
            ring
        _ ≤ 2 * (6 * Real.sqrt x) := by
            apply mul_le_mul_of_nonneg_left (logx_mul_rpow_third_le hx0) (by norm_num)
        _ = 12 * Real.sqrt x := by ring
    -- combine the two pieces
    calc θ (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) + ∑ n ∈ Finset.Ioc 2 K, θ (x ^ ((1 : ℝ) / (n : ℝ)))
        ≤ Real.log 4 * Real.sqrt x + 12 * Real.sqrt x := by
          exact add_le_add hn2 htail
      _ = (Real.log 4 + 12) * Real.sqrt x := by ring

/-- **`ψ − θ = O(√x)`.**  The prime-power correction to the second Chebyshev function is
`O(√x)` — no `log` factor, sharpening Mathlib's `|ψ − θ| ≤ 2√x·log x`. -/
theorem psi_sub_theta_isBigO_sqrt :
    (fun x => ψ x - θ x) =O[atTop] fun x => Real.sqrt x := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 12, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hnn : 0 ≤ ψ x - θ x := by have := theta_le_psi x; linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  exact psi_sub_theta_le_const_mul_sqrt hx

end ChebyshevBoundsOQ03OQ02
