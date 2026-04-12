/-
Erdős Problem #100 — Open Question: Kanold's Bound from Guth-Katz

**Question**: Is Kanold's bound (diam ≥ cn^{3/4}) provable from the
Guth-Katz derived bound (diam ≥ cn/log n)?

**Answer**: YES. Since n/log n dominates n^{3/4} asymptotically,
the Guth-Katz bound implies Kanold's bound as a corollary.

**Proof idea**: From log x ≤ x - 1 (applied to x = n^{1/4}), we get
log n = 4·log(n^{1/4}) ≤ 4·n^{1/4}. Thus:
  cn/log n ≥ cn/(4·n^{1/4}) = (c/4)·n^{3/4}

Status: PROVED (from axiomatized Guth-Katz)
Reference: https://erdosproblems.com/100
-/

import Proofs.Erdos100Problem

open Erdos100 Filter

namespace Erdos100OQ02OQ02

/-
## Key Lemma: log n ≤ 4·n^{1/4}

From `log x ≤ x - 1` for x > 0 (applied with x = n^{1/4}):
  log(n^{1/4}) ≤ n^{1/4} - 1 ≤ n^{1/4}
  log n = 4·log(n^{1/4}) ≤ 4·n^{1/4}
-/

/--
For n ≥ 1 (natural number), log n ≤ 4·n^{1/4}.

Proof: `log n = 4·log(n^{1/4})` via `log(x^p) = p·log x`,
and `log(n^{1/4}) ≤ n^{1/4}` from the elementary bound `log x ≤ x - 1`.
-/
theorem log_le_four_rpow_quarter {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  -- n^{1/4} ≥ 1 since n ≥ 1
  have hq_ge1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  -- log(n^{1/4}) = (1/4)·log n
  have hlog_eq : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) = (1 : ℝ) / 4 * Real.log (n : ℝ) :=
    Real.log_rpow hn_pos _
  -- log(n^{1/4}) ≤ n^{1/4} (from log x ≤ x - 1 ≤ x for x > 0)
  have hlog_le : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  -- Combine: log n = 4·log(n^{1/4}) ≤ 4·n^{1/4}
  linarith

/--
**Kanold's Bound from Guth-Katz.**

For n-point integer distance sets in ℝ², diam ≥ c·n^{3/4}, proved as a
corollary of the Guth-Katz derived bound diam ≥ c·n/log n.

The constant is c_{GK}/4 where c_{GK} is the Guth-Katz constant.
This eliminates the need for Kanold's bound as a separate axiom:
it follows from the stronger Guth-Katz result.

**Key step**: log n ≤ 4·n^{1/4} implies n/log n ≥ n/(4·n^{1/4}),
and n^{3/4}·n^{1/4} = n gives n/(4·n^{1/4}) = n^{3/4}/4.
-/
theorem kanold_bound_from_gk :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
        S.card = n → hasIntegerDistances S →
        c * (n : ℝ) ^ ((3 : ℝ) / 4) ≤ diam S := by
  obtain ⟨c_gk, hc_pos, hgk⟩ := diam_ge_n_over_log_n
  refine ⟨c_gk / 4, by linarith, ?_⟩
  filter_upwards [hgk, Filter.eventually_ge_atTop 3] with n hgk_n hn3
  intro S hcard hint
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  -- Key: log n ≤ 4·n^{1/4}
  have hlog_le : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
    log_le_four_rpow_quarter (by omega)
  -- n^{3/4}·n^{1/4} = n (rpow addition)
  have hrpow_mul : (n : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = (n : ℝ) := by
    rw [← Real.rpow_add hn_pos,
        show (3 : ℝ) / 4 + (1 : ℝ) / 4 = 1 from by norm_num,
        Real.rpow_one]
  -- Core bound: n^{3/4}·log n ≤ 4n
  have key : (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log (n : ℝ) ≤ 4 * (n : ℝ) := by
    calc (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log (n : ℝ)
        ≤ (n : ℝ) ^ ((3 : ℝ) / 4) * (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
          apply mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = 4 * ((n : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ = 4 * (n : ℝ) := by rw [hrpow_mul]
  -- Chain: (c_gk/4)·n^{3/4} ≤ c_gk·n/log n ≤ diam S
  calc c_gk / 4 * (n : ℝ) ^ ((3 : ℝ) / 4)
      ≤ c_gk * ↑n / Real.log ↑n := by
        rw [le_div_iff hlog_pos]
        calc c_gk / 4 * (↑n) ^ ((3 : ℝ) / 4) * Real.log ↑n
            = c_gk / 4 * ((↑n) ^ ((3 : ℝ) / 4) * Real.log ↑n) := by ring
          _ ≤ c_gk / 4 * (4 * ↑n) :=
              mul_le_mul_of_nonneg_left key (by linarith)
          _ = c_gk * ↑n := by ring
    _ ≤ diam S := hgk_n S hcard hint

end Erdos100OQ02OQ02
