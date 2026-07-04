/-
  Chebyshev–PNT Bridge OQ-04 — the convergence engine for the prime-power tail.

  Self-contained: imports only Mathlib (portable to Aristotle `prove_file`).

  ## Context

  The companion file `ChebyshevPNTBridgeOQ04.lean` proves Mertens' first theorem
  in its von Mangoldt (Λ) weighted form and the exact prime / prime-power split

    `Σ_{d≤N} Λ(d)/d = Σ_{p≤N} (log p)/p + R(N)`,

  with `R(N) = Σ_{d≤N, ¬prime} Λ(d)/d ≥ 0` the prime-power tail.  The *upper*
  half of Mertens' first theorem for the honest prime sum follows from tail
  nonnegativity (`primeLogRecip_le`).  The matching **lower** bound is the sole
  remaining analytic step: a uniform bound `R(N) = O(1)`.

  Regrouping the tail by base prime,

    `R(N) = Σ_{p^k ≤ N, k ≥ 2} (log p)/p^k
          ≤ Σ_{p} (log p) Σ_{k ≥ 2} p^{-k}
          = Σ_{p} (log p)/(p(p−1))
          ≤ Σ_{n ≥ 2} (log n)/(n(n−1))  < ∞`,

  the whole obstruction collapses to the **convergence of `Σ (log n)/n²`-type
  series**.  Mathlib has `summable_one_div_nat_rpow` (the `p`-series test) but no
  log-weighted companion.  This file supplies exactly that missing engine:

    `summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ)^2)`,

  by the clean majorant `log x ≤ 2√x` (hence `log n / n² ≤ 2·n^{-3/2}`), reducing
  to the convergent `3/2`-series.  No axioms, no `sorry`.

  With this in hand the remaining work for the lower half of Mertens I is purely
  the prime-power *reindexing* (`R(N) ≤ 2·Σ_{p} (log p)/p²`), a `Finset`
  bookkeeping step over `{p^k : k ≥ 2}`, feeding this summability as the majorant.
-/
import Mathlib

open scoped BigOperators

namespace ChebyshevPNTBridgeOQ04Tail

/-- **Log/√ majorant.** For every `x > 0`, `log x ≤ 2·√x`.

    Proof: `log x = log ((√x)²) = 2·log √x ≤ 2·(√x − 1) ≤ 2·√x`, using
    `Real.log_le_sub_one_of_pos` on `√x > 0`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have : Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [Real.sq_sqrt hx.le]
    rw [this, Real.log_pow]; push_cast; ring
  rw [h2]; nlinarith [h1, hs]

/-- **The convergence engine.** `Σ_{n} (log n)/n²` is summable.

    Termwise `0 ≤ log n / n² ≤ 2·n^{-3/2}` (from `log n ≤ 2√n`), and the majorant
    `Σ 2·n^{-3/2}` converges by the `p`-series test (`p = 3/2 > 1`). -/
theorem summable_log_div_sq :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  -- Majorant `n ↦ 2 · (1 / n^{3/2})` is summable.
  have hmaj : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · -- nonnegativity of `log n / n²`
    exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  · -- termwise bound `log n / n² ≤ 2·(1 / n^{3/2})`
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      -- reduce to `log n ≤ 2·(1/n^{3/2})·n² = 2·√n`
      have hkey : 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) * (n : ℝ) ^ 2
          = 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, one_div,
          show ((n : ℝ) ^ 2) = (n : ℝ) ^ (2 : ℝ) from by
            rw [← Real.rpow_natCast]; norm_num,
          ← Real.rpow_neg hx.le, mul_assoc, ← Real.rpow_add hx]
        norm_num
      rw [hkey]; exact log_le_two_mul_sqrt hx

end ChebyshevPNTBridgeOQ04Tail

-- Axiom audit: both results depend only on the ordinary foundational axioms
-- (propext / Classical.choice / Quot.sound); no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms ChebyshevPNTBridgeOQ04Tail.log_le_two_mul_sqrt
#print axioms ChebyshevPNTBridgeOQ04Tail.summable_log_div_sq
