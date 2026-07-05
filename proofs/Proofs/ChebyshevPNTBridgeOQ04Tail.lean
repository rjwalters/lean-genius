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

  ## What this file supplies (all verified, no axioms, no `sorry`)

  - `log_le_two_mul_sqrt`   : `log x ≤ 2√x` (the majorant device).
  - `summable_log_div_sq`   : `Σ_n (log n)/n²` converges (the full-integer engine).
  - `summable_primes_log_div_sq` : `Σ_{p prime} (log p)/p²` converges — the exact
    prime-indexed **majorant** that dominates the tail after reindexing.
  - `geom_tail_le_two_div_sq` : the per-prime geometric collapse bound
    `(log p)/(p(p−1)) ≤ 2·(log p)/p²`, which is what summing the `k`-series for a
    fixed prime `p` produces before comparison to the majorant.

  The only step left to close the lower half of Mertens I is the `Finset`
  reindexing `R(N) = Σ_{p^k≤N,k≥2}(log p)/p^k ≤ Σ_{p≤N} (log p)/(p(p−1))`
  (grouping the tail by base prime and summing over `k`), after which
  `geom_tail_le_two_div_sq` and `summable_primes_log_div_sq` give the uniform
  bound `R(N) ≤ 2·Σ_p (log p)/p² < ∞`.
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

/-- **The prime majorant is summable.** `Σ_{p prime} (log p)/p²` converges.

    This is the target majorant for the prime-power tail `R(N)`: after regrouping
    `R(N) = Σ_{p^k ≤ N, k ≥ 2} (log p)/p^k` by base prime and summing the geometric
    series in `k`, one obtains `R(N) ≤ Σ_p (log p)/(p(p−1)) ≤ 2·Σ_p (log p)/p²`, so
    the finiteness of `R(N)` reduces to *this* prime-indexed series. It follows from
    the full-integer engine `summable_log_div_sq` by restriction along the injective
    coercion `Nat.Primes ↪ ℕ`. -/
theorem summable_primes_log_div_sq :
    Summable (fun p : Nat.Primes => Real.log (p : ℕ) / ((p : ℕ) : ℝ) ^ 2) := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
    fun a b hab => Subtype.ext hab
  exact summable_log_div_sq.comp_injective hinj

/-- **Geometric per-prime tail bound (real form).** For a real base `x ≥ 2`, the
    higher-power tail `Σ_{k ≥ 2} (log x)/x^k = (log x)/(x(x−1))` is bounded by
    `2·(log x)/x²`.

    This is the exact-in-`k` summation that turns the double prime-power sum into
    the prime-indexed majorant `summable_primes_log_div_sq`: for a fixed prime `p`,
    `Σ_{k ≥ 2} (log p)/p^k = (log p)/(p(p−1))`, and `p/(p−1) ≤ 2` for `p ≥ 2`. -/
theorem geom_tail_le_two_div_sq {x : ℝ} (hx : 2 ≤ x) :
    Real.log x / (x * (x - 1)) ≤ 2 * (Real.log x / x ^ 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x - 1 := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- Rewrite the right side as a single fraction and cross-multiply, using only
  -- the `div_le_iff₀` / `le_div_iff₀` primitives.
  rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < x * (x - 1)),
    div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
  -- goal: log x · x² ≤ 2·log x · (x·(x−1)); difference is log x · x · (x−2) ≥ 0
  nlinarith [mul_nonneg (mul_nonneg hlog hx0.le) (by linarith : (0 : ℝ) ≤ x - 2),
    hlog, hx0]

end ChebyshevPNTBridgeOQ04Tail

-- Axiom audit: all results depend only on the ordinary foundational axioms
-- (propext / Classical.choice / Quot.sound); no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms ChebyshevPNTBridgeOQ04Tail.log_le_two_mul_sqrt
#print axioms ChebyshevPNTBridgeOQ04Tail.summable_log_div_sq
#print axioms ChebyshevPNTBridgeOQ04Tail.summable_primes_log_div_sq
#print axioms ChebyshevPNTBridgeOQ04Tail.geom_tail_le_two_div_sq
