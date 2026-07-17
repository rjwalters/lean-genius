/-
# Alternating-Series Boole Summation — OQ-01-OQ-01, explicit remainder closed form

The parent file `AlternatingSeriesBooleSummationOQ01OQ01.lean` proves the order-`K` Boole
summation limit

  `S = ∑_{k=0}^{K-1} ((-1)^k / 2^{k+1}) · (-1)^n (Δᵏa)_n + ((-1)^K / 2^K) · T_K`
      (`boole_general_tendsto`),

where `T_K := lim_m altSum (Δᴷa) n m` is the limit of the alternating series of the `K`-th
forward differences.  Its `iterate_altSum_tendsto` shows every `T_k` exists, but only through the
**recursion** `T_{k+1} = (-1)^n (Δᵏa)_n − 2 T_k` (`T_0 = S`): each `T_k` is exhibited via the
previous one, not by a standalone formula.

This file settles the outstanding open item (`nextSteps` #2 in the problem tracker): unrolling that
recursion into an **explicit, non-recursive closed form** for the higher-difference series limit,

  `T_K = ∑_{k=0}^{K-1} (-2)^{K-1-k} · (-1)^n (Δᵏa)_n + (-2)^K · S`   (`iterate_altSum_limit_closed`),

expressing `T_K` purely through the base sum `S` and the boundary data `(Δᵏa)_n`, with no reference
to the intermediate limits.  The proof is a single induction on `K` feeding the parent's first-order
engine `fdiff_altSum_tendsto` its own inductive hypothesis; the only bookkeeping is the geometric
weight `(-2)^{K-1-k}` and the identity `(-2)^{K-k} = −2·(-2)^{K-1-k}` for `k < K`.

Consequences proved here:

* `iterate_altSum_limit_closed_of_antitone` — the same closed form unconditionally for antitone null
  sequences (convergence supplied by Mathlib's alternating-series test, via the parent's
  `altSum_tendsto_of_antitone`).
* `iterate_altSum_limit_one` — sanity check `K = 1`: `T_1 = (-1)^n a_n − 2 S`, matching
  `fdiff_altSum_tendsto`.
* `boole_general_tendsto_closed` — substituting the closed form back into `boole_general_tendsto`,
  a self-consistency identity: the two closed forms fit together to give exactly `S`.

All results are over `ℝ` and axiom-free.
-/

import Mathlib
import Proofs.AlternatingSeriesBooleSummation
import Proofs.AlternatingSeriesBooleSummationOQ01OQ01

namespace AlternatingSeriesBooleSummationOQ01OQ01ClosedForm

open AlternatingSeriesBooleSummation AlternatingSeriesBooleSummationOQ01OQ01
open Finset Filter Topology

/-! ## The explicit closed form for the higher-difference series limit -/

/-- **Explicit closed form for `T_K`.**  If `a → 0` and the base alternating series converges
(`altSum a n · → S`), then for every order `K` the alternating series of the `K`-th forward
difference converges to the explicit value

  `T_K = ∑_{k=0}^{K-1} (-2)^{K-1-k} · (-1)^n (Δᵏa)_n + (-2)^K · S`.

This unrolls the recursion `T_{k+1} = (-1)^n (Δᵏa)_n − 2 T_k` (with `T_0 = S`) of the parent's
`iterate_altSum_tendsto` into a standalone formula in the base sum `S` and the boundary data
`(Δᵏa)_n`.  Proof by induction on `K`: the successor step applies the first-order limit engine
`fdiff_altSum_tendsto` (to the null sequence `Δᴷa`, using `iterate_fdiff_tendsto_zero`) to the
inductive hypothesis, and the geometric weights recombine via `(-2)^{K-k} = −2·(-2)^{K-1-k}`. -/
theorem iterate_altSum_limit_closed {a : ℕ → ℝ} {n : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) (K : ℕ) :
    Tendsto (fun m => altSum (fdiff^[K] a) n m) atTop
      (𝓝 ((∑ k ∈ Finset.range K,
              (-2 : ℝ) ^ (K - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
          + (-2 : ℝ) ^ K * S)) := by
  induction K with
  | zero => simpa using hS
  | succ K ih =>
    -- `Δ^{K+1}a = Δ(Δᴷa)`, so the target series is the first-order series of `Δᴷa`.
    have hstep : fdiff^[K + 1] a = fdiff (fdiff^[K] a) :=
      congrFun (Function.iterate_succ' fdiff K) a
    rw [hstep]
    -- `Δᴷa` is null, and its base series converges to the order-`K` closed form (the IH).
    have hbk : Tendsto (fdiff^[K] a) atTop (𝓝 0) := iterate_fdiff_tendsto_zero ha0 K
    have h := fdiff_altSum_tendsto hbk ih
    -- It remains to identify the order-`(K+1)` closed form with `(-1)^n (Δᴷa)_n − 2·(order-K form)`.
    have hval :
        (∑ k ∈ Finset.range (K + 1),
              (-2 : ℝ) ^ (K + 1 - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
          + (-2 : ℝ) ^ (K + 1) * S
        = (-1 : ℝ) ^ n * (fdiff^[K] a) n
          - 2 * ((∑ k ∈ Finset.range K,
                    (-2 : ℝ) ^ (K - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
                + (-2 : ℝ) ^ K * S) := by
      -- Normalise the exponent `(K+1)-1-k` to `K-k`.
      have e1 : ∀ k, K + 1 - 1 - k = K - k := by intro k; omega
      simp only [e1]
      -- Pull the top term `k = K` out of the sum; its weight `(-2)^{K-K}` is `1`.
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
      -- Rewrite the remaining range-`K` sum as `-2` times the order-`K` sum, termwise.
      have hsum :
          (∑ k ∈ Finset.range K, (-2 : ℝ) ^ (K - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
            = -2 * ∑ k ∈ Finset.range K,
                (-2 : ℝ) ^ (K - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' : k < K := Finset.mem_range.mp hk
        have he : K - k = (K - 1 - k) + 1 := by omega
        rw [he, pow_succ]
        ring
      rw [hsum, pow_succ]
      ring
    rw [hval]
    exact h

/-! ## Corollaries -/

/-- **Unconditional closed form for antitone null sequences.**  For an antitone `a → 0` the base
series converges by Mathlib's alternating-series test, so the closed form for `T_K` holds outright
(no convergence hypothesis).  We return the base sum `S` alongside the explicit higher-difference
limit. -/
theorem iterate_altSum_limit_closed_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (ha0 : Tendsto a atTop (𝓝 0)) (n K : ℕ) :
    ∃ S, Tendsto (fun m => altSum a n m) atTop (𝓝 S)
      ∧ Tendsto (fun m => altSum (fdiff^[K] a) n m) atTop
          (𝓝 ((∑ k ∈ Finset.range K,
                  (-2 : ℝ) ^ (K - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
              + (-2 : ℝ) ^ K * S)) := by
  obtain ⟨S, hS⟩ := altSum_tendsto_of_antitone ha ha0 n
  exact ⟨S, hS, iterate_altSum_limit_closed ha0 hS K⟩

/-- **Sanity check `K = 1`.**  The closed form gives `T_1 = (-1)^n a_n − 2 S`, exactly the value
delivered by the parent's first-order engine `fdiff_altSum_tendsto`. -/
theorem iterate_altSum_limit_one {a : ℕ → ℝ} {n : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) :
    Tendsto (fun m => altSum (fdiff a) n m) atTop (𝓝 ((-1 : ℝ) ^ n * a n - 2 * S)) := by
  have h := iterate_altSum_limit_closed ha0 hS 1
  simpa [sub_eq_add_neg] using h

/-- **Self-consistency with `boole_general_tendsto`.**  Substituting the explicit closed form for
`T_K` into the order-`K` Boole limit identity reproduces exactly `S`: the boundary sum with the
Boole/Euler weights `(-1)^k/2^{k+1}` plus `((-1)^K/2^K)` times the explicit `T_K` collapses back to
the base sum.  This is the closed-form version of `boole_general_tendsto` in which the remainder is
no longer an abstract limit but the explicit formula from `iterate_altSum_limit_closed`. -/
theorem boole_general_tendsto_closed {a : ℕ → ℝ} {n K : ℕ} {S : ℝ}
    (ha0 : Tendsto a atTop (𝓝 0))
    (hS : Tendsto (fun m => altSum a n m) atTop (𝓝 S)) :
    S = (∑ k ∈ Finset.range K,
            ((-1 : ℝ) ^ k / 2 ^ (k + 1)) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
        + ((-1 : ℝ) ^ K / 2 ^ K)
          * ((∑ k ∈ Finset.range K,
                (-2 : ℝ) ^ (K - 1 - k) * ((-1 : ℝ) ^ n * (fdiff^[k] a) n))
            + (-2 : ℝ) ^ K * S) := by
  exact boole_general_tendsto ha0 hS (iterate_altSum_limit_closed ha0 hS K)

#check @iterate_altSum_limit_closed
#check @iterate_altSum_limit_closed_of_antitone
#check @boole_general_tendsto_closed

end AlternatingSeriesBooleSummationOQ01OQ01ClosedForm
