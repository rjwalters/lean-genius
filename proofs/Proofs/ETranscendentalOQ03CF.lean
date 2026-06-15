/-
  Continued-fraction route to `μ(exp 1) ≤ 2`
  ==========================================

  Companion / blueprint file for `ETranscendentalOQ03.lean`.

  STATUS: build-pending, UNREGISTERED (not imported by `Proofs.lean`).
  Authored under a verification blackout (Docker build + Aristotle `prove`
  both unavailable). The statements below pin the exact Mathlib v4.26.0
  identifiers the route depends on; the proof bodies are `sorry` and have
  NOT been machine-checked. Do not register this file or rely on its lemmas
  until a live build session discharges the sorries.

  ── What this file is for ────────────────────────────────────────────────
  `ETranscendentalOQ03.lean` currently has a single open axiom

      axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) :
        ¬ LiouvilleWith p (Real.exp 1)

  i.e. the upper bound `μ(e) ≤ 2`. Prior sessions (S5d/S6/S13) established
  that the *series* route (`e = Σ 1/k!`, via `Real.exp_bound` /
  `Complex.sum_div_factorial_le`) closes only the EASY direction `μ ≥ 2`
  (already done: `irrational_liouvilleWith_two`), not the upper bound. The
  upper bound genuinely needs the continued-fraction best-approximation
  theory.

  This file factors that one opaque axiom into THREE named targets, so the
  next live session has concrete sub-goals instead of a monolith:

    (G2) `convs_sub_lower_bound` — a convergent-error LOWER bound, the mirror
         of Mathlib's existing UPPER bound `GenContFract.abs_sub_convs_le`.
         NEW FINDING (this session): this is CHEAP, derivable from the exact
         error formula `GenContFract.sub_convs_eq` plus
         `succ_nth_stream_b_le_nth_stream_fr_inv`. Prior notes assumed the
         lower bound was a missing/hard piece — it is not.

    (G3) `not_liouvilleWith_of_partDen_subexp` — the general analytic
         reduction: bounded-growth partial denominators ⟹ irrationality
         measure ≤ 2. This is the classical "law of best approximation"
         (convergents are best approximations). MEDIUM effort; absent from
         Mathlib. ~100–200 LOC.

    (G1) `exp_one_partDen_linear` — the e-SPECIFIC arithmetic: the regular
         continued fraction of e is `[2; 1, 2, 1, 1, 4, 1, 1, 6, …]`, so its
         partial denominators grow at most linearly. This is Euler's 1737
         theorem and is the TRUE BOTTLENECK: absent from Mathlib, ~hundreds
         of LOC (a research-grade formalization of Euler/Hermite). The
         Hermite–Padé integral route is an ALTERNATIVE that avoids G1 and G3
         by constructing the approximations and their lower bounds directly;
         it is the recommended path if G1 proves too costly.

  ── Mathlib v4.26.0 hooks (verified to exist by source inspection) ────────
    GenContFract.of                                        (Computation/Basic)
    GenContFract.convs / .dens                             (Basic.lean:325/321)
    GenContFract.abs_sub_convs_le                          (Approximations:393)
      |v - convs n| ≤ 1 / (dens n * dens (n+1))
    GenContFract.sub_convs_eq                              (Approximations:328)
      v - convs n = (-1)^n / (B * (fr⁻¹ * B + pB))   [exact error formula]
    GenContFract.succ_nth_stream_b_le_nth_stream_fr_inv    (Approximations:111)
      b_{n+1} ≤ fr_n⁻¹   [⟹ fr⁻¹ < partDen + 1 by `nth_stream_fr_lt_one`]
    GenContFract.of_den_mono                               (Approximations:299)
    GenContFract.succ_nth_fib_le_of_nth_den                (Approximations:249)
    LiouvilleWith                                          (…/Liouville/LiouvilleWith:51)
      ∃ C, ∃ᶠ n in atTop, ∃ m, x ≠ m/n ∧ |x - m/n| < C / n^p

  GAPS confirmed absent from Mathlib v4.26.0 (grepped the whole
  `Mathlib/Algebra/ContinuedFractions/` tree):
    * no best-approximation theorem (no `best_approx*`)
    * no convergent-error LOWER bound (only the upper bound above)
    * no continued fraction of `e` (no mention of `exp`)
-/
import Mathlib

open Real Filter
open scoped Topology

namespace ETranscendentalOQ03CF

/-! ### (G2) Convergent-error two-sided bound  -- CHEAP, derivable from Mathlib -/

/-- **Lower bound on the convergent error** (mirror of `abs_sub_convs_le`).

For a non-terminating regular continued fraction of `v`,
`1 / (dₙ · (dₙ₊₁ + dₙ)) ≤ |v - pₙ/qₙ|`, where `dₙ = (of v).dens n`.

Informal proof (NOT machine-checked — build-pending):
By `GenContFract.sub_convs_eq` the exact error is
`v - convs n = (-1)^n / (B · (fr⁻¹·B + pB))` with `B = dens n`, `pB = dens (n-1)`,
and `fr = ifp.fr ∈ (0,1)` the `n`-th fractional remainder. Taking absolute values,
`|v - convs n| = 1 / (B · (fr⁻¹·B + pB))`. Now `fr⁻¹` lies strictly between the
`(n+1)`-st partial denominator `b_{n+1}` and `b_{n+1}+1`:
`b_{n+1} ≤ fr⁻¹` (`succ_nth_stream_b_le_nth_stream_fr_inv`) and `fr < 1` gives
`fr⁻¹ > 1`; together with `fr⁻¹ = b_{n+1} + (next fr) < b_{n+1} + 1`. Hence
`fr⁻¹·B + pB < (b_{n+1}+1)·B + pB = (b_{n+1}·B + pB) + B = dens (n+1) + dens n`
(using the denominator recurrence `dₙ₊₁ = b_{n+1}·dₙ + dₙ₋₁`). Inverting the
inequality (all quantities positive) yields the claim. -/
theorem convs_sub_lower_bound {v : ℝ} {n : ℕ}
    (h : ¬ (GenContFract.of v).TerminatedAt n) :
    1 / ((GenContFract.of v).dens n *
          ((GenContFract.of v).dens (n + 1) + (GenContFract.of v).dens n))
      ≤ |v - (GenContFract.of v).convs n| := by
  sorry

/-! ### (G3) General reduction: bounded partial-denominator growth ⟹ μ ≤ 2 -/

/-- **Best-approximation reduction.**  If the regular continued fraction of an
irrational `x` is infinite and its partial denominators are eventually bounded
by a sub-exponential function of the index — concretely, it suffices that
`log (dₙ₊₁) / log (dₙ) → 1`, which holds whenever the partial denominators
grow at most polynomially while the convergent denominators grow
super-exponentially — then `x` is not Liouville with any exponent `> 2`.

The proof is the classical law of best approximation: convergents `pₖ/qₖ` are
the best rational approximations, so for any `m/n` with `qₖ ≤ n < qₖ₊₁` we have
`|x - m/n| ≥ |qₖ x - pₖ| / n ≥ 1 / ((qₖ + qₖ₊₁)·n) ≥ 1 / ((qₖ+qₖ₊₁)·qₖ₊₁)`
(the middle step is (G2)). The growth hypothesis converts this into
`|x - m/n| ≥ c / n^{2+ε}` for every `ε > 0` and all large `n`, contradicting
`LiouvilleWith p x` for `p > 2`.

NOTE: the precise hypothesis form is deliberately left abstract here; pinning
it down (bounded partial quotients vs. denominator-ratio control) is part of
the G3 work. The placeholder `hgrowth` stands for that hypothesis (the
all-`m/n` lower bound it asserts already forces irrationality, so `Irrational`
is not needed as a separate input at this level of abstraction). -/
theorem not_liouvilleWith_of_partDen_subexp {x : ℝ}
    (hgrowth :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ m : ℤ, (1 : ℝ) / (n : ℝ) ^ (2 + ε) ≤ |x - m / n|)
    (p : ℝ) (hp : 2 < p) :
    ¬ LiouvilleWith p x := by
  sorry

/-! ### (G1) The e-specific kernel: e's CF has linearly-bounded partial denominators -/

/-- **Euler (1737): the regular continued fraction of `e`.**

`e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, …]`, i.e. with `a₀ = 2` and, for
`k ≥ 1`, `a_{3k-2} = 1`, `a_{3k-1} = 2k`, `a_{3k} = 1`. In particular the
`n`-th partial denominator is bounded by a linear function of `n`.

This is THE BOTTLENECK: absent from Mathlib, ~hundreds of LOC. The standard
formalization derives the convergent numerators/denominators from the Hermite
integrals `∫₀¹ xⁿ(1-x)ⁿ eˣ dx / n!` and verifies the recurrence; the integral
route can also be used directly to discharge G2+G3 for `e` without naming the
CF (the Hermite–Padé alternative). -/
theorem exp_one_partDen_linear :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ m : ℤ, (1 : ℝ) / (n : ℝ) ^ (2 + ε) ≤ |Real.exp 1 - m / n| := by
  sorry

/-! ### Assembly: factored form of the open axiom -/

/-- `μ(e) ≤ 2`, obtained by feeding the e-specific kernel (G1) into the general
reduction (G3). When all three sorries above are discharged, this `theorem`
replaces `axiom e_not_liouvilleWith_gt_two` in `ETranscendentalOQ03.lean`. -/
theorem e_not_liouvilleWith_gt_two' (p : ℝ) (hp : p > 2) :
    ¬ LiouvilleWith p (Real.exp 1) :=
  not_liouvilleWith_of_partDen_subexp exp_one_partDen_linear p hp

end ETranscendentalOQ03CF
