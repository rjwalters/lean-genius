/-
# Sum of Divisors — OQ-03: Robin's Inequality and its RH equivalence

Open question OQ-03 (from `sum-of-divisors`) asks to "formalize Robin's inequality
`σ(n) < e^γ · n · ln(ln n)`" and "state the equivalence with RH as an axiom."

## Honest scope of this file

The candidate framing — "verifiable by `native_decide` on a bounded range `n ≤ 5040`" — does **not**
work, for two independent reasons documented here:

1. **The inequality is FALSE on the bounded range.** Robin's inequality fails for a finite set of
   exceptional `n`, the largest being `n = 5040 = 7!`. (Under RH that exceptional set is exactly
   the 27 numbers `{1,2,3,4,5,6,8,9,10,12,16,18,20,24,30,36,48,60,72,84,120,180,240,360,720,840,
   2520,5040}`.) So there is no true statement "`RobinInequality n` for all `n ≤ 5040`" to decide.
   Robin's theorem is about `n ≥ 5041`.

2. **The comparison is transcendental, not decidable.** `e^γ` and `ln(ln n)` are not rational, so
   `σ(n) < e^γ · n · ln(ln n)` is not a `Decidable` proposition and `native_decide` cannot touch it.
   Worse, the only `γ` bounds in Mathlib are `1/2 < γ < 2/3`, giving `e^γ ∈ (1.6487, 1.9477)` — far
   too loose to settle the boundary cases (at `n = 5040`, `σ(n)/n ≈ 3.838` while
   `e^γ · ln(ln 5040) ≈ 3.82`, and the loose bounds place this in `(3.54, 4.18)`: undecided).

So OQ-03's verifiable content splits into: (a) a **precise statement** of Robin's inequality using
`Real.eulerMascheroniConstant` and `ArithmeticFunction.sigma`; (b) the **RH equivalence as an axiom**
(as requested — a deep 1984 theorem of Robin, far beyond current Mathlib, and `RiemannHypothesis` is
itself open); and (c) the genuinely **machine-checkable structural facts** that do not need tight
transcendental bounds. This file delivers all three honestly. Items (a),(c) are 0-axiom; item (b) is
the single, clearly-labeled axiom (so the entry is `axiomatized`, the correct status for any
RH-linked result).

## Results
* `RobinInequality`               — the precise predicate `σ(n) < e^γ · n · ln(ln n)`.
* `exp_eulerMascheroni_lower/upper`— `e^{1/2} < e^γ < e^{2/3}` (verified, 0 axioms), the sharpest
                                     `e^γ` enclosure available from Mathlib's `γ` bounds.
* `log_log_pos`                    — `ln(ln n) > 0` for `n ≥ 3` (verified, 0 axioms).
* `robin_rhs_pos`                  — the Robin bound `e^γ · n · ln(ln n)` is positive for `n ≥ 3`
                                     (verified, 0 axioms) — so the inequality is well-posed.
* `robin_iff_riemannHypothesis`    — **AXIOM**: Robin's theorem, `(∀ n ≥ 5041, RobinInequality n) ↔
                                     RiemannHypothesis`.

## References
- Robin, G. (1984). "Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann."
  J. Math. Pures Appl. 63, 187–213.
- Gronwall, T.H. (1913). "Some asymptotic expressions in the theory of numbers." (limsup = e^γ)
- Mathlib: `Real.eulerMascheroniConstant`, `one_half_lt_eulerMascheroniConstant`,
  `eulerMascheroniConstant_lt_two_thirds`; `RiemannHypothesis`.
-/

import Mathlib

open ArithmeticFunction Real

namespace SumOfDivisorsRobin

/-- **Robin's inequality at `n`**: `σ(n) < e^γ · n · ln(ln n)`, where `σ = ArithmeticFunction.sigma 1`
    is the sum-of-divisors function and `γ` is the Euler–Mascheroni constant. -/
noncomputable def RobinInequality (n : ℕ) : Prop :=
  (sigma 1 n : ℝ) < Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n)

/-! ## Verified structural facts (0 axioms) -/

/-- Lower enclosure of `e^γ`: `e^{1/2} < e^γ` (since `1/2 < γ`). Numerically `e^{1/2} ≈ 1.6487`. -/
theorem exp_eulerMascheroni_lower :
    Real.exp (1 / 2) < Real.exp eulerMascheroniConstant :=
  Real.exp_lt_exp.mpr one_half_lt_eulerMascheroniConstant

/-- Upper enclosure of `e^γ`: `e^γ < e^{2/3}` (since `γ < 2/3`). Numerically `e^{2/3} ≈ 1.9477`. -/
theorem exp_eulerMascheroni_upper :
    Real.exp eulerMascheroniConstant < Real.exp (2 / 3) :=
  Real.exp_lt_exp.mpr eulerMascheroniConstant_lt_two_thirds

/-- For `n ≥ 3`, the iterated logarithm `ln(ln n)` is positive (because `ln n > 1`, as `n > e`). -/
theorem log_log_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.log (Real.log n) := by
  have h3 : Real.exp 1 < (n : ℝ) := by
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ 3 := by norm_num
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 1 < Real.log n := by
    have h := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h
  exact Real.log_pos hlogn

/-- The Robin bound `e^γ · n · ln(ln n)` is strictly positive for `n ≥ 3`, so Robin's inequality is
    a well-posed comparison of two positive quantities on the relevant range. -/
theorem robin_rhs_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  exact mul_pos (mul_pos (Real.exp_pos _) hn0) (log_log_pos hn)

/-! ## The RH equivalence (axiom, as requested by OQ-03) -/

/-- **Robin's theorem (1984).** The Riemann Hypothesis holds **iff** Robin's inequality
    `σ(n) < e^γ · n · ln(ln n)` holds for every `n ≥ 5041`. Stated as an axiom: this is a deep
    analytic theorem (and `RiemannHypothesis` is itself an open Millennium Problem), well beyond
    what current Mathlib can prove. This axiom is the gallery's bridge between the elementary
    divisor function `σ` and the Riemann Hypothesis. -/
axiom robin_iff_riemannHypothesis :
    (∀ n : ℕ, 5041 ≤ n → RobinInequality n) ↔ RiemannHypothesis

/-!
## Closing remark

What is *not* here: a decision procedure for `RobinInequality n` at specific `n`. As explained in
the header, that is impossible with `native_decide` (transcendental constants) and indeterminate
with Mathlib's current `γ` enclosure for the delicate `n` near `5040`. Sharpening the `e^γ`
enclosure (e.g. to `1.781 < e^γ < 1.782`) — which would in principle let one *prove* the
exceptionality of `5040` and verify Robin on a finite head — is the natural follow-up, but it
requires substantially tighter `eulerMascheroniConstant` bounds than Mathlib provides today.
-/

#check @RobinInequality
#check @exp_eulerMascheroni_lower
#check @exp_eulerMascheroni_upper
#check @robin_rhs_pos
#check @robin_iff_riemannHypothesis

end SumOfDivisorsRobin
