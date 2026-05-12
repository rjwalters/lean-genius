import Mathlib
import Proofs.MeanValueTheoremOQ02
import Proofs.MeanValueTheoremOQ02OQ04

/-!
# Mean Value Theorem OQ-02 / OQ-04 / OQ-01: refutation of the OQ-04 axiom

## The Open Question (OQ-01 of `mean-value-theorem-oq-02-oq-04`)

> Can the axiom `analytic_taylor_remainder_uniform_bound` (introduced in
> `MeanValueTheoremOQ02OQ04.lean`) be proved by S2 via Mathlib's
> `HasFPowerSeriesOnBall` infrastructure?

## Answer (this file): **NO** — the axiom is mathematically false as stated.

The OQ-04 axiom asserts that whenever `f : ℝ → ℝ` is real-analytic on the
open interval `(a − R, a + R)` and `|f y| ≤ M` for `y` in that interval,
then for any `0 < r < R`, `n : ℕ`, and `x ∈ [a − r, a + r]`,

```
  |f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r).
```

Taking `f = Runge` (the standard Runge function `1 / (1 + x²)`),
`a = 0`, `R = 100`, `M = 1`, `r = 1`, `n = 0`, `x = 1` gives

* hypothesis side: `Runge` is real-analytic on `(−100, 100)` (the
  denominator `1 + x²` is everywhere ≥ 1, so `AnalyticOn.div` applies); and
  `|Runge y| ≤ 1` for all `y ∈ ℝ`, in particular on `(−100, 100)`.
* axiom-conclusion: `|Runge(1) − Runge(0)| = |1/2 − 1| = 1/2`, but
  the claimed upper bound is `1 · 1^1 / (100 − 1) = 1/99 ≈ 0.0101`.
* `1/2 > 1/99`, so the axiom is violated.

This is the **classical Runge–phenomenon obstruction**: the *real*
sup-bound `M` does *not* control the size of `f^{(k)}(a)` because the
real-analytic function `1 / (1 + x²)` extends only to the *complex* disk
of radius `1` around `0` (with poles at `±i`), even though it is real-
analytic on all of `ℝ` and uniformly bounded by `1`. Cauchy-style
geometric-tail estimates of the form `M · r^(n+1) / (R − r)` require the
sup-bound `M` to apply on the *complex* disk `D(a, R) ⊂ ℂ`, not merely on
the real interval `(a − R, a + R)`. The OQ-04 axiom drops this complex
hypothesis and is therefore not a theorem of `ℝ`-analysis.

## What this file contributes (Iteration 1)

* **Definition** `runge : ℝ → ℝ := fun x => 1 / (1 + x ^ 2)` — the
  classical Runge function (entire on `ℝ`, poles in `ℂ` at `±i`).
* **Building blocks** for the counterexample:
  - `runge_analyticOn_R` : `AnalyticOn ℝ runge (Set.Ioo (-100) 100)`,
    proved entirely via Mathlib's `analyticOn_id`, `.pow`, `.add`,
    `analyticOn_const`, and `AnalyticOn.div`.
  - `runge_abs_le_one` : `∀ y, |runge y| ≤ 1` (purely arithmetic; uses
    `1 ≤ 1 + y²` and `1 / (1 + y²) ≤ 1`).
  - `runge_zero` : `runge 0 = 1` and `runge_one` : `runge 1 = 1 / 2`
    (both `norm_num`).
* **Refutation theorem** `oq04_axiom_is_false`: a self-contained proof
  that the *statement* of the OQ-04 axiom (without invoking the axiom
  itself) is false. The argument: (a) construct the witness data above,
  (b) show that the axiom's conclusion at `(R, M, r, n, x) = (100, 1, 1,
  0, 1)` would force `|1/2 − 1| ≤ 1/99`, (c) compute `|1/2 − 1| = 1/2`
  and `1/2 > 1/99`. The refutation does *not* use the parent axiom, so
  it adds no new axioms and stands even if the parent axiom is later
  removed.
* **Corrected statement** `analytic_taylor_remainder_uniform_bound_complex`
  (theorem with `sorry`, no new axioms): the *correct* Cauchy uniform
  bound, which strengthens the OQ-04 hypothesis to a complex-disk sup
  bound (`f extends holomorphically to `Metric.ball a R ⊂ ℂ` with
  uniform sup bound `M`). The Lean proof of the corrected statement is
  the next iteration's task; the file documents the precise Mathlib
  hooks (`HasFPowerSeriesOnBall.uniform_geometric_approx'` +
  `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`).

## Counts (this iteration)

* `lineCount`: 0 → ~280 (new file)
* `theoremCount`: 0 → 5 (`runge_one_add_sq_pos`, `runge_abs_le_one`,
  `runge_zero`, `runge_one`, `oq04_axiom_is_false`,
  `analytic_taylor_remainder_uniform_bound_complex`)
* `axiomCount`: 0 (no new axioms)
* `sorries`: 1 (corrected-statement proof, deferred to S2)
* `definitionCount`: 1 (`runge`)

## Connection to sibling gallery entries

* **Parent** `mean-value-theorem-oq-02-oq-04`
  (`Proofs/MeanValueTheoremOQ02OQ04.lean`): introduces the OQ-04 axiom
  that this file refutes. The parent file is *not* changed by this
  PR; readers who care about the OQ-04 axiom should read this file's
  refutation alongside the parent's docstring.
* **Grandparent** `mean-value-theorem-oq-02`
  (`Proofs/MeanValueTheoremOQ02.lean`): provides the `taylorPolynomial`
  definition and `taylorPolynomial_zero` lemma used in the refutation
  at `n = 0`.
* **Cousin** `taylor-theorem-oq-02` (analytic remainder vanishes
  qualitatively): shows `R_n(x) → 0` for analytic `f` *without* an
  explicit Cauchy form, and is therefore unaffected by the OQ-04
  obstruction.

## Path forward (next iteration's S2 task)

The corrected statement `analytic_taylor_remainder_uniform_bound_complex`
strengthens the hypothesis to: `f` is a *complex* holomorphic function
on `Metric.ball (a : ℂ) R` with uniform sup bound `M`. Under this
hypothesis the explicit Cauchy estimate

```
  ‖p k‖ ≤ M / R^k    (Cauchy coefficient bound)
```

follows from `HasFPowerSeriesOnBall.uniform_geometric_approx'`, and
summing the geometric tail gives

```
  ‖f(x) − partialSum n y‖ ≤ M · r^(n+1) / (R^n · (R − r))    for ‖y‖ ≤ r.
```

The `partialSum` of the formal multilinear series is the complex
analogue of `taylorPolynomial`, so the bridge to the parent's
`iteratedDeriv`-based polynomial requires
`HasFPowerSeriesOnBall.factorial_smul_apply_iteratedFDeriv` (or the
Lean-4 spelling thereof) — this is the precise S2 deliverable.
-/

noncomputable section

open Real Set

namespace MeanValueTheoremOQ02OQ04OQ01

/-! ## §1. The Runge function and its basic properties -/

/-- The **Runge function** `1 / (1 + x²)`: real-analytic on all of `ℝ`,
uniformly bounded by `1`, with complex poles at `±i`. The function is
the canonical witness to the Runge phenomenon: high-degree polynomial
interpolation on equispaced nodes diverges as the node count increases,
even though `f` is everywhere bounded and infinitely differentiable. -/
def runge (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

/-- `1 + x² ≥ 1 > 0` for every real `x`. Used both for the
sup-bound proof and for `AnalyticOn.div`'s nonzero-denominator
hypothesis. -/
theorem runge_one_add_sq_pos (x : ℝ) : (0 : ℝ) < 1 + x ^ 2 := by
  have h : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  linarith

/-- Uniform sup bound: `|runge y| ≤ 1` for every real `y`.
Holds because `1 / (1 + y²) ≤ 1 / 1 = 1` and `runge y ≥ 0`. -/
theorem runge_abs_le_one (y : ℝ) : |runge y| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + y ^ 2 := runge_one_add_sq_pos y
  have hge_one : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have h_nonneg : (0 : ℝ) ≤ runge y := by
    unfold runge
    exact div_nonneg zero_le_one hpos.le
  have h_le_one : runge y ≤ 1 := by
    unfold runge
    rw [div_le_one hpos]
    exact hge_one
  rw [abs_of_nonneg h_nonneg]
  exact h_le_one

/-- `runge 0 = 1`. -/
@[simp] theorem runge_zero : runge 0 = 1 := by
  unfold runge; norm_num

/-- `runge 1 = 1/2`. -/
@[simp] theorem runge_one : runge 1 = 1 / 2 := by
  unfold runge; norm_num

/-- The Runge function is real-analytic on the open interval `(−100, 100)`.
Mathlib supplies the constituent lemmas; the proof composes
`analyticAt_id`, `analyticAt_const`, `AnalyticAt.pow`, `AnalyticAt.add`,
and `AnalyticAt.div` pointwise, then lifts via `AnalyticAt.analyticWithinAt`. -/
theorem runge_analyticOn_R :
    AnalyticOn ℝ runge (Set.Ioo (-100 : ℝ) 100) := by
  unfold runge
  intro x _
  -- Build pointwise analyticity at `x` via `AnalyticAt` combinators, then
  -- convert to `AnalyticWithinAt` for the `AnalyticOn` goal.
  have h_const_one : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) x := analyticAt_const
  have h_id : AnalyticAt ℝ (fun y : ℝ => y) x := by
    have h := (ContinuousLinearMap.id ℝ ℝ).analyticAt x
    simpa using h
  have h_sq : AnalyticAt ℝ (fun y : ℝ => y ^ 2) x := h_id.pow 2
  have h_den : AnalyticAt ℝ (fun y : ℝ => 1 + y ^ 2) x :=
    h_const_one.add h_sq
  have h_den_ne : (1 + x ^ 2 : ℝ) ≠ 0 := ne_of_gt (runge_one_add_sq_pos x)
  have h_div : AnalyticAt ℝ (fun y : ℝ => 1 / (1 + y ^ 2)) x :=
    h_const_one.div h_den h_den_ne
  exact h_div.analyticWithinAt

/-! ## §2. Refutation of the OQ-04 axiom statement -/

/-- The exact statement of the OQ-04 axiom from
`Proofs/MeanValueTheoremOQ02OQ04.lean`, repackaged as a *predicate* on
`Prop`. We refute this predicate without invoking the parent axiom
itself, so this file adds no new axioms. -/
def OQ04_AxiomStatement : Prop :=
  ∀ (f : ℝ → ℝ) (a R M : ℝ),
    0 < R → 0 ≤ M →
    AnalyticOn ℝ f (Set.Ioo (a - R) (a + R)) →
    (∀ y ∈ Set.Ioo (a - R) (a + R), |f y| ≤ M) →
    ∀ (r : ℝ), 0 < r → r < R →
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (a - r) (a + r) →
      |f x - MeanValueTheoremOQ02.taylorPolynomial f a n x| ≤
        M * r ^ (n + 1) / (R - r)

/-- **The OQ-04 axiom statement is false** (Runge counterexample).

Specializing the OQ-04 statement at `(f, a, R, M, r, n, x) =
(runge, 0, 100, 1, 1, 0, 1)` would force `|runge 1 − runge 0| ≤ 1/99`,
i.e. `1/2 ≤ 1/99`, which is numerically false.

This refutation is *constructive*: every hypothesis of the OQ-04 axiom
is verified explicitly (analyticity, sup-bound, interval membership,
strict inequalities) and the resulting numerical contradiction is
discharged by `norm_num`. The proof does not invoke the parent file's
`axiom analytic_taylor_remainder_uniform_bound`, so this theorem is
genuinely a refutation of the *statement*, not just of one particular
proof attempt.

The mathematical root cause is the **Runge phenomenon**: the real
sup-bound on `(−R, R)` does not control the complex Cauchy radius
of `f`, which for `runge` is only `1` (with poles at `±i`), not `R = 100`.
The corrected statement (see §3) replaces the real sup-bound with a
complex-disk sup bound. -/
theorem oq04_axiom_is_false : ¬ OQ04_AxiomStatement := by
  intro h
  -- Apply the alleged universal statement to the Runge witness.
  have hR : (0 : ℝ) < 100 := by norm_num
  have hM : (0 : ℝ) ≤ 1 := by norm_num
  have h_interval_eq :
      Set.Ioo ((0 : ℝ) - 100) ((0 : ℝ) + 100) = Set.Ioo (-100 : ℝ) 100 := by
    have h1 : ((0 : ℝ) - 100) = -100 := by norm_num
    have h2 : ((0 : ℝ) + 100) = 100 := by norm_num
    rw [h1, h2]
  have hf : AnalyticOn ℝ runge (Set.Ioo ((0 : ℝ) - 100) (0 + 100)) := by
    rw [h_interval_eq]
    exact runge_analyticOn_R
  have hbound : ∀ y ∈ Set.Ioo ((0 : ℝ) - 100) (0 + 100), |runge y| ≤ 1 :=
    fun y _ => runge_abs_le_one y
  have hr : (0 : ℝ) < 1 := by norm_num
  have hrR : (1 : ℝ) < 100 := by norm_num
  have hx : (1 : ℝ) ∈ Set.Icc ((0 : ℝ) - 1) (0 + 1) := by
    refine ⟨by norm_num, by norm_num⟩
  have hbound_apply :=
    h runge 0 100 1 hR hM hf hbound 1 hr hrR 0 1 hx
  -- Simplify the LHS using `taylorPolynomial_zero` from the grandparent file.
  rw [MeanValueTheoremOQ02.taylorPolynomial_zero] at hbound_apply
  -- The bound now reads `|runge 1 − runge 0| ≤ 1 · 1^(0+1) / (100 − 1) = 1/99`.
  -- Substitute the numerical values of `runge 1` and `runge 0`.
  rw [runge_one, runge_zero] at hbound_apply
  -- We now have `|1/2 − 1| ≤ 1/99`. The LHS equals `1/2` and `1/2 > 1/99`,
  -- contradiction.
  have h_lhs : |(1 / 2 : ℝ) - 1| = 1 / 2 := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by ring, abs_neg, abs_of_pos]
    norm_num
  have h_rhs : (1 : ℝ) * 1 ^ (0 + 1) / (100 - 1) = 1 / 99 := by norm_num
  rw [h_lhs, h_rhs] at hbound_apply
  -- `hbound_apply : (1 : ℝ)/2 ≤ 1/99`. Contradiction by `norm_num`.
  norm_num at hbound_apply

/-- **Corollary**: the parent file's axiom
`analytic_taylor_remainder_uniform_bound` is *unprovable* in any
extension of Lean's `ℝ`-analysis (it would entail
`OQ04_AxiomStatement`). Concretely, this file's `oq04_axiom_is_false`
proves that the *statement* of the parent axiom is inconsistent with
the rest of `ℝ`-analytic function theory; introducing the parent axiom
into a build is therefore introducing a `False`-witness, and any
downstream consumer should be flagged. -/
theorem oq04_parent_axiom_is_false_in_principle : ¬ OQ04_AxiomStatement :=
  oq04_axiom_is_false

/-! ## §3. Corrected statement (complex-disk sup bound)

The mathematically correct Cauchy uniform bound replaces the real
sup-bound on `(a − R, a + R) ⊂ ℝ` with a complex sup-bound on
`Metric.ball (a : ℂ) R ⊂ ℂ`. We restate the corrected version as a
`theorem` with a single `sorry`; the proof is deferred to S2 and goes
through Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`
plus the explicit Cauchy coefficient estimate
`FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`. -/

/-- **Corrected Cauchy uniform bound** (complex hypothesis).

For `f : ℂ → ℂ` holomorphic on `Metric.ball a R` (the open complex disk
of radius `R` around `a`) with uniform sup bound `‖f z‖ ≤ M` on that
disk, and any `0 < r < R`, the partial sum of the formal power series
of `f` at `a` satisfies
```
  ‖f z − p.partialSum n (z − a)‖ ≤ M · (r / R)^(n+1) · R / (R − r)
                                  = M · r^(n+1) / (R^n · (R − r))
```
for every `z` with `‖z − a‖ ≤ r` and every `n : ℕ`.

This is the correct Cauchy form: note the explicit `R^n` factor in the
denominator, which is precisely what the OQ-04 statement omits (and
which is why `runge` violates the OQ-04 statement at `R = 100, n = 0`:
the missing `R^n = 100^0 = 1` happens to coincide with the OQ-04 bound
at `n = 0`, but the *real* sup-bound `M = 1` is too weak — Cauchy
estimates need the *complex* sup bound on a complex disk of radius `1`,
where `runge` is unbounded near `±i`).

The proof (deferred to next iteration) chains:
1. `HasFPowerSeriesOnBall.uniform_geometric_approx'` (Mathlib): gives
   `‖f(a + y) − p.partialSum n y‖ ≤ C · (a · ‖y‖/r')^n` for some
   geometric `a < 1` and `C > 0`.
2. `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`
   (Mathlib): `∀ k, ‖p k‖ ≤ M / r^k` — the Cauchy coefficient bound.
3. Explicit geometric-tail summation: `∑_{k > n} (M/R^k) · r^k =
   M · (r/R)^{n+1} / (1 − r/R)`.

`sorry` here marks the formalization gap, *not* a mathematical gap. -/
theorem analytic_taylor_remainder_uniform_bound_complex
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (_hR : 0 < R) (_hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (_hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (_hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (r : ℝ) (_hr : 0 < r) (_hrR : r < R)
    (n : ℕ) (z : ℂ) (_hz : ‖z - a‖ ≤ r) :
    ‖f z - p.partialSum n (z - a)‖ ≤ M * r ^ (n + 1) / (R ^ n * (R - r)) := by
  -- Deferred to S2: see §3 docstring for the Mathlib chain.
  sorry

/-! ## §4. Verification -/

#check @runge
#check @runge_analyticOn_R
#check @runge_abs_le_one
#check @runge_zero
#check @runge_one
#check @oq04_axiom_is_false
#check @oq04_parent_axiom_is_false_in_principle
#check @analytic_taylor_remainder_uniform_bound_complex

end MeanValueTheoremOQ02OQ04OQ01
