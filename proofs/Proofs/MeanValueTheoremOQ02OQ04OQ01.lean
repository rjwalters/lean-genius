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

## Status (S7 ACT, 2026-05-14, researcher-3): **COMPLETE**

All supporting lemmas and the corrected complex theorem are now fully
proven: the file is **0 axioms, 0 sorries** at 758 LOC, with a clean
`docker-build` (7745 jobs, 2026-05-14, pre-blackout). The residual
`cauchy_diag_norm_bound_at_radius` sorry was discharged via Mathlib's
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` Cauchy
estimate (S6–S6f PREP pinned the v4.26.0 lemma names; S7 ACT pasted the
drop-in and fixed three elaborator details). **The per-section "sorry" /
"next iteration's task" notes below are historical iteration records
(Iteration 1 – S5) superseded by this S7 completion.**

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
open scoped NNReal ENNReal Topology Filter

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
`Metric.ball (a : ℂ) R ⊂ ℂ`.

### Off-by-one fix (S3)

The S1-S2 placeholder statement of §3 paired `p.partialSum n` with the
RHS `M · r^(n+1) / (R^n · (R-r))`. **This pairing is off by one.**

Mathlib's convention is `p.partialSum n x := ∑ k ∈ Finset.range n, …`,
so `partialSum n` truncates at degree `n − 1` and the remainder starts
at degree `n`. The geometric tail `∑_{k ≥ n} M · (r/R)^k` evaluates to
`M · (r/R)^n · R / (R − r) = M · r^n · R / (R^n · (R − r))`, not to
`M · r^(n+1) / (R^n · (R − r))`. The two differ by a factor of `r/R`,
and the S1-S2 statement is **false at `n = 0`** for any `0 < r < R/2`:
the constant function `f ≡ 1` has `‖f z − p.partialSum 0 (z − a)‖ =
‖1 − 0‖ = 1`, while the S1-S2 RHS at `n = 0` is `r/(R − r) < 1`.

The §3a theorem `originalRemainderForm_is_false` formalizes this
refutation via the constant-1 witness on `Metric.ball (0 : ℂ) 1` at
`(R, M, r, n, z) = (1, 1, 1/4, 0, 0)`.

§3b restates the corrected version with `p.partialSum (n + 1)` so that
the truncation matches the parent's `taylorPolynomial f a n` of degree
≤ `n`. With the index shift, the geometric tail starting at degree
`k = n + 1` evaluates to `M · r^(n+1) / (R^n · (R − r))` (correct).

The §3b proof is decomposed into:

* `geometric_tail_identity` (proven, pure algebra): the rewrite
  `(r / R)^(n+1) · R / (R − r) = r^(n+1) / (R^n · (R − r))`.
* `cauchy_diag_norm_bound` (deferred, sorry): the per-degree Cauchy
  coefficient bound `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / R)^k` for `‖w‖ < R`.
* `analytic_taylor_remainder_uniform_bound_complex` (deferred, sorry):
  one-step combination of `cauchy_diag_norm_bound`,
  `HasFPowerSeriesOnBall.hasSum`,
  `norm_sub_le_of_geometric_bound_of_hasSum`, and
  `geometric_tail_identity`.

`sorry` markers here mark formalization gaps, *not* mathematical gaps;
the corrected statement is the textbook Cauchy uniform bound. -/

/-- The S1-S2 explicit-form RHS packaged as a `Prop` predicate (without
`partialSum (n+1)` index correction). We refute this predicate in
`originalRemainderForm_is_false`; the corrected statement appears
below as `analytic_taylor_remainder_uniform_bound_complex`.

Quantifies over `(f, a, R, M, p, hypotheses, r, n, z, hz)` and asserts
`‖f z − p.partialSum n (z − a)‖ ≤ M · r^(n+1) / (R^n · (R − r))`. -/
def OriginalRemainderForm : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R M : ℝ),
    0 < R → 0 ≤ M →
    ∀ (p : FormalMultilinearSeries ℂ ℂ ℂ),
    HasFPowerSeriesOnBall f p a (ENNReal.ofReal R) →
    (∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M) →
    ∀ (r : ℝ), 0 < r → r < R →
    ∀ (n : ℕ) (z : ℂ), ‖z - a‖ ≤ r →
      ‖f z - p.partialSum n (z - a)‖ ≤ M * r ^ (n + 1) / (R ^ n * (R - r))

/-- **The S1-S2 explicit-form statement is false** (off-by-one refutation).

The constant function `f ≡ 1` on `Metric.ball (0 : ℂ) 1` with `R = 1`,
`M = 1`, `r = 1/4`, `n = 0`, `z = 0` satisfies every hypothesis of
`OriginalRemainderForm` (analyticity via `hasFPowerSeriesOnBall_const`
restricted to radius 1, sup bound `‖(1 : ℂ)‖ = 1 ≤ 1`, strict
inequalities), but the conclusion would force
`‖(1 : ℂ) − 0‖ ≤ 1 / 3`, i.e. `1 ≤ 1/3`, contradiction.

The witness `(constFormalMultilinearSeries ℂ ℂ 1).partialSum 0` is the
empty sum (`Finset.range 0 = ∅`), hence `= 0 : ℂ`, so the LHS evaluates
to `‖1 − 0‖ = 1`. The RHS `1 · (1/4)^1 / (1^0 · (1 − 1/4)) = (1/4) /
(3/4) = 1/3`. The numerical contradiction `1 ≤ 1/3` is discharged by
`norm_num`.

The mathematical root cause is the `partialSum n` truncation
convention (sum over `Finset.range n`, i.e., degrees `0, …, n−1`):
the geometric tail from degree `n` evaluates to
`M · r^n · R / (R^n · (R − r))`, not `M · r^(n+1) / (R^n · (R − r))`.
The corrected statement (§3b) uses `partialSum (n + 1)` so the index
matches the RHS. -/
theorem originalRemainderForm_is_false : ¬ OriginalRemainderForm := by
  intro h
  -- Apply the alleged universal statement to the constant-1 witness on `ℂ`.
  set f : ℂ → ℂ := fun _ => (1 : ℂ)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := constFormalMultilinearSeries ℂ ℂ (1 : ℂ)
  have hR : (0 : ℝ) < 1 := by norm_num
  have hM : (0 : ℝ) ≤ 1 := by norm_num
  -- Convert the radius-⊤ constant power series to radius `ENNReal.ofReal 1`.
  have h_top_ofReal : (ENNReal.ofReal (1 : ℝ)) ≤ ⊤ := le_top
  have h_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_pos]; norm_num
  have hf : HasFPowerSeriesOnBall f p 0 (ENNReal.ofReal (1 : ℝ)) := by
    have h_const : HasFPowerSeriesOnBall (fun _ : ℂ => (1 : ℂ))
        (constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) ⊤ :=
      hasFPowerSeriesOnBall_const
    exact h_const.mono h_ofReal_pos h_top_ofReal
  have hbound : ∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), ‖f z‖ ≤ 1 := by
    intro z _
    show ‖(1 : ℂ)‖ ≤ 1
    simp
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hrR : (1 / 4 : ℝ) < 1 := by norm_num
  have hz : ‖(0 : ℂ) - 0‖ ≤ (1 / 4 : ℝ) := by
    simp
  have hbound_apply :=
    h f 0 1 1 hR hM p hf hbound (1 / 4) hr hrR 0 0 hz
  -- LHS: `‖f 0 − p.partialSum 0 (0 − 0)‖ = ‖1 − 0‖ = 1`.
  have h_partialSum : (p.partialSum 0) ((0 : ℂ) - 0) = 0 := by
    unfold FormalMultilinearSeries.partialSum
    simp
  rw [h_partialSum] at hbound_apply
  -- `f 0` is definitionally `(1 : ℂ)`; convert and rewrite the norm.
  have h_f_zero : f 0 = (1 : ℂ) := rfl
  rw [h_f_zero, sub_zero] at hbound_apply
  have h_norm_one : ‖(1 : ℂ)‖ = 1 := norm_one
  rw [h_norm_one] at hbound_apply
  -- RHS at `(R, M, r, n) = (1, 1, 1/4, 0)`: `1 * (1/4)^1 / (1^0 * (1 - 1/4)) = 1/3`.
  norm_num at hbound_apply

/-! ### §3b. Corrected statement (`partialSum (n + 1)`) -/

/-- **Geometric tail identity** (proven, pure algebra).

The rewrite `(r / R)^(n+1) · R / (R − r) = r^(n+1) / (R^n · (R − r))`
under hypotheses `0 < r`, `r < R`. Used to convert between the
"geometric-ratio" form of the Cauchy tail bound and the explicit
"polynomial-power" form. -/
theorem geometric_tail_identity (r R : ℝ) (hR : 0 < R) (hrR : r < R) (n : ℕ) :
    (r / R) ^ (n + 1) * R / (R - r) = r ^ (n + 1) / (R ^ n * (R - r)) := by
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hRr_pos : 0 < R - r := by linarith
  have hRr_ne : R - r ≠ 0 := ne_of_gt hRr_pos
  have hRn_ne : R ^ n ≠ 0 := pow_ne_zero n hR_ne
  -- Split into two steps via the intermediate identity `(r/R)^(n+1) * R = r^(n+1) / R^n`.
  have key : (r / R) ^ (n + 1) * R = r ^ (n + 1) / R ^ n := by
    rw [div_pow, pow_succ R n]
    field_simp
  calc (r / R) ^ (n + 1) * R / (R - r)
      = r ^ (n + 1) / R ^ n / (R - r) := by rw [key]
    _ = r ^ (n + 1) / (R ^ n * (R - r)) := by rw [div_div]

/-- **Cauchy diagonal-norm bound at a strict intermediate radius**
(S5 sub-lemma; one remaining `sorry`).

For `f : ℂ → ℂ` holomorphic on `Metric.ball a R` with uniform sup bound
`‖f z‖ ≤ M` on that disk, the *diagonal* multilinear evaluation
`p k (fun _ ↦ w)` of the `k`-th formal-power-series coefficient is
bounded by `M · (‖w‖ / r')^k` for every `r' ∈ (0, R)`.

This is the **finite-radius** form of the textbook Cauchy coefficient
estimate. It is the statement that directly matches Mathlib's
Cauchy-integral chain on the closed sphere `sphere a r'`: the bound
involves only the *strict* sub-disk radius `r'`, not the boundary `R`.
The boundary form `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / R)^k` then follows
by taking `r' → R⁻` (continuity of the upper bound — formalized in
`cauchy_diag_norm_bound` below).

The remaining proof chain (deferred to a future iteration; this is the
only residual `sorry` in this file as of S5) routes through:

1. **Sub-disk inclusion**: `closedBall a r' ⊂ Metric.ball a R` for
   `r' < R`, so `f` is bounded by `M` on `sphere a r' ⊂ closedBall a r'`.
2. `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
   (Cauchy integral on `sphere a r'`):
   `‖iteratedDeriv k f a‖ ≤ k! · M / (r')^k`.
3. `HasFPowerSeriesOnBall.factorial_smul`: relates the formal-series
   coefficient `p k` to `iteratedFDeriv k f a / k!`.
4. `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` (in 1D the product
   collapses to `w^k`):
   `(iteratedFDeriv k f a) (fun _ ↦ w) = w^k * iteratedDeriv k f a`.
5. Combine: `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / r')^k`.

Why this decomposition is useful. The boundary form
`cauchy_diag_norm_bound` requires two distinct mathematical ingredients:
(a) the Cauchy estimate on a *closed* sphere of radius `r' < R`, and
(b) the continuity-of-upper-bound limit `r' → R⁻`. The original
`cauchy_diag_norm_bound` statement entangled both. This sub-lemma
isolates ingredient (a) — the *finite-radius* Cauchy bound — so that
the limit argument (ingredient b) can be discharged independently and
the remaining gap is the precise statement Mathlib's Cauchy-integral
infrastructure produces directly. -/
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (_hR : 0 < R) (_hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (hr' : 0 < r') (hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k := by
  -- (1) Inclusions: `closedBall a r' ⊂ ball a R` and `sphere a r' ⊂ closedBall a r'`.
  have h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R := fun z hz =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'R)
  have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := fun z hz => by
    apply hbound
    exact h_cls_sub (Metric.sphere_subset_closedBall hz)
  -- (2) Analytic on `Metric.ball a R` via the EMetric ↔ Metric set bridge,
  -- then `.mono` to `Metric.closedBall a r'`.
  have h_analyticOn_R : AnalyticOnNhd ℂ f (Metric.ball a R) := by
    have h := hf.analyticOnNhd
    rwa [Metric.emetric_ball] at h
  have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
    h_analyticOn_R.mono h_cls_sub
  -- (3) DiffContOnCl on `Metric.ball a r'` via `DiffContOnCl.mk_ball`.
  have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') :=
    DiffContOnCl.mk_ball
      (h_analyticOn_cls.differentiableOn.mono Metric.ball_subset_closedBall)
      h_analyticOn_cls.continuousOn
  -- (4) Mathlib's Cauchy estimate on `sphere a r'` (`Liouville.lean:44`).
  have h_cauchy : ‖iteratedDeriv k f a‖ ≤ k.factorial * M / r' ^ k :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' hf_diff_cont
      h_sphere_bound
  -- (5) Bridge `p k` to `iteratedDeriv k f a` via `factorial_smul` +
  -- diagonal collapse (`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`).
  have h_factor_smul : k.factorial • p k (fun _ ↦ w) =
      iteratedFDeriv ℂ k f a (fun _ ↦ w) :=
    hf.factorial_smul w k
  have h_diag : iteratedFDeriv ℂ k f a (fun _ ↦ w) =
      w ^ k • iteratedDeriv k f a := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp
  have h_combined : k.factorial • p k (fun _ ↦ w) =
      w ^ k • iteratedDeriv k f a := h_factor_smul.trans h_diag
  -- (6) Take norms, divide by `k.factorial > 0`.
  have h_normed : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ ≤
      (k.factorial : ℝ) * (M * (‖w‖ / r') ^ k) := by
    have h1 : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ =
        ‖w‖ ^ k * ‖iteratedDeriv k f a‖ := by
      have hnorm : ‖k.factorial • p k (fun _ ↦ w)‖ =
          ‖w ^ k • iteratedDeriv k f a‖ := by rw [h_combined]
      rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_smul, norm_pow] at hnorm
      exact hnorm
    rw [h1]
    have h_pow_nn : 0 ≤ ‖w‖ ^ k := pow_nonneg (norm_nonneg _) _
    have h2 : ‖w‖ ^ k * ‖iteratedDeriv k f a‖ ≤
        ‖w‖ ^ k * (k.factorial * M / r' ^ k) :=
      mul_le_mul_of_nonneg_left h_cauchy h_pow_nn
    have hr'_pow_pos : (0 : ℝ) < r' ^ k := pow_pos hr' k
    calc ‖w‖ ^ k * ‖iteratedDeriv k f a‖
        ≤ ‖w‖ ^ k * (k.factorial * M / r' ^ k) := h2
      _ = (k.factorial : ℝ) * (M * (‖w‖ / r') ^ k) := by
          rw [div_pow]; ring
  have h_factorial_pos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast k.factorial_pos
  exact le_of_mul_le_mul_left h_normed h_factorial_pos

/-- **Cauchy diagonal-norm bound** (S4 statement; S5 limit-extraction proof).

For `f : ℂ → ℂ` holomorphic on `Metric.ball a R` with uniform sup bound
`‖f z‖ ≤ M` on that disk, the *diagonal* multilinear evaluation
`p k (fun _ ↦ w)` of the `k`-th formal-power-series coefficient is
bounded by `M · (‖w‖ / R)^k` for every `w` with `‖w‖ < R`.

**Proof (S5).** The bound for every strict intermediate radius
`r' ∈ (0, R)` is supplied by `cauchy_diag_norm_bound_at_radius`:
`‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / r')^k`. The function
`r' ↦ M · (‖w‖ / r')^k` is continuous at `R` (since `R > 0`), so
`Filter.Tendsto` along `𝓝[<] R` lands at `M · (‖w‖ / R)^k`.
`le_of_tendsto` then transports the eventual pointwise bound to the
limit value, yielding the boundary bound.

As of S5 this routed through `cauchy_diag_norm_bound_at_radius`, then the
sole residual `sorry`. **S7 (2026-05-14) discharged that lemma**, so the
limit-extraction step here and the finite-radius Cauchy estimate it calls
are both fully proven via Mathlib's
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
infrastructure (see the §0 Status banner). -/
theorem cauchy_diag_norm_bound
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (_hw : ‖w‖ < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / R) ^ k := by
  -- Setup.
  have hR_ne : (R : ℝ) ≠ 0 := ne_of_gt hR
  -- Pointwise bound on the open interval `(0, R)` of intermediate radii,
  -- via the deferred finite-radius Cauchy estimate.
  have h_at_r : ∀ r' ∈ Set.Ioo (0 : ℝ) R,
      ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k := by
    rintro r' ⟨hr'_pos, hr'_lt_R⟩
    exact cauchy_diag_norm_bound_at_radius f a R M hR hM p hf hbound k w r'
      hr'_pos hr'_lt_R
  -- The function `r' ↦ M · (‖w‖ / r')^k` is continuous at `R`.
  -- Composition: const ↦ `M` × ((const `‖w‖` / id) ^ k).
  have hg_cont : ContinuousAt (fun r' : ℝ => M * (‖w‖ / r') ^ k) R := by
    refine continuousAt_const.mul ?_
    exact ((continuousAt_const.div continuousAt_id hR_ne).pow k)
  -- Tendsto along `𝓝[<] R` lands at the boundary value.
  have h_tendsto :
      Filter.Tendsto (fun r' : ℝ => M * (‖w‖ / r') ^ k)
        (𝓝[<] R) (𝓝 (M * (‖w‖ / R) ^ k)) :=
    hg_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- The open interval `(0, R)` is eventually in `𝓝[<] R` (and nonempty since
  -- `R > 0`), so the pointwise bound holds eventually along the filter.
  have h_Ioo_mem : Set.Ioo (0 : ℝ) R ∈ 𝓝[<] R := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioi 0, isOpen_Ioi, hR, ?_⟩
    rintro x ⟨hx_pos, hx_lt_R⟩
    exact ⟨hx_pos, hx_lt_R⟩
  have h_event :
      ∀ᶠ r' in 𝓝[<] R, ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k :=
    Filter.eventually_of_mem h_Ioo_mem h_at_r
  -- Transport the eventual lower bound through the limit (`ge_of_tendsto` lifts
  -- a lower bound on `f c` to a lower bound on `lim f`).
  exact ge_of_tendsto h_tendsto h_event

/-- **Corrected Cauchy uniform bound** (complex hypothesis, fixed index).

For `f : ℂ → ℂ` holomorphic on `Metric.ball a R` (the open complex disk
of radius `R` around `a`) with uniform sup bound `‖f z‖ ≤ M` on that
disk, and any `0 < r < R`, the *degree-(n+1) truncated* partial sum of
the formal power series of `f` at `a` satisfies
```
  ‖f z − p.partialSum (n + 1) (z − a)‖ ≤ M · r^(n+1) / (R^n · (R − r))
```
for every `z` with `‖z − a‖ ≤ r` and every `n : ℕ`.

This is the textbook Cauchy uniform bound. The `n + 1` in
`partialSum (n + 1)` is the **degree** of the truncated polynomial
(matching the parent's `taylorPolynomial f a n` convention), so the
tail begins at degree `n + 1` and the geometric sum
`∑_{k ≥ n+1} M · (r/R)^k = M · (r/R)^(n+1) · R/(R−r) =
M · r^(n+1) / (R^n · (R − r))` (via `geometric_tail_identity`).

**Proof (S4, this iteration; sorry-free as of S7).** The combination is
formalized in full. It calls the Cauchy coefficient bound
`cauchy_diag_norm_bound`, which as of S4 was itself closed under a
`sorry`; that gap was fully discharged at S7 (2026-05-14). The proof
chains:

1. `HasFPowerSeriesOnBall.hasSum_sub` (Mathlib): from `z` in the
   `EMetric.ball a (ENNReal.ofReal R)`, get
   `HasSum (fun k ↦ p k (fun _ ↦ z − a)) (f z)`.
2. `cauchy_diag_norm_bound` (this file, sorry): for every `k`,
   `‖p k (fun _ ↦ (z − a))‖ ≤ M · (‖z − a‖ / R)^k ≤ M · (r / R)^k`.
3. `norm_sub_le_of_geometric_bound_of_hasSum` (Mathlib): combine 1 + 2 at
   index `n + 1` to bound `‖partialSum (n+1) − f z‖ ≤ M · (r/R)^(n+1) / (1 − r/R)`.
4. Algebraic identity `(r/R)^(n+1) / (1 − r/R) = r^(n+1) / (R^n · (R−r))`
   (a rescaling of `geometric_tail_identity`) plus `norm_sub_rev` give the
   final stated bound. -/
theorem analytic_taylor_remainder_uniform_bound_complex
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    (n : ℕ) (z : ℂ) (hz : ‖z - a‖ ≤ r) :
    ‖f z - p.partialSum (n + 1) (z - a)‖ ≤ M * r ^ (n + 1) / (R ^ n * (R - r)) := by
  -- Setup: arithmetic preconditions.
  have hzR : ‖z - a‖ < R := lt_of_le_of_lt hz hrR
  have hRr_pos : 0 < R - r := sub_pos.mpr hrR
  have hrR_lt_one : r / R < 1 := (div_lt_one hR).mpr hrR
  have hrR_nn : 0 ≤ r / R := div_nonneg hr.le hR.le
  have hR_ne : (R : ℝ) ≠ 0 := ne_of_gt hR
  have hRr_ne : (R - r : ℝ) ≠ 0 := ne_of_gt hRr_pos
  have hRn_ne : (R : ℝ) ^ n ≠ 0 := pow_ne_zero _ hR_ne
  -- Step 1: `z ∈ EMetric.ball a (ENNReal.ofReal R)` (the hypothesis of `hasSum_sub`).
  have hz_eball : z ∈ EMetric.ball a (ENNReal.ofReal R) := by
    rw [EMetric.mem_ball, edist_dist, dist_eq_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hzR
  -- Step 2: `HasSum` of the diagonal series to `f z`.
  have hsum : HasSum (fun k : ℕ => p k fun _ => z - a) (f z) :=
    hf.hasSum_sub hz_eball
  -- Step 3: per-term geometric bound `‖p k (fun _ ↦ (z-a))‖ ≤ M · (r/R)^k`.
  have hterm : ∀ k, ‖p k fun _ => z - a‖ ≤ M * (r / R) ^ k := by
    intro k
    have h_cauchy := cauchy_diag_norm_bound f a R M hR hM p hf hbound k (z - a) hzR
    have hwR_nn : 0 ≤ ‖z - a‖ / R := div_nonneg (norm_nonneg _) hR.le
    have hwR_le : ‖z - a‖ / R ≤ r / R := by gcongr
    have hpow : (‖z - a‖ / R) ^ k ≤ (r / R) ^ k := by gcongr
    calc ‖p k fun _ => z - a‖
        ≤ M * (‖z - a‖ / R) ^ k := h_cauchy
      _ ≤ M * (r / R) ^ k := by
          exact mul_le_mul_of_nonneg_left hpow hM
  -- Step 4: apply `norm_sub_le_of_geometric_bound_of_hasSum` at index `n + 1`.
  have htail :=
    norm_sub_le_of_geometric_bound_of_hasSum hrR_lt_one hterm hsum (n + 1)
  -- `htail : ‖(∑ k ∈ range (n+1), p k (fun _ ↦ (z-a))) - f z‖ ≤ M * (r/R)^(n+1) / (1 - r/R)`
  -- Step 5: rewrite the LHS finite sum as `p.partialSum (n+1) (z - a)`.
  have h_partialSum :
      (∑ k ∈ Finset.range (n + 1), p k fun _ => z - a)
        = p.partialSum (n + 1) (z - a) := by
    rfl
  rw [h_partialSum] at htail
  -- Step 6: `‖partialSum (n+1) − f z‖ = ‖f z − partialSum (n+1)‖`.
  rw [norm_sub_rev] at htail
  -- Step 7: rewrite the RHS `M * (r/R)^(n+1) / (1 - r/R)` to `M * r^(n+1) / (R^n * (R-r))`.
  -- We use the already-proven `geometric_tail_identity` and a careful chain of
  -- associativity rewrites — `field_simp + ring` here leaves stray `R⁻¹^n` factors
  -- that `ring` cannot combine.
  have h_rhs_eq :
      M * (r / R) ^ (n + 1) / (1 - r / R) = M * r ^ (n + 1) / (R ^ n * (R - r)) := by
    have h_geo := geometric_tail_identity r R hR hrR n
    -- h_geo : (r / R) ^ (n + 1) * R / (R - r) = r ^ (n + 1) / (R ^ n * (R - r))
    have h1r : (1 - r / R : ℝ) = (R - r) / R := by field_simp
    calc M * (r / R) ^ (n + 1) / (1 - r / R)
        = M * (r / R) ^ (n + 1) / ((R - r) / R) := by rw [h1r]
      _ = M * (r / R) ^ (n + 1) * R / (R - r) := by rw [div_div_eq_mul_div]
      _ = M * ((r / R) ^ (n + 1) * R) / (R - r) := by rw [mul_assoc]
      _ = M * ((r / R) ^ (n + 1) * R / (R - r)) := by rw [mul_div_assoc]
      _ = M * (r ^ (n + 1) / (R ^ n * (R - r))) := by rw [h_geo]
      _ = M * r ^ (n + 1) / (R ^ n * (R - r)) := by rw [← mul_div_assoc]
  rw [h_rhs_eq] at htail
  exact htail

/-! ## §3a. Existential Cauchy-style geometric approximation (S2 addition, proven)

This is the Mathlib-native translation of
`HasFPowerSeriesOnBall.uniform_geometric_approx'` from its `y`-centered
form `f (a + y)` (with `y` in a ball around `0`) to a `z`-centered form
(with `z` in a ball around `a`). The translation is purely a change of
variables `y = z − a`; no new mathematics, but it packages the Mathlib
lemma in a form that is more directly usable for downstream consumers
who reason about `z ∈ Metric.ball a r` rather than `y ∈ Metric.ball 0 r`.

The existential constants `K ∈ (0, 1)` and `C > 0` come from Mathlib's
internal Cauchy + geometric-tail combination and depend on the formal
multilinear series `p` (and the gap between `r` and the convergence
radius `R`), not on a user-supplied complex sup bound `M`. The sharper
explicit form (with `K = ‖z − a‖ / r`, `C = M · R / (R − r)`, requiring
`‖f‖ ≤ M` on `Metric.ball a R`) is left as the §3b `sorry` above; it
requires the Cauchy integral formula chain (`Complex.norm_cauchyPowerSeries_le`
+ `DifferentiableOn.hasFPowerSeriesOnBall`), which is heavier machinery
than `uniform_geometric_approx'` alone. -/

/-- **Existential Cauchy-style geometric approximation, complex
hypothesis** (S2 addition, proven via Mathlib's
`HasFPowerSeriesOnBall.uniform_geometric_approx'`).

For any `f : ℂ → ℂ` admitting a formal power series expansion `p` on
the disk `Metric.ball a R`, and any `r' < R`, there exist constants
`K ∈ (0, 1)` and `C > 0` such that on the strict subdisk
`Metric.ball a r'`, the residual after the `n`-th partial sum decays
geometrically in `n`:
```
  ‖f z − p.partialSum n (z − a)‖ ≤ C · (K · (‖z − a‖ / r'))^n.
```
This is precisely Mathlib's `uniform_geometric_approx'` after the
change of variables `z = a + y`. It does **not** require a complex sup
bound `‖f‖ ≤ M` on the disk — only that `f` admits the power-series
expansion (which is automatic for `f` complex-differentiable on the
closed disk, via `DifferentiableOn.hasFPowerSeriesOnBall`).

Pairing with the §3b `sorry`: the §3b explicit form
`M · r^(n+1) / (R^n · (R − r))` strengthens this existential by
identifying `C` and `K` with the explicit Cauchy constants, but
requires the sup bound `‖f‖ ≤ M` on the complex disk (the hypothesis
the parent OQ-04 axiom drops; cf. §2's refutation). -/
theorem analytic_taylor_remainder_uniform_geometric_complex
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {a : ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p a R) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < R) :
    ∃ K ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0,
      ∀ z ∈ Metric.ball a (r : ℝ), ∀ n,
        ‖f z - p.partialSum n (z - a)‖ ≤ C * (K * (‖z - a‖ / r)) ^ n := by
  obtain ⟨K, hK, C, hC, hp⟩ := hf.uniform_geometric_approx' hr
  refine ⟨K, hK, C, hC, fun z hz n => ?_⟩
  have hy : z - a ∈ Metric.ball (0 : ℂ) (r : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    rwa [Metric.mem_ball, dist_eq_norm] at hz
  have key := hp (z - a) hy n
  have h_simp : a + (z - a) = z := by ring
  rw [h_simp] at key
  exact key

/-! ## §4. Verification -/

#check @runge
#check @runge_analyticOn_R
#check @runge_abs_le_one
#check @runge_zero
#check @runge_one
#check @oq04_axiom_is_false
#check @oq04_parent_axiom_is_false_in_principle
#check @OriginalRemainderForm
#check @originalRemainderForm_is_false
#check @geometric_tail_identity
#check @cauchy_diag_norm_bound_at_radius
#check @cauchy_diag_norm_bound
#check @analytic_taylor_remainder_uniform_bound_complex
#check @analytic_taylor_remainder_uniform_geometric_complex

end MeanValueTheoremOQ02OQ04OQ01
