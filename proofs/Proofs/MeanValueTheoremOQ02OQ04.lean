import Mathlib
import Proofs.MeanValueTheoremOQ02

/-!
# Mean Value Theorem OQ-02 / OQ-04: RETRACTED Cauchy uniform Taylor remainder bound

## The Open Question (OQ-04 of `mean-value-theorem-oq-02`)

> Is there a uniform error bound formalization: for all `x ∈ [a − r, a + r]`
> and `f` analytic on the disk of radius `R > r`,
>   `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)`?
> This uniform version is used in complex analysis and approximation theory.

## Status: **RETRACTED**

The S1 iteration of this slug (researcher-3, 2026-05-11, PR #17705) introduced
the OQ-04 statement as an `axiom analytic_taylor_remainder_uniform_bound`,
together with a one-line `n = 0` corollary `analytic_remainder_zero_bound`.

The child slug `mean-value-theorem-oq-02-oq-04-oq-01` (researcher-6,
PR #17837 merged 2026-05-12) subsequently proved that this axiom is
**mathematically false** by constructing an explicit Runge counterexample
(`oq04_axiom_is_false` in `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`):

  Witness `(f, a, R, M, r, n, x) = (runge, 0, 100, 1, 1, 0, 1)`:
  * `runge x := 1 / (1 + x²)` is real-analytic on `(−100, 100)`.
  * `|runge y| ≤ 1` uniformly on `(−100, 100)`.
  * `|runge 1 − runge 0| = |1/2 − 1| = 1/2`.
  * Axiom's claimed bound: `1 · 1^1 / (100 − 1) = 1/99`.
  * `1/2 > 1/99`, contradicting the axiom.

The mathematical root cause is the **Runge phenomenon**: a *real* sup bound
`M` on `f` over `(a − R, a + R) ⊂ ℝ` does *not* control the Cauchy
coefficient bounds `|f^{(k)}(a) / k!| ≤ M / R^k`, because the real-analytic
function `1 / (1 + x²)` extends only to the *complex* disk of radius `1`
around `0` (with poles at `±i`), even though it is real-analytic and
uniformly bounded by `1` on all of `ℝ`. Cauchy-style geometric-tail
estimates of the form `M · r^(n+1) / (R − r)` require the sup bound to apply
on the *complex* disk `D(a, R) ⊂ ℂ`, not merely on the real interval.

## Action taken (S2, researcher-8, 2026-05-14)

Both the false axiom and the false-by-inheritance `n = 0` theorem are
**removed** from this file. The file is now a doc-only stub preserving
the namespace and providing cross-references to:

* The constructive refutation in
  `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`
  (theorem `oq04_axiom_is_false`).
* The **corrected statement** in that same child file
  (theorem `analytic_taylor_remainder_uniform_bound_complex`),
  which strengthens the hypothesis to `HasFPowerSeriesOnBall f p a R`
  on a **complex** disk. As of S7 (2026-05-14, child PR #23192) this is
  **fully proven and sorry-free** at v4.26.0: the finite-radius sub-lemma
  `cauchy_diag_norm_bound_at_radius` (the last residual `sorry`) was
  discharged via Mathlib's
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.

Removing the axiom eliminates a gallery-integrity bug (a `False`-witness
in the build closure): any downstream consumer that imports
`Proofs.MeanValueTheoremOQ02OQ04` and `Proofs.MeanValueTheoremOQ02OQ04OQ01`
together could otherwise have derived `False` via
`oq04_axiom_is_false (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
analytic_taylor_remainder_uniform_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _)`.

## What this file currently contains

Just this docstring plus an empty namespace. **No axioms, no theorems,
no definitions, no sorries.** The slug's mathematical content lives
entirely in the corrected complex-form theorem in the child slug's file.

## Gallery integrity bookkeeping

* `axiomCount`: 1 → 0 (false axiom removed).
* `theoremCount`: 1 → 0 (false-by-inheritance corollary removed).
* `sorries`: 0 (unchanged).
* `definitionCount`: 0 (unchanged).
* `lineCount`: 173 → ~90 (mostly retraction docstring).

## Connection to sibling gallery entries

* **Parent** `mean-value-theorem-oq-02` (Taylor's theorem with Lagrange
  remainder): unchanged. Provides `taylorPolynomial`,
  `taylorPolynomial_zero`, and the *true* `taylor_lagrange_remainder`
  axiom (qualitative pointwise Lagrange remainder).
* **Child** `mean-value-theorem-oq-02-oq-04-oq-01`: refutes this slug's
  S1 axiom and states the corrected complex-disk form.
* **Cousin** `taylor-theorem-oq-02` (`taylor_remainder_tendsto_zero`):
  unchanged. The qualitative `R_n(x) → 0` for analytic `f` does *not*
  fall to the Runge phenomenon (the convergence does not require a real
  sup bound).

## Path forward

This slug should be **closed** in favor of `mean-value-theorem-oq-02-oq-04-oq-01`,
which carries the mathematically correct version. A future iteration may
choose to:

  (a) keep this slug as a doc-only retraction record (current state), or
  (b) delete the file outright (after updating `Proofs.lean` and the
      gallery `meta.json` to point to the child slug).

The deployer / curator should decide between (a) and (b); option (a) is
chosen here to preserve a permanent record of the refutation for
pedagogical / audit purposes.

## References

* Refutation: `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` §2.
* Corrected complex-disk Cauchy bound:
  `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` §3.
* Runge phenomenon: Runge, C. (1901). "Über empirische Funktionen und
  die Interpolation zwischen äquidistanten Ordinaten." Z. Math. Phys.
  46, 224–243.
-/

namespace MeanValueTheoremOQ02OQ04

/- Intentionally empty: the S1 axiom `analytic_taylor_remainder_uniform_bound`
   and the S1 derived theorem `analytic_remainder_zero_bound` were retracted
   in S2 (researcher-8, 2026-05-14) following the constructive refutation in
   the child slug `mean-value-theorem-oq-02-oq-04-oq-01`. See file docstring
   for the full retraction record.

   The corrected complex-disk Cauchy bound is stated and (as of S7,
   2026-05-14, child PR #23192) fully proven sorry-free in
   `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` as
   `analytic_taylor_remainder_uniform_bound_complex`. Consumers should
   import that file directly. -/

end MeanValueTheoremOQ02OQ04
