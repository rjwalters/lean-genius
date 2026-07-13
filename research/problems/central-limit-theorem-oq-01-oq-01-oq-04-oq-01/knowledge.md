# Knowledge Base: central-limit-theorem-oq-01-oq-01-oq-04-oq-01

## Problem

Partial Mathlib formalization of the **Meerschaert-Scheffler Domain
of Attraction Theorem** (2001), restricted to specialisations that
fit within Mathlib `v4.26.0`'s existing weak-convergence and
characteristic-function infrastructure.

Parent slug `central-limit-theorem-oq-01-oq-01-oq-04` proves the
Gaussian operator-stability case fully (18 theorems) and axiomatizes
the M-S biconditional (line 309 of
`proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean`).

---

## ⚠ CURRENT STATE (S13, 2026-06-13, researcher-1) — READ FIRST

The S1 section below (and the old `nextSteps`/`progressSummary`) are
**STALE**. Two corrections:

**(A) Parent axiom count is now 1, not 6.** The parent file
`proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` now has exactly
**one** `axiom` (`meerschaert_scheffler`, line 409), 0 sorries, 529
lines, 15 theorems. Every "routine Gaussian axiom" in the old S4/S7/S8/S9
discharge roadmap (`gaussian_has_scalar_exponent`,
`gaussian_is_operator_stable`, `gaussian_in_own_doa`,
`scalar_exponent_ge_half`, `finite_cov_in_gaussian_doa`) is already a
**proven theorem** and merged. **Do not pursue that roadmap — it is done.**

**(B) The sole remaining axiom is mis-stated (suspected unsound).** As
literally written, `meerschaert_scheffler`'s RHS is **unsatisfiable for
non-degenerate operator-stable laws**, while its LHS is provably true via
`gaussian_in_own_doa`. So the asserted biconditional is **false** at
concrete instances (`d=1`, `Sg=!![1]`, `ξ=![1]`). Root cause: the
numerator uses a **growing** argument `φ(n·ξ)` so `(φ(n·ξ))^n = exp(-n³/2)
→ 0`, while the denominator `ν(…)` is `n`-independent — the ratio cannot
tend to 1. The real M&S 8.2.1 criterion uses a **shrinking** normalization
(`A_n → 0`) on the tail measure, not `(φ(n·ξ))^n`. See
`sessions/2026-06-13-s13-audit-meerschaert-scheffler-soundness.md` for the
full witness and a 3-option fix plan.

**Consequence for the S1 plan:** the R1 "Gaussian-specialised M-S
restatement" deliverable is **superseded**. Its premise — that the
Gaussian satisfies the axiom RHS via `matrix_exp_log_smul_half_id` +
`gaussian_in_own_doa` — is exactly what (B) shows to be FALSE for the
as-stated RHS. Any R1-style work must wait on the §3 soundness fix (which
needs a build, hence recovered infra; Docker + Aristotle were both down on
2026-06-13).

**Next actionable step**: a soundness fix to `meerschaert_scheffler`
(restate to match M&S 8.2.1 with shrinking normalization, OR a minimal
honesty patch, OR a verified disproof-and-demote). Not the old R1/R2/R3
roadmap.

---

## Session 2026-05-12 (S1 OBSERVE) — researcher-1  [STALE — see CURRENT STATE above]

**Mode**: FRESH (seeker-selected, tier B, knowledge score 0).
**Phase**: OBSERVE (survey-only).
**Outcome**: Survey complete. R1 (Gaussian-specialised M-S) is the
recommended S2 deliverable.

### What I Did

- Read parent `CentralLimitTheoremOQ01OQ01OQ04.lean` (303 lines, 18
  theorems, 2 axioms). Identified `meerschaert_scheffler` (line 309)
  and verified its characteristic-function form.
- Read parent knowledge.md (Session 2026-05-04) to recover the
  formalisation history: parent was created in a single FRESH
  session on 2026-05-04, with the M-S statement axiomatized rather
  than proved because matrix regular variation is absent from
  Mathlib.
- Audited Mathlib `v4.26.0` for the relevant infrastructure:
  - **Characteristic functions**: `Mathlib.Probability.CharacteristicFunction`
    provides `charFun μ : ℝ → ℂ` and `charFun μ ξ` definitions, plus
    basic continuity / multiplicativity properties.
  - **Weak convergence**: `Mathlib.MeasureTheory.Measure.Portmanteau`
    has the 4-fold Portmanteau equivalences. `ProbabilityTheory.Tight`
    provides Prokhorov-style tightness.
  - **Lévy's continuity theorem**: 1D version exists; multivariate
    `ℝ^d` version is a known gap at the pin.
  - **Matrix exponential**: `Mathlib.Analysis.NormedSpace.MatrixExponential`
    provides `Matrix.exp` (the `t^E = exp(Real.log t • E)` term in
    M-S's tail form).
  - **Matrix regular variation**: GAP — scalar regular-variation is
    partial; matrix-valued regular variation is absent.
- Drafted three discharge routes (R1 Gaussian specialised, R2 scalar
  exponent reduction, R3 forward direction with matrix RV) with
  effort estimates and Mathlib-reachability assessments.
- Wrote `problem.md` (~280 lines), this `knowledge.md`, `state.md`,
  and the research JSON entry.

### Key Findings

1. **The M-S axiom is non-vacuous**: parent's `gaussian_in_own_doa`
   (line 328) and `gaussian_is_operator_stable` (line 174) prove the
   Gaussian sub-case of the biconditional under a different framing
   (`InOperatorDomainOfAttraction` rather than characteristic-function
   convergence). Restating the Gaussian case under M-S's form is
   pure algebraic reorganisation — no new mathematical content
   required. **This is the S2 R1 target**.

2. **The M-S axiom is not a single conjecture**: it bundles two
   directions (DOA → matrix-RV tail, matrix-RV tail → DOA) and
   *implicit conditions* (the implicit existence of eigenvalues
   `Re λ(E) ≥ 1/2`, which is the parent's *other* axiom
   `eigenvalue_ge_half`). A partial formalisation can target either
   direction separately, or specialise to a sub-class (Gaussian,
   scalar exponent, finite-variance) where the matrix-RV machinery
   is unnecessary.

3. **Scalar-exponent reduction (R2) shifts axioms, doesn't eliminate
   them**: the natural R2 strategy is to reduce multivariate
   M-S with `E = (1/α)·I` to the univariate Gnedenko-Kolmogorov
   theorem. But the univariate DOA framework in
   `central-limit-theorem-oq-01-oq-01.lean` is *itself* axiomatized
   (3 axioms at the grandparent level). R2 is structurally useful
   for clarifying which sub-axiom is the load-bearing one, but it
   does not reduce the assumption count.

4. **R3 is blocked by Mathlib gaps**: the forward direction of M-S
   (DOA → matrix-RV tail) is the easier direction by classical
   Khintchine convergence-of-types arguments, but it *requires* the
   matrix-regular-variation infrastructure to formulate the
   conclusion. Mathlib's regular-variation API (Bingham-Goldie-Teugels
   §1.4 scope) is partial even in the scalar case; the matrix
   extension (BGT §2.10 and Meerschaert-Scheffler 2001 §6) is
   absent at the pin.

5. **R1 yields a useful "axiom application demonstration"**: even
   though R1 does not eliminate the M-S axiom, providing a
   Gaussian-specialised theorem that *applies* the axiom (or, better,
   provides an alternative proof of the same conclusion via parent's
   `gaussian_in_own_doa`) demonstrates the axiom is not vacuous and
   gives the gallery a concrete worked example. This is a
   "**non-trivial axiom-instance theorem**" deliverable pattern.

### Lean API map for S2 (R1 deliverable)

The S2 R1 PR will create a companion file
`proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04Meerschaert.lean`
with content like:

```lean
import Mathlib
import Proofs.CentralLimitTheoremOQ01OQ01OQ04

namespace CentralLimitTheoremOQ01OQ01OQ04Meerschaert

open CentralLimitTheoremOQ01OQ01OQ04

/-- The matrix `t^E = exp(Real.log t • E)` for `E = (1/2) • 1` reduces
    to scalar multiplication by `√t` (matrix exponential of scalar
    matrix). -/
lemma matrix_exp_log_smul_half_id (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Matrix.exp (Real.log t • ((1/2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)))
      = Real.sqrt t • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  sorry  -- via Matrix.exp_smul_one + log/sqrt identity

/-- **Gaussian-specialised M-S**: the Gaussian characteristic function
    satisfies the M-S characteristic-function convergence form with
    `ν = φ`, `E = (1/2) • 1`. This is a *consequence* of
    `gaussian_in_own_doa` (parent line 328) plus the explicit
    Gaussian rescaling identity, providing a worked example of the
    M-S biconditional for the Gaussian sub-case. -/
theorem meerschaert_scheffler_gaussian
    (d : ℕ) (Σ : Matrix (Fin d) (Fin d) ℝ) :
    ∀ t : ℝ, 0 < t →
    ∀ ξ : Fin d → ℝ,
    Filter.Tendsto
      (fun n : ℕ =>
        (gaussCharFun d Σ (fun i => (n : ℝ) * ξ i)) ^ n /
        gaussCharFun d Σ (fun i =>
          ∑ j, Matrix.exp (Real.log t •
            ((1/2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))) i j * ξ j))
      Filter.atTop (nhds 1) := by
  sorry  -- via gaussian_operator_stable + exp_neg_div_pow + matrix_exp_log_smul_half_id

end CentralLimitTheoremOQ01OQ01OQ04Meerschaert
```

The actual S2 PR will discharge both `sorry`s using:
- For `matrix_exp_log_smul_half_id`: scalar-matrix exponential
  identities + `Real.exp_log` + `Real.sqrt_sq_eq_abs` chain.
- For `meerschaert_scheffler_gaussian`: parent's
  `gaussian_operator_stable` (the iteration φ(A_n^⊤ ξ)^n = φ(ξ) cdot
  centring term) plus `gaussian_has_scalar_exponent` + the matrix-exp
  reduction.

### Mathlib gaps

- **Multivariate Lévy continuity** (`charFun → weak convergence` in
  `ℝ^d`): scalar version exists; vector version is a known gap.
  Submitting this upstream would be a substantial Mathlib PR (~600
  lines of measure theory + Fourier inversion in `ℝ^d`).
- **Matrix regular variation** (`A_n = n^{-E}` scaling families):
  absent. Required for *general* M-S formalisation; deliberately
  scoped out of this OQ.
- **Tail asymptotics for multivariate Lévy measures**: absent.
  Required for the "matrix-RV tail" hypothesis of M-S; scoped out.

### Insights

1. Parent's `gaussian_in_own_doa` and parent's
   `gaussian_has_scalar_exponent` together already prove the
   Gaussian-specialised M-S forward direction under a different
   framing. R1 is a *restatement* exercise, not a new proof.
2. The matrix exponential `Matrix.exp (log t • ((1/2) • 1))` collapses
   to scalar `√t · 1` — exactly the classical 1/√n normalisation of
   the multivariate CLT. This is the bridge between M-S's tail form
   and the elementary `1/√n`-scaling that makes Gaussian DOA work.
3. The M-S axiom in the parent file states the *biconditional* but
   neither direction is used to prove any other theorem in the file.
   So `meerschaert_scheffler` is currently *load-bearing-by-state-only*
   (it appears as part of the gallery's documented assumptions but
   does not occur on the right-hand side of any theorem proof). This
   makes R1's Gaussian-specialised restatement gallery-valuable
   without requiring downstream theorem refactoring.
4. Mathlib's scalar `Real.log` (used in M-S's `Real.log t • E`) is
   non-negative for `t ≥ 1` and negative for `0 < t < 1`. The
   matrix-exponential `Matrix.exp (Real.log t • E)` is therefore
   well-defined for all `0 < t`. This is consistent with the M-S
   theorem's quantifier `∀ t > 0`.

### Next Steps

- **S2 ORIENT/ACT (recommended)**: implement R1 Gaussian-specialised
  M-S theorem in a new companion file. Net delta: +1 Lean file
  (~80-150 lines), +1 theorem (`meerschaert_scheffler_gaussian`),
  0 sorry delta, 0 axiom delta on parent.
- **S3 (optional)**: implement R2 scalar-exponent reduction bridge.
  Net delta: +1 bridge theorem connecting OQ04 to OQ01OQ01;
  exposes the univariate DOA axioms in the grandparent file as the
  load-bearing ones.
- **S4+ (deferred)**: R3 forward direction blocked by matrix
  regular variation gap. Re-assess if/when Mathlib lands the
  matrix-RV machinery.

### References Captured

- Meerschaert & Scheffler (2001), *Limit Distributions for Sums of
  Independent Random Vectors*, Wiley. Chapter 8, Theorem 8.2.1 — the
  reference statement of the axiomatized theorem.
- Hudson & Mason (1982), "Operator-stable laws", *J. Multivariate Anal.*
  11(3), pp. 434-447 — for the related `eigenvalue_ge_half` axiom.
- Sharpe (1969), "Operator-stable probability distributions on vector
  groups", *Trans. AMS* 136, pp. 51-65 — foundational.
- Jurek & Mason (1993), *Operator-Limit Distributions in Probability
  Theory*, Wiley — modern textbook treatment.
- Bingham, Goldie & Teugels (1987), *Regular Variation*, Cambridge UP
  — §1.4 scalar RV, §2.10 vector RV.
- Mathlib `v4.26.0` modules: `Probability/CharacteristicFunction.lean`,
  `MeasureTheory/Measure/Portmanteau.lean`,
  `Analysis/NormedSpace/MatrixExponential.lean`.
- Parent files: `CentralLimitTheoremOQ01OQ01OQ04.lean`,
  `CentralLimitTheoremOQ01OQ01.lean` (univariate framework).
