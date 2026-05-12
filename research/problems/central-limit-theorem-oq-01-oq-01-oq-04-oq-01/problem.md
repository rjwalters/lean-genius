# Problem: Partial Mathlib Formalization of the Meerschaert-Scheffler DOA Theorem

**Slug**: `central-limit-theorem-oq-01-oq-01-oq-04-oq-01`
**Parent**: `central-limit-theorem-oq-01-oq-01-oq-04` —
*Multivariate Operator-Stable Distributions and Matrix Domain of
Attraction*. Status `axiomatized`, badge `axiom`, 2 axioms, 18
theorems, ~303 lines (`proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean`).
**Grandparent**: `central-limit-theorem-oq-01-oq-01` (univariate CLT
+ DOA framework, 3 axioms).

## Plain Statement

The parent file proves Gaussian operator-stability over `ℝ^d`
fully (18 theorems), and frames the multivariate domain of
attraction problem. Two axioms remain:

- `eigenvalue_ge_half` (Hudson-Mason 1982 spectral bound — out of
  scope for this OQ).
- **`meerschaert_scheffler`** (Meerschaert-Scheffler 2001 DOA
  biconditional — this OQ's target).

The axiom statement (lines 309–319 of the parent file) is the
characteristic-function form of the Meerschaert-Scheffler theorem:

```lean
axiom meerschaert_scheffler (d : ℕ) (φ : (Fin d → ℝ) → ℂ) :
    (∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ) ↔
    ∃ (E : Matrix (Fin d) (Fin d) ℝ) (ν : (Fin d → ℝ) → ℂ),
      ∀ t : ℝ, 0 < t →
      ∀ ξ : Fin d → ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          (φ (fun i => (n : ℝ) * ξ i)) ^ n /
          ν (fun i => ∑ j, Matrix.exp (Real.log t • E) i j * ξ j))
        Filter.atTop (nhds 1)
```

**The open question** asks: *Can this biconditional be partially
formalized in Lean 4 / Mathlib `v4.26.0`, using Mathlib's existing
weak-convergence, characteristic-function, and Lévy-continuity
infrastructure?* — without requiring the matrix-regular-variation
machinery that Mathlib genuinely lacks.

The realistic deliverable target is **one direction** of the
biconditional in a **specialised form** (e.g. the Gaussian-DOA
case, or the scalar-exponent specialisation `E = (1/α)·I` reducing
to the univariate Gnedenko-Kolmogorov theorem).

## Why this Matters

1. **Axiom elimination on a gallery entry.** Replacing
   `meerschaert_scheffler` with a (possibly partial) theorem would
   drop the parent's `axiomCount` from 2 to 1 (or to 0 if
   `eigenvalue_ge_half` is later closed). Reducing axiom counts on
   operator-stable theory is high-leverage because the slug feeds
   the wider CLT family (`central-limit-theorem-oq-01-oq-01`,
   `central-limit-theorem-oq-02-*`, `central-limit-theorem-oq-03-*`).

2. **First Mathlib bridge from univariate to multivariate DOA.**
   Mathlib already has Lévy's continuity theorem for ℝ
   (`MeasureTheory.LevyContinuity` style results) and partial
   characteristic-function infrastructure. Even a 1-D-to-d-D bridge
   lemma (the *forward direction* of M-S restricted to scalar
   exponents `E = (1/α)·I`) would be a publishable bridge.

3. **Specialisation to Gaussian operator-stability has full proof.**
   The parent file proves `gaussian_is_operator_stable` and
   `gaussian_in_own_doa` directly (theorems, not axioms). So the
   Gaussian sub-case of M-S is already proved in spirit; what
   remains is reformulating it under M-S's tail-condition statement.

4. **Bridges univariate alpha-stable embedding.** Parent's
   `alpha_stable_is_operator_stable` (line 211) reduces 1D α-stable
   theory to operator-stable theory via the scalar embedding
   `E = (1/α)·I`. The OQ04OQ01 question asks whether this embedding
   can be lifted from operator-stability ("invariance under
   `A_n^⊤ ξ`") to domain-of-attraction ("`φ(n·ξ)^n / ν` converges").

## Mathematical Specification

### B.1 The Meerschaert-Scheffler Theorem (Statement)

> **Theorem (Meerschaert-Scheffler 2001, Thm 8.2.1).** Let `μ` be a
> probability measure on `ℝ^d` with characteristic function `φ`.
> The following are equivalent:
>
> (i) `μ` lies in the operator domain of attraction of some
>     operator-stable law `ν`: there exist matrices `A_n ∈ GL(d, ℝ)`
>     and vectors `b_n ∈ ℝ^d` such that `A_n^{-1}(X_1 + ⋯ + X_n) - b_n`
>     converges weakly to `Y ~ ν`.
>
> (ii) The Lévy measure of `μ` has a *matrix regularly varying tail*:
>     there exists `E ∈ ℝ^{d×d}` with all eigenvalues having real part
>     `≥ 1/2`, and a slowly varying function `L`, such that for all
>     `t > 0` and `ξ ∈ ℝ^d ∖ {0}`,
>
>     `t · μ({x : ‖x‖ ≥ ‖t^E x‖}) → ‖x‖^(-?) · L(t)`  *(matrix-tail form)*.
>
> The characteristic-function reformulation (the axiom we have):
>
> `φ(n ξ)^n / ν(t^E ξ) → 1`  for all `t > 0`, `ξ ∈ ℝ^d` (after
> centring and scaling by `A_n = n^{-E}`).

For our OQ04OQ01 task we **deliberately restrict** to scenarios where
the matrix-regular-variation machinery (the "matrix tail" hypothesis
(ii)) can be specialised or bypassed.

### B.2 Three Specialisation Routes

| Route | Specialisation | Mathlib Reachable? | Effort |
|-------|----------------|--------------------|--------|
| **R1** | Gaussian → Gaussian DOA: `φ = gaussCharFun d Σ`, show `φ ∈ DOA(φ)` via the M-S characterisation. | YES (parent already has `gaussian_in_own_doa`; restate under M-S form). | ~30-80 Lean lines |
| **R2** | Scalar exponent: `E = (1/α)·I`, reduce to univariate α-stable DOA. Use parent's `alpha_stable_is_operator_stable` + univariate DOA framework (`central-limit-theorem-oq-01-oq-01.lean`). | PARTIAL: univariate DOA is itself axiomatized in the grandparent file. | ~150-300 Lean lines |
| **R3** | Forward direction only (`(i) → (ii)` of M-S): given DOA, derive the matrix-regular-variation tail. This is the *easier* direction by Khintchine convergence-of-types. | NO: needs matrix regular variation, not in Mathlib. | blocked |

**R1 is the recommended S2 target** — concrete, in-scope, immediate
gallery value (axiom→theorem on the Gaussian-DOA case at least).

### B.3 What Parent File Already Provides (toward R1)

| Existing decl | Line | Content |
|---------------|------|---------|
| `gaussCharFun d Σ` | ~70 | characteristic function of N(0, Σ) on ℝ^d |
| `gaussian_operator_stable` | 148 | `gaussCharFun ∈ IsOperatorStable d` |
| `gaussian_in_own_doa` | 328 | `gaussCharFun ∈ InOperatorDomainOfAttraction d (gaussCharFun)` |
| `gaussian_has_scalar_exponent` | 161 | Gaussian uses exponent matrix `E = (1/2)·I` |
| `quadForm_scale_inv_sqrt` | 99 | `quadForm(ξ/√n) = (1/n)·quadForm(ξ)` (heart of Gaussian stability) |
| `exp_neg_div_pow` | 135 | `(exp(-x/n))^n = exp(-x)` (the algebraic identity) |

For R1 (Gaussian-specialised M-S), the *forward* direction
`Gaussian DOA → characteristic-function convergence` is already
implicit in `gaussian_in_own_doa`. Restating it under the M-S
biconditional form (with the explicit `ν = gaussCharFun` and
`E = (1/2)·I`) is the S2 deliverable.

## Mathlib Infrastructure Map (pinned `v4.26.0`)

| Need | Mathlib Module | Status |
|------|----------------|--------|
| Weak convergence of probability measures | `Mathlib.MeasureTheory.Measure.Portmanteau` (4 implications, classical) | available |
| Characteristic function of a measure | `Mathlib.Probability.CharacteristicFunction` (`charFun μ`) | available |
| Lévy's continuity theorem (1D) | `Mathlib.Probability.Distributions.Gaussian` neighbourhood | partial — 1D version, multivariate gap |
| Lévy's continuity (multivariate) | — | **GAP** (the standard ℝ^d generalisation is missing at the pin) |
| Probability measure on ℝ^d | `MeasureTheory.Measure` + `Multivariate` modules | available |
| Matrix exponential `Matrix.exp` | `Mathlib.Analysis.NormedSpace.MatrixExponential` | available |
| `Matrix.exp` of `Real.log t • E` for tail-form | `Mathlib.Analysis.NormedSpace.MatrixExponential` | available |
| `Filter.Tendsto` to a `nhds 1` in `ℂ` | `Mathlib.Topology.Algebra.Order.LiminfLimsup` | available |
| Matrix regular variation (`A_n = n^{-E}`) | — | **GAP** (no matrix-regular-variation theory in Mathlib) |
| `Algebra.IsInvariant`, `arithFrobAt` (not used here, ruled out) | n/a | n/a |
| Operator-stable structures | parent file's `IsOperatorStable`, `InOperatorDomainOfAttraction` | available (parent-defined) |

**Crucial gaps** for a *general* M-S formalisation:
- Multivariate Lévy continuity theorem (Mathlib has scalar Lévy continuity).
- Matrix regular variation (slowly-varying functions are partial,
  matrix-valued regular variation is absent).
- Tail asymptotics of multivariate Lévy measures.

These gaps justify the OQ04OQ01 question's "partial" framing: a
full M-S is a 6-12 month Mathlib project, but a **Gaussian
specialisation** is one PR.

## Reference Reading

| # | Source | Why |
|---|--------|-----|
| 1 | Meerschaert, M. M.; Scheffler, H.-P. (2001). *Limit Distributions for Sums of Independent Random Vectors: Heavy Tails in Theory and Practice*. Wiley. Chapter 8, Theorem 8.2.1. | The reference theorem; the axiom in the parent file is its characteristic-function form. |
| 2 | Hudson, W. N.; Mason, J. D. (1982). "Operator-stable laws". *J. Multivariate Anal.* 11(3). | Original eigenvalue bound `Re λ(E) ≥ 1/2` — parent's other axiom. |
| 3 | Sharpe, M. (1969). "Operator-stable probability distributions on vector groups". *Trans. AMS* 136. | Foundational paper introducing operator-stable laws. |
| 4 | Jurek, Z.; Mason, J. D. (1993). *Operator-Limit Distributions in Probability Theory*. Wiley. | Modern textbook with both univariate and multivariate DOA results. |
| 5 | Bingham, Goldie, Teugels (1987). *Regular Variation*. Cambridge UP. §1.4 (scalar reg var) + §2.10 (vector). | Regular-variation tools; matrix RV is treated in extensions. |
| 6 | Mathlib `Probability/CharacteristicFunction.lean` | The Mathlib `charFun μ` API; 1D Lévy continuity. |
| 7 | Parent file `central-limit-theorem-oq-01-oq-01` (univariate DOA framework, 3 axioms). | Hand-off framework; R2 hooks into this. |

## Proposed Decomposition

| Session | Phase | Target | Lines (est.) |
|---------|-------|--------|--------------|
| **S1 (this)** | OBSERVE | Survey: M-S theorem, three specialisation routes (R1/R2/R3), Mathlib gap map, parent's Gaussian-side evidence. Markdown + JSON only. | 0 Lean / ~600 md+json |
| **S2** | ORIENT/ACT | **R1 (Gaussian specialised M-S)**: in a new companion file `CentralLimitTheoremOQ01OQ01OQ04Meerschaert.lean`, restate the M-S biconditional for `φ = gaussCharFun d Σ`, with `E = (1/2)·I` and `ν = gaussCharFun d Σ`. Both directions follow from `gaussian_in_own_doa` and `gaussian_has_scalar_exponent` (already proven). The deliverable is a Lean-level *application* of the axiom to a specific instance with a fully-derived alternative proof, demonstrating the axiom is not vacuous and yielding a *Gaussian-specialised M-S theorem*. | ~80-150 Lean |
| **S3** | ACT (alt R2) | **R2 (scalar exponent reduction)**: write a bridge lemma reducing the multivariate scalar-exponent M-S form to the univariate `central-limit-theorem-oq-01-oq-01.lean` framework. This depends on the univariate DOA axioms in the grandparent file, so the net axiom count does not drop (one axiom replaces another), but the *structure* is improved. | ~150-300 Lean |
| **S4+** | DEFER | **R3 (forward direction with matrix RV)** is blocked by missing Mathlib matrix-regular-variation machinery. Defer until that infrastructure lands upstream. | 0 |

The S2 R1 path is the **minimum tractable formalisation deliverable**
for this OQ. It does not eliminate `meerschaert_scheffler` (the full
axiom remains), but it produces a *Gaussian-specialised, fully proved
instance* of the M-S biconditional, demonstrating non-vacuity and
giving a concrete worked example.

## Honest Calibration

- **R1 risk**: low. The Gaussian sub-case is already proved (under a
  different framing) by `gaussian_in_own_doa`. The S2 work is mostly
  algebraic reorganisation of existing theorems.
- **R2 ambition**: medium. Reducing multivariate scalar-exponent M-S
  to univariate DOA is the standard Khintchine argument, but Mathlib's
  univariate DOA is itself axiomatized in the grandparent file. This
  *does not* eliminate axioms; it merely shifts the axiom location.
- **R3 viability**: blocked. The matrix-regular-variation machinery is
  a substantial Mathlib contribution that this OQ deliberately scopes
  *out*.

**The S1 OBSERVE output is doc-only — no Lean changes, no axiom delta.**
This is a survey iteration that prepares S2 (ACT) for a Gaussian-
specialised M-S theorem.

The realistic estimate for closing OQ04OQ01 is **1-2 more sessions**:
S2 produces R1's Gaussian specialisation; S3 (optional) produces R2's
scalar-exponent reduction. Neither eliminates the parent's
`meerschaert_scheffler` axiom in its full multivariate generality —
but together they document and verify the non-trivial sub-cases that
Mathlib *can* support at `v4.26.0`.
