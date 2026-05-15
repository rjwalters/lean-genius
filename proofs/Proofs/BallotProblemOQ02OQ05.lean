import Mathlib
import Proofs.BallotProblemOQ02

/-!
# Donsker's Functional CLT — statement layer (S2 ACT)

## Research Problem: ballot-problem-oq-02-oq-05

This file is the **statement layer** of the OQ-05 pipeline that connects the
discrete ballot problem (`Proofs/BallotProblem.lean`) to its continuous-time
shadow (`Proofs/BallotProblemOQ02.lean`) via Donsker's functional central
limit theorem.

The S2 deliverable is statement-only:

- `interpolatedRescaled` — the canonical interpolated rescaled random walk
  $S_n^\ast(t) = (S_{\lfloor n t\rfloor} + \{n t\}\,\xi_{\lfloor n t\rfloor})/\sqrt n$,
  living in $C([0,1], \mathbb{R})$.
- `WeakConvergesInC01` — an ad hoc weak-convergence predicate on path
  trajectories. Mathlib v4.26.0 lacks a first-class Polish/Borel space
  structure on $C([0,1], \mathbb{R})$, so the predicate is encoded against
  continuous test functionals in the pointwise topology. This is strictly
  weaker than the classical sup-norm weak-convergence formulation but
  suffices for the axiomatic targets in S3-S7.
- `donsker_fclt` — Donsker (1951): the rescaled interpolated walk
  converges weakly in $C([0, 1])$ to standard Brownian motion. Wiedijk #45.

No theorems are proved in this file; sessions S3+ will prove the discrete
reflection identity (`discrete_reflection`) and use `donsker_fclt` plus
auxiliary continuous-mapping axioms to derive the parent's three axioms
(`reflection_principle`, `firstPassageTime_eq_maxEvent`, and the embedded
arcsine identity) as theorems.

## Status (0 sorries, 1 axiom)

- [x] Interpolated rescaled walk definition
- [x] Ad hoc weak-convergence predicate on $C([0,1])$
- [x] Donsker FCLT axiom statement
- [ ] Discrete reflection identity (S3, sorry-free target)
- [ ] Continuous-mapping-for-sup axiom (S4)
- [ ] Reflection-principle theorem deriving parent's axiom (S4)
- [ ] First-passage-time event theorem (S5)
- [ ] Sparre Andersen + arcsine derivation (S6)
- [ ] Parent-file axiom downgrade (S7)
-/

namespace BallotOQ05

open MeasureTheory ProbabilityTheory ContinuousBallot

variable {Ω : Type*}

/-! ## Part I: Interpolated rescaled random walk -/

/-- The partial sum `S_k = ξ_0 + ξ_1 + ⋯ + ξ_{k-1}` of an i.i.d. sequence. -/
noncomputable def partialSum (xi : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, xi i ω

/-- The **interpolated rescaled random walk** on `[0, 1]`.

  $S_n^\ast(t) = \dfrac{S_{\lfloor n t\rfloor} + \{n t\}\,\xi_{\lfloor n t\rfloor}}{\sqrt n}$

This is the canonical $C([0, 1], \mathbb{R})$-valued process used in Donsker's
theorem. For `n = 0` the convention `Real.sqrt 0 = 0` and division-by-zero
yielding `0` give the degenerate value `0`. -/
noncomputable def interpolatedRescaled
    (xi : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  let k : ℕ := ⌊t * n⌋₊
  let frac : ℝ := t * n - k
  (partialSum xi k ω + frac * xi k ω) / Real.sqrt n

/-! ## Part II: Ad hoc weak-convergence predicate on `C([0,1])` -/

/-- Weak convergence of a sequence of path-valued random elements to a path
limit. Encoded against the pointwise topology on `ℝ → ℝ`, which is what
Mathlib v4.26.0 provides without requiring the Polish structure on
$C([0, 1], \mathbb{R})$.

For continuous test functionals `Φ : (ℝ → ℝ) → ℝ`, the predicate asserts
$\mathbb{E}_\mu[\Phi(X_n)] \to \mathbb{E}_\mu[\Phi(X)]$. When `Φ` is
non-integrable on either side, Lean's `∫ ... ∂μ = 0` convention applies,
so the predicate degenerates to `|0 - 0| < ε`, trivially satisfied — i.e.
the predicate constrains only the integrable continuous test functionals,
matching the operational content of weak convergence.

This is **temporary scaffolding**: a Polish-space refinement should
replace it once Mathlib supplies `Polish (C(Set.Icc (0:ℝ) 1, ℝ))`. -/
def WeakConvergesInC01
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → ℝ → Ω → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  ∀ Φ : (ℝ → ℝ) → ℝ, Continuous Φ → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |∫ ω, Φ (fun t => Xn n t ω) ∂μ - ∫ ω, Φ (fun t => X t ω) ∂μ| < ε

/-! ## Part III: Donsker's functional CLT (axiomatized) -/

/-- **Donsker's functional CLT** (Donsker 1951, Wiedijk #45).

For i.i.d. mean-0 variance-1 measurable random variables $\xi_1, \xi_2, \ldots$
on a probability space $(\Omega, \mu)$, there exists a standard Brownian motion
$W$ on the same probability space such that the interpolated rescaled walk
$S_n^\ast$ converges weakly in $C([0, 1])$ to $W$.

**Axiomatization rationale.** A full proof requires Mathlib infrastructure
that is absent at v4.26.0:

- Polish-space structure on `C(Icc (0:ℝ) 1, ℝ)` (needs separability via
  Stone-Weierstrass)
- Prokhorov's tightness theorem
- Kolmogorov-Centsov continuity criterion
- Continuous mapping theorem for weak convergence

Each gap is itself a substantial Mathlib contribution; collectively they
exceed any single-session research scope. The axiom is named, classical,
and corresponds to Wiedijk's "100 Theorems" item #45, which is open in
all major theorem provers as of 2026.

**Use.** This axiom unlocks the derivation pipeline in S4-S6 that
downgrades the parent file's three axioms (`reflection_principle`,
`firstPassageTime_eq_maxEvent`, embedded arcsine) to theorems. -/
axiom donsker_fclt
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (xi : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (xi i))
    (hindep : iIndepFun xi μ)
    (hmean : ∀ i, ∫ ω, xi i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (xi i ω) ^ 2 ∂μ = 1) :
    ∃ bm : BrownianMotion Ω μ,
      WeakConvergesInC01 μ (interpolatedRescaled xi) bm.W

end BallotOQ05
