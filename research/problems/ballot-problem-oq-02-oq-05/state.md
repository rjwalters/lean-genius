# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-6, 2026-05-12): inaugural OBSERVE survey for `ballot-problem-oq-02-oq-05` — the seeker-selected open-question child of `ballot-problem-oq-02` (`Proofs/BallotProblemOQ02.lean`, the axiomatized continuous-time ballot problem via Brownian motion). The OQ asks for a formal proof of Donsker's functional CLT connecting the discrete and continuous ballot problems.

This iteration produces:

- `problem.md` — formal Lean-target signatures, Mathlib infrastructure map, classification (tier B, significance 8, tractability 3), and S2-S7 decomposition into tractable sub-deliverables.
- `knowledge.md` — historical timeline (Bachelier 1900 to Mörters-Peres 2010), reflection-principle bijection proof, continuous mapping theorem formulations, Lévy arcsine law variants, Sparre Andersen discrete arcsine, Skorohod-vs-$C[0,1]$ encoding tradeoffs, full bibliography.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/ballot-problem-oq-02-oq-05.json` — new entry.

No Lean changes in S1.

## Active Approach

**"Axiomatize Donsker, derive parent axioms" — collapse three ad hoc axioms into one named classical theorem.**

The parent `Proofs/BallotProblemOQ02.lean` carries three axioms (`reflection_principle`, `firstPassageTime_eq_maxEvent`, an arcsine identity embedded in the main theorem). The OQ-05 pipeline replaces them with:

1. One axiom for **Donsker's FCLT** itself: the rescaled interpolated random walk converges weakly in $C([0, 1])$ to standard Brownian motion.
2. One axiom for the **continuous mapping theorem applied to sup** (the general CMT is a Mathlib gap; restricting to the sup-functional sidesteps the Portmanteau dependency chain).
3. Optionally one axiom for the **continuous mapping for the positive-time integral functional** (used only in the Lévy arcsine derivation, S6).

The three parent axioms then become theorems:

- `reflection_principle` (parent) $\leftarrow$ `donsker_fclt` + `cmt_sup` + `discrete_reflection` (S3, proved). Closes the first parent axiom.
- `firstPassageTime_eq_maxEvent` (parent) $\leftarrow$ uses path continuity from `BrownianMotion.pathContinuous` + `Real.csInf_mem` directly; no Donsker dependency. Closes the second parent axiom.
- Embedded arcsine in `main_theorem` (parent) $\leftarrow$ Sparre Andersen 1949 (theorem, ~150 lines) + Stirling + `cmt_integral`. Closes the third parent axiom.

The result is a clean axiom budget: **2-3 named classical axioms** in the OQ-05 file, **0 axioms** in the parent, **the parent file's status `axiomatized` can plausibly downgrade to `verified` if all three named axioms can be eventually downgraded to Mathlib theorems**.

## Blockers

None mathematical for S1 (this is an OBSERVE iteration).

Practical infrastructure constraints (deferred to S2+):

- Weak convergence on $C([0, 1])$ is partial in Mathlib v4.26.0; the `MeasureTheory.Measure.Portmanteau` development supplies basic equivalences but not the full continuous mapping theorem. S2 will need to encode the weak-convergence predicate ad hoc or import `ProbabilityMeasure` carefully.
- The `proofs/.lake` symlink in the researcher worktree is recursive (per `feedback_researcher_lake_symlink_broken.md`); any future Docker build will be a ~25-minute fresh clone.
- Mathlib does not have a first-class Brownian motion (the parent file axiomatizes via a `BrownianMotion` structure). S2 should reuse the parent's structure rather than introduce a new one.

## Next Action

**S2 (any researcher)**: Create `proofs/Proofs/BallotProblemOQ02OQ05.lean` introducing:

```lean
import Mathlib
import Proofs.BallotProblemOQ02  -- for ContinuousBallot.BrownianMotion

namespace BallotOQ05

open MeasureTheory ProbabilityTheory ContinuousBallot

/-- Interpolated rescaled random walk on `[0, 1]`. -/
noncomputable def interpolatedRescaled
    {Ω : Type*} (xi : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  let k : ℕ := Nat.floor (t * n)
  let frac := t * n - k
  ((∑ i ∈ Finset.range k, xi i ω) + frac * xi k ω) / Real.sqrt n

/-- Weak-convergence predicate on `C([0,1], ℝ)`. Encoded ad hoc until the
Mathlib `Mathlib.MeasureTheory.Measure.Portmanteau` API is more complete. -/
def WeakConvergesInC01
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → ℝ → Ω → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  ∀ Φ : (ℝ → ℝ) → ℝ, Continuous Φ → ∀ ε > 0, ∃ N,
    ∀ n ≥ N, |∫ ω, Φ (fun t => Xn n t ω) ∂μ - ∫ ω, Φ (fun t => X t ω) ∂μ| < ε
  -- placeholder formalism; revisit when Mathlib lands `Continuous` on `C([0,1])`

/-- **Donsker's functional CLT** (axiomatized at v4.26.0). -/
axiom donsker_fclt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (xi : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (xi i))
    (hindep : ∀ i j, i ≠ j → IndepFun (xi i) (xi j) μ)
    (hmean : ∀ i, ∫ ω, xi i ω ∂μ = 0)
    (hvar  : ∀ i, ∫ ω, (xi i ω)^2 ∂μ = 1) :
    ∃ bm : BrownianMotion Ω μ,
      WeakConvergesInC01 μ (interpolatedRescaled xi) bm.W

end BallotOQ05
```

**Expected size**: ~80 Lean lines. 0 sorries, 1 new axiom (`donsker_fclt`), 1 new structure (`WeakConvergesInC01` definition), 0 new theorems.

The S2 deliverable is **statement-only**: introduces the central axiom and the supporting infrastructure (interpolated walk + weak-convergence predicate). S3 onward adds substance.

## Prior Next-Action Sketch

(None — this is the inaugural S1 iteration.)

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE survey)
- Current approach attempts: 1 (OBSERVE → axiomatize-Donsker decomposition)
- Approaches tried: 1

## Open files

- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, S2-S7 decomposition.
- `knowledge.md` — historical timeline (Bachelier $\to$ Mörters-Peres), reflection-principle bijection proof, three CMT formulations, Lévy arcsine variants, Sparre Andersen, full bibliography.

## S1 Deliverable

This iteration is **survey-only**:

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:

- `problem.md` (~3.5K words) with formal Lean signature targets, Mathlib infrastructure map (13 ingredients tracked, ~4 available / ~2 partial / ~7 gap), and S2-S7 decomposition into single-session deliverables.
- `state.md` (this file) advancing phase NEW $\to$ OBSERVE.
- `knowledge.md` (~3K words) with historical timeline, three CMT formulations, full bibliography (Donsker 1951, Billingsley 1968, Karatzas-Shreve 1991, Lévy 1939, Sparre Andersen 1949, Prokhorov 1956, Feller 1968, Resnick 1999, Mörters-Peres 2010, OEIS A000984).
- `src/data/research/problems/ballot-problem-oq-02-oq-05.json` — new entry with progressSummary, builtItems=[], insights, mathlibGaps (7 gap items), nextSteps (S2 through S7).

The S1 next-action is fully specified: create `proofs/Proofs/BallotProblemOQ02OQ05.lean` with `donsker_fclt` axiom + `interpolatedRescaled` definition + `WeakConvergesInC01` predicate (~80 Lean lines, 0 sorries, 1 new axiom).
