# Research State: lovasz-local-lemma-oq-01

## Current State
**Phase**: ORIENT → SURVEYED (true goal scoped; rational surrogate already complete)
**Path**: full
**Since**: 2026-06-26
**Iteration**: 2

## Current Focus

Authoritative goal (problem.md): **formalize the full probabilistic LLL with
measure-theoretic probability spaces in Lean 4**. (The research-pool *title*
"Finite Symmetric Thresholds" is a misnomer — that scope is already done; see
below.)

## Key finding 1: the rational/combinatorial surrogate is already complete

`Proofs/LovaszLocalLemma.lean` (364 lines, **0 sorries, 0 axioms**) already
proves the symmetric/general bounds, K-SAT (`ksat_lll`), Moser–Tardos
(`moser_tardos_termination`, `symmetric_moser_tardos_bound`), and the full
threshold theory: `lllThreshold d = d^d/(d+1)^(d+1)`, `lllThreshold_pos`, and
`lllThreshold_le_quarter (d) (hd : 1 ≤ d)` for ALL d ≥ 1. There is no
`LovaszLocalLemmaOQ01.lean` and no gallery dir; re-proving any of the above
would be duplication.

These are stated over `ℚ` with probabilities as rationals and dependency
encoded combinatorially (`IsValidDepGraph`, `HasMaxDegree`) — a faithful
*surrogate*, but NOT a measure-theoretic probability space.

## Key finding 2: the genuine gap is measure-theoretic

The true OQ-01 deliverable is the LLL over an actual probability space:
events as measurable sets `A_i : Set Ω` in a `MeasureTheory.ProbabilityMeasure`,
a real dependency/independence relation, and the conclusion
`μ (⋂ i, (A_i)ᶜ) > 0`. Mathlib provides the needed primitives —
`ProbabilityTheory.iIndepSet`, `MeasureTheory.Measure`, `condProb`/`cond`,
`ProbabilityTheory.cond` — but no LLL. A full proof (the Spencer / cluster-
expansion or the Moser–Tardos entropy-compression argument over a real measure
space) is research-grade and spans multiple sessions.

## Concrete tractable first increment (for a build-enabled session)

1. State the measure-theoretic symmetric LLL as a Lean theorem (events in a
   `ProbabilityMeasure`, `iIndepSet` for the non-neighbours, `μ Aᵢ ≤ p`,
   `e·p·(d+1) ≤ 1` ⟹ `μ (⋂ Aᵢᶜ) > 0`) — a precise specification, even before
   the proof.
2. Bridge identity (low-risk, pure ℚ algebra) linking the surrogate to the
   classical form: `(d+1) * lllThreshold d = (d/(d+1))^d ↗ 1/e`, i.e. the MT
   threshold dominates the textbook `1/(e(d+1))` bound. The base file uses the
   `d^d/(d+1)^(d+1)` form but never states this.
3. General-d threshold monotonicity `lllThreshold (d+1) ≤ lllThreshold d`
   (reduces to `(d+1)^(2d+2) ≤ d^d·(d+2)^(d+2)`), which would subsume
   `lllThreshold_le_quarter`.

## Blockers

The measure-theoretic formalization is a large effort (Mathlib has the
probability primitives but no LLL). Docker was down this session, so even the
low-risk increments (items 2–3) could not be build-verified; landing
unverified non-trivial inequalities is unsafe.

## Next Action

In a session with a working build: start with item 1 (state the
measure-theoretic symmetric LLL precisely, as a Prop / sorried theorem) and
item 2 (the `(d+1)·lllThreshold d = (d/(d+1))^d` bridge). Do NOT re-prove the
rational surrogate — it is already complete in `LovaszLocalLemma.lean`.
