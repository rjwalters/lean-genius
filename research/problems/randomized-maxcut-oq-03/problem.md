# Problem: Can we prove the 1/2 ratio is tight by exhibiting a graph family where the al...

**Slug**: `randomized-maxcut-oq-03`
**Created**: 2026-05-12
**Status**: Available
**Source**: gallery-gap (parent: `randomized-maxcut`)
**Category**: extension
**Tractability**: challenging
**Tags**: graph-theory, algorithms, probability, approximation, randomized

## Problem Statement

Can we prove the 1/2 ratio is tight by exhibiting a graph family where the algorithm achieves exactly 1/2?

## Source Gallery Proof

- Parent: `randomized-maxcut` — Randomized MaxCut Approximation
- Related: randomized-maxcut

## Goal for This Workspace

This is a research workspace for a single open question extracted from the gallery. The researcher should:

1. **OBSERVE**: Read the parent proof's `meta.json` and source files to understand the existing context (what is already proven, the conventions used, the API surface).
2. **ORIENT**: Survey Mathlib and the literature for relevant results. Look for adjacent formalizations, near-misses, and the standard proof techniques that apply.
3. **DECIDE**: Pick a concrete sub-question or first-step lemma that is plausibly within reach. Prefer a small, build-verifiable statement over an ambitious one.
4. **ACT**: Either ship a Lean scaffold (with stated targets and `sorry` placeholders for the remaining gaps) or, for moonshot-flavored questions, an S1 OBSERVE doc-only PR mapping the landscape and pointing to viable S2 follow-ups.

The Seeker has done the candidate-pool plumbing; the Researcher owns the OODA loop from here. See the role spec at `.lean/roles/researcher.md` for the standard cadence.

## Suggested First Steps

1. `gh pr list --search "randomized-maxcut-oq-03"` — confirm no parallel session is already in flight (race-safety re-check at session start).
2. Inspect `src/data/proofs/randomized-maxcut/meta.json` — `openQuestions` array — for adjacent OQs that may share infrastructure.
3. Search Mathlib for the central object referenced in the problem statement; the API surface usually dictates the cleanest decomposition.
