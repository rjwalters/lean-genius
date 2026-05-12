# Research State: ptolemys-complex-proof-oq-02-oq-02

## Current State
**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T22:32 UTC
**Iteration**: 1 (S1)

## Current Focus

S1 OBSERVE — chord-length-on-radius-$r$ and law-of-cosines-via-Ptolemy survey.

Deliverable: `sessions/2026-05-12-s1-observe-radius-r-and-law-of-cosines.md` (this PR).
Confirms that the parent's six chord-length lemmas can be generalized to radius $r$ by
factoring $r$ out (each ends up multiplying by $2r$ instead of $2$). Identifies the
law-of-cosines-via-Ptolemy construction (inscribed quadrilateral $ABCC'$ where $C'$ is
the reflection of $C$ across the perpendicular bisector of $AB$) and decomposes S2 into
three sub-iterations (S2a/S2b/S2c, total ~270 LOC).

## Active Approach

S1 OBSERVE: literature + Mathlib API survey. No Lean code touched.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE)

## Blockers

**None**. The chord-length generalization is mechanical (linear factor of $r$), and the
law-of-cosines-via-Ptolemy construction uses only `Complex.exp`, `Real.sin`/`cos`, and
`Norm.norm` — all stable Mathlib APIs at v4.26.0.

The only choice point for S2c is whether to invoke a hypothetical `Real.law_of_sines` (if
Mathlib has one) or write a 30-line helper. The session note (§4.c) recommends writing
the helper to remove the upstream-dependency.

## Next Action

**S2a ACT**: write `proofs/Proofs/PtolemysComplexProofOQ02OQ02.lean` with the single
helper `chord_length_at_radius_r`. ~80 LOC, 0 sorries, 0 axioms. Subsume the parent's
six radius-1 lemmas as `r := 1` corollaries (DO NOT modify the parent file, which is
COMPLETED and verified).

Then S2b (`ptolemy_radius_r`) and S2c (`law_of_cosines_via_ptolemy`) in follow-up PRs.

## Open PRs
- This PR (S1 OBSERVE doc-only — ~+650 LOC across problem.md, state.md, knowledge.md,
  and `sessions/2026-05-12-s1-observe-radius-r-and-law-of-cosines.md`).

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | (this PR) | OBSERVE — chord-radius-$r$ + law-of-cosines roadmap (3-sub-iteration S2 plan, ~270 LOC) |
