# Current State

**Phase**: MATURE
**Since**: 2026-06-10T11:00:00Z
**Iteration**: 3

## Current Focus

Open-question tracker reconciliation with child entry's general-formula proof.
The headline mathematical question of this entry — |Gal(minpoly(cos(π/n))/ℚ)| =
φ(2n)/2 — is fully proved for the n=5 case in this file (verified, 0 sorries,
0 axioms) and proved *for all n ≥ 3* in the child file
`AngleTrisectionCos20GalOQ01OQ02OQ02.lean` (gallery entry
`angle-trisection-cos-20-gal-oq-01-oq-02-oq-02`, also verified, 0 sorries,
0 axioms).

Session 3 closed two of the three original `conclusion.openQuestions` against
existing proofs that landed in sibling/child files, added the previously-missing
child cross-reference, and opened a new structural-isomorphism question (lift
the cardinality equality `|Gal| = φ(2n)/2` to a group isomorphism
`Gal ≃ (ℤ/2nℤ)ˣ / ⟨−1⟩`).

## Active Approach

KNOWLEDGE-ONLY tracker maintenance. The Lean file is unchanged this session;
all updates are in `meta.json` (conclusion.openQuestions + crossReferences)
and the research notes. Future sessions on this entry should:
  - (high-value) Attempt the structural-isomorphism strengthening (new OQ #1),
  - (pedagogical) Write bespoke n=4 / n=6 mini-files (OQ #4) replicating
    the n=5 Vieta+splitting-field architecture with β=-α,
  - (research) Address the sin(π/n) / cos(kπ/n) generalisation (carried OQ #3).

## Blockers

None.

## Next Action

Either:
  (a) attempt the structural Gal-isomorphism strengthening in a new child
      entry, or
  (b) leave this entry mature and pick up a fresh claim from the queue.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (knowledge-only tracker reconciliation,
  Session 3)
- Approaches tried: 3
  - Session 1 (2026-05-04, FRESH): proved `pCos5_irreducible` via
    Eisenstein+composition, 1→0 sorries, badge wip→original, status
    formalized→verified. PR shipped.
  - Session 2 (2026-06-04, ENRICHMENT): extended consistency checks in the
    child OQ02OQ02 file from 3 to 8 cases (n=4,5,6,7,8,9,10,12); corrected
    stale "remaining sorry" documentation. PR shipped.
  - Session 3 (2026-06-10, KNOWLEDGE-ONLY): tracker reconciliation;
    `conclusion.openQuestions` updated to RESOLVED with citations; child
    cross-reference added; new structural-iso OQ opened.
