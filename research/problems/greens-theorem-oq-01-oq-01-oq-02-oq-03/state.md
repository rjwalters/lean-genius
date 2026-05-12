# Current State

**Phase**: ORIENT (S2 SCAFFOLD complete: ordered case fully proved, general + continuous deferred)
**Since**: 2026-05-12T03:45:00Z
**Iteration**: 2
**Owner**: researcher-6

## Current Focus

S2 SCAFFOLD per S1 OBSERVE plan: port the parent file's three real-valued
`intervalIntegral_swap` theorems to Banach codomain `E`. The ordered case
is fully proved (verbatim port); general + continuous cases are stubbed
for S3.

## Active Approach

**Verbatim port from real-valued parent + linarith → abel for general case.**

The S1 audit (PR #17769) confirmed every Mathlib lemma the parent invokes
is already Bochner-generic. The S2 ordered-case proof is therefore a literal
character-for-character port with `f : ℝ → ℝ → E` substituted for
`f : ℝ → ℝ → ℝ`. The general-case proof requires four `linarith → abel`
substitutions in the sign analysis (the underlying identities are
additive-abelian, not order-theoretic).

## Blockers

None mathematical.

Practical (build): the `proofs/.lake` symlink in the researcher worktree
points to itself (memory `feedback_researcher_lake_symlink_broken.md`),
so Docker build will be a fresh ~25-minute clone. This S2 SCAFFOLD only
adds ~143 lines with verbatim ports, so build risk is low.

## Next Action

**S3 ACT**: close the two sorries (`intervalIntegral_swap`,
`intervalIntegral_swap_of_continuous`).

### General case (sorry 1)
Port the parent's 4-case sign analysis verbatim. The four sub-cases are
- `a ≤ b ∧ c ≤ d`: direct from ordered case (no sign-flip).
- `a ≤ b ∧ c > d`: one flip on the y-axis via `flip_bounds_E`.
- `a > b ∧ c ≤ d`: one flip on the x-axis via `flip_bounds_E`.
- `a > b ∧ c > d`: two flips combining via `neg_outside_E`.

Each sub-case has one `linarith` invocation in the parent's proof, all
four replaced by `abel` in the port. Estimated ~80 lines.

### Continuous case (sorry 2)
Apply the general case after extracting measurability + integrability
from continuity via `Continuous.measurable` and
`ContinuousOn.integrableOn_compact` (both codomain-generic). Estimated
~30 lines.

### S4 (post-S3)
Companion file `…Aristotle.lean` exposing `flip_bounds_E` and
`neg_outside_E` as parallelizable Aristotle targets (already private-proven
here, but a public companion enables independent Aristotle scheduling).

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Audit + documentation | 0 Lean | merged #17769 |
| S2 | ORIENT | Ordered case proved; general + cont. sorry | 143 | **this session** |
| S3 | ACT | Close general + continuous sorries | ~110 | next |
| S4 | ACT | Aristotle companion file | ~30 | |

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S2 ORIENT verbatim port)
- Approaches tried:
  - S1 (researcher-1): OBSERVE audit confirming codomain genericity.
  - S2 (researcher-6): ORIENT — port ordered case + stub general/continuous.

## Key Files

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` — **new in S2** (143 lines,
  5 theorems including 2 private helpers, 0 axioms, 2 sorries).
- `src/data/proofs/greens-theorem-oq-01-oq-01-oq-02-oq-03/` — **new in S2**
  gallery entry (status `axiomatized`, sorries 2).
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` — parent file, 231 lines,
  3 theorems (ordered/general/continuous), 0 sorries, 0 axioms. Verified.
