# Research State: szemeredi-theorem-oq-01

## Current State
**Phase**: DECISION-RECORDED (Approach A committed; Approach B spun off — pending sibling-slug extraction by seeker/curator)
**Path**: full
**Since**: 2026-05-30 (was OBSERVE since 2026-04-05, ORIENT since 2026-05-30 earlier today)
**Iteration**: 3
**Last Updated**: 2026-05-30 (Session 2, researcher-1, **S2 Mathlib audit** — `cornersTheoremBound` confirmed tower-type per Mathlib docstring; Approach A committed; Approach B spin-off recommended)

## Current Focus
Approach A committed: axiomatize the Kelley-Meka statement
`r_3(N) ≤ N · exp(-c (log N)^{1/12})` in a new
`proofs/Proofs/SzemerediTheoremOQ01.lean` (~30 LOC). Status will be
`axiomatized`, badge `axiom`. This is the right call given the Mathlib
gap inventory in `knowledge.md` Session 1 (no Bohr-set, no sifted-Fourier,
no `U^3` uniformity) and the audit finding in Session 2.

## Active Approach
**A (committed)** — axiomatize Kelley-Meka. Single `axiom` declaration
in a new file; minimal scaffolding; gallery entry marks status
`axiomatized` / badge `axiom` per project policy.

**B (spun off)** — Salem-Spencer quantitative Roth: cannot derive
`O(N / log log N)` from Mathlib's tower-type `cornersTheoremBound` (per
S2 audit, Mathlib's own docstring: "depends on `SzemerediRegularity.bound`,
which is a tower-type exponential"). Recommended spin-off slug:
`szemeredi-theorem-oq-01-incomplete-01`, BLOCKED on upstream Mathlib
infrastructure (Bohr-set, sifted-Fourier, `U^3`). See Session 2 memo §6.

## Attempt Count
- Total attempts: 2 (S1 OBSERVE → ORIENT survey + this S2 audit)
- Current approach attempts: 0 Lean ACTs (Approach A axiomatize is the next session's deliverable)
- Approaches tried: 1 (Approach A committed; Approach B audited and ruled out for this slug)

## Blockers
None. The next researcher session can ship Approach A (~30 LOC
axiomatize + gallery entry) directly.

## Next Action

Ship **Approach A** (axiomatize Kelley-Meka) in a fresh researcher
session:

1. Create `proofs/Proofs/SzemerediTheoremOQ01.lean` (~30 LOC):
   - Standard Mathlib imports.
   - `axiom kelley_meka_bound : ...` stating
     `r_3(N) ≤ N · exp(-c (log N)^{1/12})` in the Mathlib-compatible
     form (likely against `rothNumberNat` from
     `Mathlib.Combinatorics.Additive.SalemSpencer`).
   - Comment block citing Kelley-Meka 2023 (Annals of Math), with
     pointer to spin-off sibling for Approach B.
2. Create gallery entry `src/data/proofs/szemeredi-theorem-oq-01/`:
   - `meta.json`: `status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 1`, `sorryCount: 0`.
   - `annotations.json`, `index.ts` (minimal).
3. Update this state.md: Phase DECISION-RECORDED → ACT-shipped (or COMPLETED if no further work planned).

After Approach A lands, the slug is **graduation-ready** modulo any
Aristotle / Mechanic Docker-verify. The Approach B spin-off (sibling
slug) is independent and tracked separately.

See knowledge.md for the full survey (Session 1) and audit (Session 2).
