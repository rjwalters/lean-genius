# Research State: szemeredi-theorem-oq-01

## Current State
**Phase**: ACT-shipped (Approach A landed)
**Path**: full
**Since**: 2026-06-03 (was DECISION-RECORDED since 2026-05-30)
**Iteration**: 4
**Last Updated**: 2026-06-03 (Session 3, researcher-1, **ACT** — `SzemerediTheoremOQ01.lean` + gallery entry shipped)

## Current Focus
Approach A landed. New artifacts:

- `proofs/Proofs/SzemerediTheoremOQ01.lean` (~88 lines, 1 axiom, 1 theorem, 0 sorries) — axiomatizes the Kelley–Meka 2023 bound `r_3(N) ≤ N · exp(-c (log N)^{1/12})` against Mathlib's `rothNumberNat` and derives the density form `r_3(N)/N ≤ exp(-c (log N)^{1/12})` as a non-axiomatic corollary.
- `src/data/proofs/szemeredi-theorem-oq-01/{meta.json, annotations.json}` — gallery entry with `status: axiomatized`, `badge: axiom`, `axiomCount: 1`, `sorries: 0`. Three section annotations (docstring, axiom, density corollary).
- `proofs/Proofs.lean` — registered `import Proofs.SzemerediTheoremOQ01`.

Pending: post-merge Mechanic / Auditor Docker-verify. The local Docker daemon is currently in I/O-error state (metadata DB corrupt at `/var/lib/desktop-containerd/...`) so this session could not run the build locally. The file is written in the same idioms as `SzemerediFullOQ02.lean` (proven working) and the `div_le_iff₀ … ; mul_comm ; exact hb` finish should be safe.

## Active Approach
**A (shipped)** — axiomatize Kelley–Meka. Single `axiom kelley_meka_bound`
with non-axiomatic density-form corollary
`rothNumberNat_density_le_kelley_meka`. Gallery entry marks status
`axiomatized` / badge `axiom` per project axiom integrity policy.

**B (spun off)** — Salem–Spencer quantitative Roth. Recommended sibling
slug `szemeredi-theorem-oq-01-incomplete-01` (BLOCKED on upstream
Mathlib infrastructure: no Bohr-set, no sifted-Fourier, no `U^3`). See
Session 2 audit memo in `knowledge.md`.

## Attempt Count
- Total attempts: 3 (S1 OBSERVE → ORIENT survey, S2 Mathlib audit, S3 ACT-ship)
- Current approach attempts: 1 Lean ACT (Approach A shipped)
- Approaches tried: 1 (Approach A shipped; Approach B audited and ruled out for this slug)

## Blockers
None for this slug. Approach B (sibling slug, BLOCKED on upstream
infrastructure) is tracked separately.

## Next Action

Post-merge:

1. Mechanic / Auditor: run Docker build of `Proofs.SzemerediTheoremOQ01`
   and verify `axiomCount: 1`, `sorries: 0`.
2. Curator / Seeker: extract the recommended sibling slug
   `szemeredi-theorem-oq-01-incomplete-01` for the BLOCKED Salem–Spencer
   quantitative direction.
3. This slug is graduation-ready once Mechanic/Auditor pass.

See `knowledge.md` Session 3 (this session) for the ACT log.
