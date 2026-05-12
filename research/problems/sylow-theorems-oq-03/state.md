# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12T20:55:00Z
**Iteration**: 1
**Last update**: 2026-05-12 (S1 OBSERVE by researcher-1)

## Current Focus

S1 OBSERVE — duplicate detection against completed sibling
`sylow-theorems-oq-02` + audit of OQ-02's actual gaps (5 axioms + 1
sorry in `proofs/Proofs/SylowTheoremOQ02.lean`, 393 lines) + three
narrow adjacent S2 candidates.

## Active Approach

**Doc-only S1 OBSERVE.** No Lean changes. Deliverable is three
markdown files + one JSON gallery entry:

- `problem.md` — duplicate-detection note, OQ-02 audit table, three
  narrow S2 candidates (A: project_pgroup axiom; B: inter_trivial
  axiom; C: normal_of_unique sorry) with concrete Lean signatures.
- `knowledge.md` — § 1 duplicate detection, § 2 OQ-02 audit (5
  axioms + 1 sorry classified), § 3-5 detailed proof sketches for
  Candidates A/B/C with Lean skeletons, § 6 recommended S2 scope,
  § 8 risk register, § 10 cost estimate.
- `state.md` (this file).
- `src/data/research/problems/sylow-theorems-oq-03.json` — gallery
  entry, status `in-progress`, knowledge payload.

## S1 Summary

### Duplicate detection

`sylow-theorems-oq-03` ("pro-p Sylow recovered as inverse limit") is
a near-duplicate of completed `sylow-theorems-oq-02` ("Pro-p Sylow
Theory for Profinite Groups"). Memory pattern (researcher-12 PR
#18235, 2026-05-12): for duplicate Millennium / Hilbert / completed-
sibling slugs, S1 OBSERVE = duplicate-detection + parent audit +
shortlist 2-3 narrow adjacent S2 targets.

### Three S2 candidates locked

| ID | Target item | Type | Effort  | Notes |
|----|-------------|------|---------|-------|
| A  | `sylowProP_projects_pgroup` | axiom (line 134) | ~50 LOC | Most clearly dischargable; uses existing `proP_subgroup_card_ppow` (line 332) |
| B  | `sylowProP_inter_trivial`   | axiom (line 142) | ~25 LOC | Requires `IsProfiniteGroup` to expose totally-disconnected; **conditional** |
| C  | `sylowProP_normal_of_unique` | sorry (line 285) | ~40 LOC | Uses `isProP_conj_map` (line 226); rebundling care needed |

### Recommended S2 ACT (Candidate A)

Ship `proofs/Proofs/SylowTheoremOQ03.lean` (~50 LOC) discharging
`sylowProP_projects_pgroup` using `proP_subgroup_card_ppow`. Update
OQ-02's file by replacing the axiom with the new theorem.

Net: **OQ-02 axiom count 5 → 4** with no change to its gallery
status (`completed`) or main theorem signatures.

### Out of scope

The two **deep** axioms (`sylowProP_existence`,
`sylowProP_conjugacy`) require the full inverse-limit construction
and remain out of OQ-03 scope; they are OQ-02's own long-term
`nextSteps`.

## Blockers

None mathematical. Candidate B is **conditional** on
`IsProfiniteGroup`'s API exposing totally-disconnected — if it does
not, B requires a small augmentation that can either piggyback on B
or be split out.

**Operational:** worktree `proofs/.lake` is recursive
(`feedback_researcher_lake_symlink_broken.md`); local docker build
~25–45 min. S1 OBSERVE doc-only — no build needed.

## Next Action

**S2 ACT (Candidate A) — any researcher.** Create
`proofs/Proofs/SylowTheoremOQ03.lean` with
`sylowProP_projects_pgroup` discharged (~30 LOC inside the file plus
imports/namespace). Concrete skeleton in `knowledge.md` § 3.2.

The change to OQ-02's file (delete axiom, replace uses) is +0/–3
lines and can be bundled into the same PR.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches tried: 1 (duplicate-detection + narrow axiom-discharge
  shortlist)

## Open files

- `problem.md` — OQ-02 audit + S2 candidate signatures (this PR).
- `knowledge.md` — detailed candidate proof sketches (this PR).
- `state.md` (this file).
- (downstream) `proofs/Proofs/SylowTheoremOQ02.lean` — audit target;
  **not touched** in S1.

## Race awareness

OQ-03 has zero open PRs and zero recent merges at push time
(verified 2026-05-12 ~20:55 UTC via `gh pr list --search "sylow-
theorems-oq-03 in:title"`). Sister slugs (oq-01, oq-02, oq-04,
oq-05) target different aspects; no concurrent S1 OBSERVE risk.
The completed parent `oq-02` is in `completed` state — no concurrent
research activity expected.
