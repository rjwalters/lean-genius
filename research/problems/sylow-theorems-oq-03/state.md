# Current State

**Phase**: PREP (S2 PREP chain complete — 6 PREPs merged; S2 ACT for Candidate A* nominated)
**Since**: 2026-05-12T20:55:00Z
**Last update**: 2026-05-14 (STATE-SYNC by researcher-4; catch up 6 merged S2 PREPs)
**Iteration**: 8 (S1, S1b, S2 PREP, S2 PREP-2, S2 PREP-3, S2 PREP-4, S2 PREP-5, S2 PREP-6)

## STATE-SYNC 2026-05-14 (researcher-4)

**Mode**: STATE-SYNC (doc-only). Between 2026-05-12T22:16Z (PR #18285,
S1 OBSERVE) and 2026-05-13T10:16Z (PR #18735, S2 PREP-6), **8 PRs**
merged for this slug but `state.md` was never updated past S1.
JSON `currentState.phase = "OBSERVE"` likewise lagged. This STATE-SYNC
bookends the PREP chain and pins the S2 ACT target for the picker.

### Merged-PR ledger (S1 through S2 PREP-6)

| # | PR | Phase | Date | Author | Key finding |
|---|----|-------|------|--------|-------------|
| 1 | #18285 | S1 OBSERVE | 2026-05-12 | researcher-1 | OQ-03 is a near-duplicate of completed OQ-02. Lists 3 candidates A/B/C with concrete signatures. |
| 2 | #18359 | S1b OBSERVE | 2026-05-12 | researcher-? | Audit correction — Candidate C (`normal_of_unique` sorry) is **moot** (already covered by OQ-02's recovery chain). Recommends "**Candidate A\***" — A with continuity-enhanced signature instead of bare `Fintype`. |
| 3 | #18453 | S2 PREP | 2026-05-13 | researcher-? | Candidate A\* decomposed into 5 substeps. Five Mathlib bearer names flagged "likely" pending verification at S2 ACT. |
| 4 | #18493 | S2 PREP-2 | 2026-05-13 | researcher-? | Candidate B (`sylowProP_inter_trivial`) decomposed into 5 substeps. TDS-flag (totally-disconnected) correction. |
| 5 | #18546 | S2 PREP-3 | 2026-05-13 | researcher-? | **`frattini_profinite` axiom is degenerate as stated** (+339 LOC audit). Discharges as a 1-line corollary — but the axiom may need restatement before ACT to be non-trivial. |
| 6 | #18658 | S2 PREP-4 | 2026-05-13 | researcher-? | Mathlib bearer audit for Candidate B: **PHANTOM** `closedSubgroup_eq_sInf_open` (not in Mathlib v4.26.0). Re-routes via `nhds_basis_clopen` + 6 minor findings. |
| 7 | #18722 | S2 PREP-5 | 2026-05-13 | researcher-? | `IsTopologicalGroup` typeclass-instance bridge for Candidate B5 + closure of PREP-4 §11 deferred API audit. |
| 8 | #18735 | S2 PREP-6 | 2026-05-13 | researcher-8 | **Candidate A\* Mathlib bearer audit**. Verifies the 5 PREP-1 "likely" names. **MAJOR WIN: `Subgroup.index_ker` at `Mathlib/GroupTheory/Index.lean:322`** collapses Substep 5's 3-lemma cardinality bridge to a single `rfl`-adjacent rewrite. Namespace corrections: `QuotientGroup.quotientKerEquivRange` (not `MulEquiv.*`), `IsPGroup.of_card` in `PGroup.lean` (not `Sylow.lean`), `Subgroup.index_eq_card` (not `..._quotient`). Net A* LOC budget **60 → ~50**, "medium build risk" → "negligible". |

### Candidate scope at end of PREP chain

| Candidate | Target axiom/sorry | Status | LOC | Build risk | Recommendation |
|-----------|-------------------|--------|-----|-----------|----------------|
| **A\*** | `sylowProP_projects_pgroup` (axiom L134 of `SylowTheoremOQ02.lean`) | **PREP complete, ACT-ready** | ~50 (down from PREP-1's ~60 via PREP-6 Finding I) | negligible | **Ship next** — all bearers verified, namespace paths corrected, cardinality bridge collapsed. |
| B | `sylowProP_inter_trivial` (axiom L142) | PREP complete | ~25 | medium (deferred to ACT post-PREP-5 typeclass bridge) | Deferrable — conditional on Candidate A\* not regressing the `IsTopologicalGroup` instance. |
| frattini | `frattini_profinite` (axiom) | PREP-3 audit: **degenerate as stated** | — | — | **Out of scope** — discharges trivially; suggests axiom restatement is a curator/architect concern, not researcher. |
| C | `sylowProP_normal_of_unique` (sorry L285) | S1b: **moot** | — | — | **Out of scope** — already covered by OQ-02's recovery chain per S1b correction. |

### S2 ACT Candidate A\* — Lean signature lock-in

Concrete target (per PREP-1 + PREP-6 corrections):

```lean
-- New file: proofs/Proofs/SylowTheoremOQ03.lean (~50 LOC)
theorem sylowProP_projects_pgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    {p : ℕ} [Fact (Nat.Prime p)] (P : SylowProP p G)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Fintype H] (φ : G →* H) (hφ : Continuous φ) :
    IsPGroup p (φ.range) := by
  -- 5 substeps per PREP-1 §3 + PREP-6 §2 simplification
  sorry  -- targets discharged at ACT
```

(Replaces OQ-02's `axiom sylowProP_projects_pgroup` at
`proofs/Proofs/SylowTheoremOQ02.lean:134` — `+0/–3 LOC` in OQ-02.)

### Net axiom impact

After S2 ACT (Candidate A\*) lands: OQ-02 axiom count **5 → 4**, no
change to gallery status or main theorem signatures. The remaining 4
OQ-02 axioms (`sylowProP_existence`, `sylowProP_conjugacy`,
`sylowProP_inter_trivial`, `frattini_profinite`) split into deep
(2 — out of OQ-03 scope) + adjacent (1 = Candidate B, deferrable)
+ degenerate (1 = `frattini_profinite`, curator/architect concern
per PREP-3 audit).

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

**S2 ACT (Candidate A\*) — any researcher.** Create
`proofs/Proofs/SylowTheoremOQ03.lean` (~50 LOC, **down from PREP-1's
~60** via PREP-6 Finding I's `Subgroup.index_ker` collapse) with
`sylowProP_projects_pgroup` discharged at the continuity-enhanced
signature locked in the STATE-SYNC section above. Use:

- PREP-1 (#18453) §3 — 5-substep decomposition
- PREP-6 (#18735) §2 — `Subgroup.index_ker` cardinality bridge
  (collapses Substep 5 from 3 lemmas / "medium risk" to 1 `rw`)
- PREP-6 (#18735) §3 — namespace corrections
  (`QuotientGroup.quotientKerEquivRange`, `IsPGroup.of_card` in
  `PGroup.lean`, `Subgroup.index_eq_card`)

Bundle the OQ-02 axiom replacement (`+0/–3 LOC`) into the same PR.
OQ-02 axiom count after merge: **5 → 4**.

Carries the established "build pending" convention while the
`proofs/.lake` recursive-symlink issue (PREP-1 § "Operational
notes") gates the Docker build chain.

### Subsequent candidates (post-A\* ACT, in priority order)

1. **Candidate B ACT** (~25 LOC, conditional). Apply PREP-2 / PREP-4 /
   PREP-5's findings — `nhds_basis_clopen` (replacing phantom
   `closedSubgroup_eq_sInf_open`) + `IsTopologicalGroup` instance
   bridge. Deferrable until A\* lands cleanly.
2. **frattini_profinite restatement** (curator/architect, not
   researcher). PREP-3 audit found the axiom degenerate as stated;
   restate or remove as an axiom-cleanup PR.
3. **Candidate C** (~40 LOC). PREP-1 nominated, but S1b correction
   marked **moot** — already covered by OQ-02's recovery chain. No
   action needed.

## Attempt Counts

- Total attempts: 8 (S1, S1b, S2 PREP, S2 PREP-2, S2 PREP-3, S2
  PREP-4, S2 PREP-5, S2 PREP-6)
- Current approach attempts: 7 (S2 PREP chain — all doc-only)
- Approaches tried: 1 (duplicate-detection + Candidate A* +
  exhaustive Mathlib bearer audit; Candidate A* unblocked for ACT)

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
