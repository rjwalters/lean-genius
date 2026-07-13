# S7a ACT — OQ-02 axiom drop 4 → 3 (post-S6 follow-on)

**Researcher:** researcher-1
**Date:** 2026-06-05
**Phase:** ACT (follow-on to S6 Candidate B; no new mathematical content)
**Iteration:** 16

## Goal

Realize the §7a follow-on from S6 ACT (2026-06-05) state.md, top-of-list
NEXT TOP: delete the now-superseded axiom `sylowProP_inter_trivial`
from `SylowTheoremOQ02.lean` together with its `#check` line.

S6 ACT shipped `ProfiniteSylow.sylowProP_inter_trivial_via_quotient`
in `Proofs/SylowTheoremOQ03B.lean` (3066 Docker jobs clean), proving
the axiom's exact signature via the PREP-2 finite-quotient route. The
axiom is now redundant; per S6 §7a, the clean follow-on is a 1-PR
deletion mirroring the A* → S4 split pattern.

## What shipped

| File | Δ | Note |
|------|---|------|
| `proofs/Proofs/SylowTheoremOQ02.lean` | −7/+5 LOC (net −2) | Delete `axiom sylowProP_inter_trivial` L133-137 + corresponding `#check @sylowProP_inter_trivial` L372; insert 5-line comment in place of the axiom block explaining the discharge |
| `src/data/proofs/sylow-theorems-oq-02/meta.json` | 7 fields | `axiomCount` 4 → 3 (top + leanFile), `lineCount` 374 → 372 (top + leanFile), description "4 axioms" → "3 axioms", `assumptions` rewritten to credit S6 Candidate B for the new discharge, conclusion `summary` line-count + axiom-count adjusted, two `sections[]` summary entries updated (axioms / counting-and-summary) |
| `research/problems/sylow-theorems-oq-03/sessions/2026-06-05-s7a-act-oq02-axiom-drop-4-to-3.md` | NEW | This file |
| `research/problems/sylow-theorems-oq-03/state.md` | header + §7a entry | Phase / Iteration / S7a outcome block |

## Build verification

Both files Docker-verified clean on lockfile (mathlib v4.26.0 /
lean v4.26.0) in this session:

```
./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ02
✔ [3061/3061] Built Proofs.SylowTheoremOQ02
=== Build succeeded ===

./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ03B
✔ [3066/3066] Built Proofs.SylowTheoremOQ03B (6.4s)
=== Build succeeded ===
```

The OQ-02 `#check` enumeration at end-of-file now correctly omits the
deleted axiom and lists 3 axioms + 10 theorems (12 declarations total).
The OQ-03B file is unchanged at the `.lean` level; it references the
deleted axiom only in docstrings, so the build remains clean.

## Risks predicted vs realized

| # | Predicted | Outcome |
|---|-----------|---------|
| 1 | Other callers of `sylowProP_inter_trivial` outside OQ-02 / OQ-03B | **NONE**: `grep -nr "sylowProP_inter_trivial[^_]" proofs/Proofs/` finds 4 hits in OQ-03B (all docstrings) + 0 hits elsewhere |
| 2 | The deleted axiom's section endLine in meta.json shifts | **MINOR**: section endLines are already partially out of date (e.g. summary-and-checks endLine 298 while file ends at 372/374); deferred to a future meta.json refresh — this PR updates the top-level + leanFile counts + assumptions + conclusion + per-section summary prose |
| 3 | The 5-line discharge comment grows the file relative to the bare deletion | **REALIZED, EXPECTED**: net −2 LOC, not the −6 LOC S6 §7a predicted. The discharge comment is justified for documentation continuity (a future reader of OQ-02 deserves to know why the axiom slot is empty); the predicted −6 LOC was over-aggressive |

## Net axiom impact

* OQ-02 axiom count: **4 → 3** (this PR).
* OQ-03B axiom count: **0 → 0** (unchanged; theorems-only file).
* OQ-03 axiom count: **0 → 0** (unchanged; the A*-bearing file).

Aggregate Sylow-OQ family: **4 → 3 axioms** across the three files
(OQ-02 down by 1, OQ-03 and OQ-03B unchanged). The remaining 3 axioms
in OQ-02 are:
1. `sylowProP_exists` — existence via Zorn's lemma (deep, retained).
2. `sylowProP_conjugate` — conjugacy via finite approximation (deep, retained).
3. `frattini_profinite` — Frattini argument (curator/architect-scope
   restatement deferred per S6 §7c).

## Revised Current Focus / Next Action

This S7a PR brings OQ-02's axiom budget to 3 — the natural stopping
point per S6 §7d. Subsequent natural next actions (per S6 §7b/§7c):

- **§7b (out-of-band)** — Mathlib upstream contribution for the
  PREP-4/5 chain `nhds_basis_clopen` / `exist_openNormalSubgroup_sub_open_nhds_of_one`
  that powers OQ-03B's discharge proof. Already noted in S6.
- **§7c (curator/architect scope)** — `frattini_profinite` axiom
  restatement (factor through a derivable form using existing
  Mathlib `Subgroup.normalizer` API). Already noted in S6.

## Files modified

4 files:
1. `proofs/Proofs/SylowTheoremOQ02.lean` (−7/+5 LOC, net −2)
2. `src/data/proofs/sylow-theorems-oq-02/meta.json` (7 fields)
3. `research/problems/sylow-theorems-oq-03/sessions/2026-06-05-s7a-act-oq02-axiom-drop-4-to-3.md` (NEW)
4. `research/problems/sylow-theorems-oq-03/state.md` (header + §7a entry)

NO edits to: `proofs/Proofs/SylowTheoremOQ03.lean`,
`proofs/Proofs/SylowTheoremOQ03B.lean`, sibling slug JSONs, sibling
slug directories, `.loom/`, gallery `meta.json` for OQ-03 / OQ-03B.

## Pattern note

This is the second clean "axiom drop" PR in the Sylow-OQ family —
mirrors S4 ACT (PR #19380) which dropped OQ-02's earlier projection
axiom 1 day after S2 ACT shipped the discharging theorem. Today's S7a
ships ~1 day after S6 ACT (2026-06-05). The pattern is:

1. ACT iteration ships a new theorem with the OQ-02 axiom's exact signature.
2. Build verification confirms the theorem elaborates.
3. Same-day or next-day follow-on PR deletes the now-redundant axiom.

The separation preserves bisection-friendliness: if the theorem PR
introduces a regression, the axiom-drop PR can be reverted
independently without losing the theorem.
