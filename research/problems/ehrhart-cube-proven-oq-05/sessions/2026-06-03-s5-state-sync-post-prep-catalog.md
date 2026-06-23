# S5 STATE-SYNC — Post-PREP catalog + 21-day quiescence audit

**Date**: 2026-06-03
**Researcher**: researcher-1
**Type**: Doc-only STATE-SYNC (no Lean edits, no parent edits).
**Scope**: Refresh stale `state.md` (frozen at "Phase: OBSERVE (S1
complete) / Iteration: 1" from 2026-05-12) to reflect the **four
additional merged PREP iterations** shipped 2026-05-13 by other
researchers, and document the 21-day quiescence window since the last
slug touch.

This iteration is **iteration-neutral** for the underlying research
plan: it does not advance the discharge of any S2-S5 goal, and the
next-action recommendation (AXIOM-FIX per S2b/S2c PREPs, then S2 ACT)
is unchanged. The single load-bearing observation is that the slug's
canonical state pointer (`state.md`) is now resynchronised with the
five merged PRs and the cumulative session-memo catalog.

## §1 Slug quiescence (21-day window)

Window: 2026-05-13T07:00:00Z (S2c PREP merge `#18617`) → today 2026-06-03.

Per-bearer `git log origin/main --since="2026-05-13T07:00:00Z"` for
each slug-related path:

| Bearer | Touches in window | Latest touching commit |
|--------|-------------------|------------------------|
| `proofs/Proofs/EhrhartPolynomials.lean` | 1 (full-tree import) | `ecb47b35601` (Sperner #19454, 2026-05-16) |
| `proofs/Proofs/PicksTheorem.lean` | 1 (same Sperner import) | `ecb47b35601` |
| `research/problems/ehrhart-cube-proven-oq-05/` | 1 (same) | `ecb47b35601` |
| `src/data/research/problems/ehrhart-cube-proven-oq-05.json` | 1 (same) | `ecb47b35601` |
| `proofs/Proofs/EhrhartCubeProvenOQ05.lean` | **0** | does not exist (S2 ACT not yet run) |

The single touching commit (`ecb47b35601`, Sperner PR #19454,
2026-05-16) is a large multi-file ACT that imported a tree-wide
snapshot including these files. **0 substantive content touches**
to the slug's research dir or to its bearer files since then —
slug content is byte-stable across the 21-day window post-Sperner.

## §2 Bearer SHA pins (at base SHA `996638aefdf`)

| Bearer | SHA1 |
|--------|------|
| `proofs/Proofs/EhrhartPolynomials.lean` | `7f8a2695552e64ceaa3814591135a10f19177c28` |
| `proofs/Proofs/PicksTheorem.lean` | `e49266b5718e9465a3c5f5b35204196614a60f0a` |
| `src/data/research/problems/ehrhart-cube-proven-oq-05.json` | `f47b07a80a795356b00f753b5c592ebef2537d71` |
| `proofs/Proofs/EhrhartCubeProvenOQ05.lean` | (does not exist) |

Parent axiom line numbers in `EhrhartPolynomials.lean`:

| # | Axiom | Line |
|---|-------|------|
| 1 | `ehrhart_theorem` | 108 |
| 2 | `ehrhart_leading_coeff_volume` | 141 |
| 3 | `ehrhart_macdonald_reciprocity` | 178 |

All three line numbers match the S2 PREP §"Axiom-inheritance audit"
verbatim. The `ehrhart_leading_coeff_volume` axiom at line 141 is the
one S2b PREP §1.5 flagged as **logically inconsistent** (Fix B/D
proposed; ripple-corrected by S2c PREP to single-file 5-LOC change).

## §3 Cumulative PREP catalog (5 merged PRs, 4 doc-only PREPs after S1)

| Iter | Date | Researcher | PR | Type | Session memo |
|------|------|-----------|----|----- |--------------|
| S1 OBSERVE | 2026-05-12 | researcher-9 | #18384 | doc-only | `(state.md original)` |
| S2 PREP | 2026-05-13 | researcher-8 | #18475 | doc-only | `2026-05-13-s2-prep-lean-blueprint.md` |
| S4 PREP | 2026-05-13 | researcher-9 | #18492 | doc-only | `2026-05-13-s4-prep-q2-bridge-construction.md` |
| S2b PREP | 2026-05-13 | researcher-11 | #18535 | doc-only | `2026-05-13-s2b-prep-axiom-audit-inconsistency.md` |
| S2c PREP | 2026-05-13 | researcher-12 | #18617 | doc-only | `2026-05-13-s2c-prep-ripple-scope-correction-zero-consumers.md` |

**Net**: 5 merged PRs, 0 Lean files modified, 0 axioms changed,
0 sorries closed. The `state.md` head was last refreshed at S1 OBSERVE
on 2026-05-12 and is **21 days stale** at PR-creation time of this
SYNC — none of the 4 follow-on PREP authors refreshed it. This SYNC
is the first to do so.

### §3.1 What each PREP established

* **S2 PREP** (researcher-8): concrete Lean blueprint for
  `EhrhartCubeProvenOQ05.lean` — type signatures for `ehrhartPoly_2d_explicit`
  (Q1), `simpleLatticePolygon_to_latticePolygon` (Q2 bridge),
  `picks_theorem_derived` (Q2 close); ~80 LOC scaffold target;
  axiom-inheritance audit (3 axioms from `EhrhartPolynomials.lean`,
  0 new); Mathlib API surface verified against pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
* **S4 PREP** (researcher-9): Q2 bridge design memo. Identifies
  `SimpleLatticePolygon` (`PicksTheorem.lean`) and `LatticePolygon`
  (`EhrhartPolynomials.lean`, `extends LatticePolytope 2`) as
  parallel-but-non-overlapping. The bridge cannot be pure
  projection-of-fields: `SimpleLatticePolygon` lacks a
  `latticePointCount` function. Construction B.2 ("placeholder
  count") recommended over 3 alternatives. ~25 LOC, 0 sorries, 0
  axioms estimated for S4 ACT.
* **S2b PREP** (researcher-11): **CRITICAL** —
  `ehrhart_leading_coeff_volume` (line 141) is logically inconsistent
  (applied twice with two distinct positive volumes derives `1 = 2`,
  hence `False`). **MAJOR** — `LatticePolygon.interiorPoints` (line
  208) is not linked to Macdonald `interior_count(1)`. Both block
  S3 ACT as currently scoped. 4 fix options analysed; Fix B (move
  `volume` into the structure) + Fix D (link `interiorPoints` to
  `interior_count`) recommended.
* **S2c PREP** (researcher-12): ripple-scope correction — grep
  verification shows the 4 files S2b PREP §3.6 named as needing
  ripple updates (OQ-02, OQ-04, `EhrhartCrossPolytope`,
  `EhrhartSimplexProven`) **do not import** `Proofs.EhrhartPolynomials`.
  Fix B/D blast radius is **single-file 5 LOC** (not cross-file as
  S2b PREP §3.6 implied). The AXIOM-FIX PR can be a single-file
  Mechanic patch.

### §3.2 Cumulative readiness gate (post-S2c)

| # | Item | Status |
|---|------|--------|
| 1 | Concrete Lean scaffold blueprint (S2 PREP) | GREEN |
| 2 | Q2 bridge construction design (S4 PREP) | GREEN |
| 3 | Axiom-inconsistency audit + fixes (S2b PREP) | GREEN |
| 4 | Ripple-scope correction (single-file fix) (S2c PREP) | GREEN |
| 5 | AXIOM-FIX PR shipped (Fix B + Fix D, 5 LOC) | **NOT YET** |
| 6 | S2 ACT shipped (`EhrhartCubeProvenOQ05.lean` scaffold) | **NOT YET** |
| 7 | S3 ACT (Q1 explicit form) | NOT YET |
| 8 | S4 ACT (Q2 bridge) | NOT YET |
| 9 | S5 ACT (Q2 close: `picks_theorem_derived`) | NOT YET |

**Items 5 and 6 both require Docker verification**; both are blocked
by current infra (§5 below).

## §4 Next action (revised, supersedes stale state.md "Next Action")

The state.md "Next Action" block (lines 73-99) describes the S2 ACT
deliverable — outdated since 4 PREPs have intervened. The **actual**
next action is:

### §4.1 AXIOM-FIX (single-file Mechanic patch, ~5 LOC)

Per S2b PREP Fix B + Fix D and S2c PREP ripple correction:

* Modify `proofs/Proofs/EhrhartPolynomials.lean` line 141 area
  (`ehrhart_leading_coeff_volume`): change the axiom signature to
  bind `volume` as a structure field rather than universally
  quantifying it (Fix B per S2b PREP §3.1).
* Modify `proofs/Proofs/EhrhartPolynomials.lean` line 208 area
  (`LatticePolygon`): add a field or axiom linking
  `interiorPoints` to `interior_count(1)` (Fix D per S2b PREP §3.2).
* Single-file change, 0 ripple per S2c PREP audit.
* Build verification: `./proofs/scripts/docker-build.sh
  Proofs.EhrhartPolynomials` (and `Proofs.PicksTheorem` if any
  downstream is affected — S2c PREP confirms none are).

### §4.2 S2 ACT (~80 LOC scaffold, after AXIOM-FIX lands)

Per S2 PREP blueprint:

* Create `proofs/Proofs/EhrhartCubeProvenOQ05.lean` (~80 LOC).
* 3 theorem stubs with `:= by sorry` (S3/S4/S5 targets).
* Wire into `proofs/Proofs.lean` umbrella.
* Create minimal `src/data/proofs/ehrhart-cube-proven-oq-05/{meta.json,index.ts}`.
* Update `src/data/research/problems/ehrhart-cube-proven-oq-05.json`
  (phase OBSERVE → ACT, iteration 1 → 2).
* Build verification: `./proofs/scripts/docker-build.sh
  Proofs.EhrhartCubeProvenOQ05`.

Both §4.1 and §4.2 are mechanical execution against existing PREP
deliverables. The mathematical hard work (the algebraic Q1 derivation,
the Q2 bridge construction) is already designed in S2/S4 PREPs.

## §5 Infra blocker (Docker / disk pressure)

Host disk at PR-creation time:

```
$ df -h /Users/rwalters/GitHub/lean-genius
Filesystem      Size    Used   Avail Capacity
/dev/disk3s5   926Gi   890Gi   5.1Gi   100%
```

**5.1 Gi free, 100% capacity.** Below the ≥10 Gi pre-flight threshold
for safe Docker builds. AXIOM-FIX (~5 LOC patch) and S2 ACT (~80 LOC
scaffold) both require `docker-build.sh` verification; both are
blocked until disk recovers to ≥15 Gi free.

This SYNC (doc-only, ≤ 4 KB of writes) is safe at current disk state.
This same blocker was observed and documented in the sibling slug
`spherical-law-of-sines-oq-03` S5 PREP §7 (this researcher's prior
iteration in this session).

## §6 Race / saturation (re-affirmed at PR-creation)

```
$ gh pr list --search "ehrhart-cube-proven-oq-05 in:title" --state open
(no open PRs)
```

Field clear: 0 open PRs on slug. The most recent PR on slug is
S2c PREP (#18617) merged 2026-05-13. This SYNC's doc-only file list
(§7 below) is disjoint from any in-flight agent work.

## §7 Files modified by this PR

1. `research/problems/ehrhart-cube-proven-oq-05/sessions/2026-06-03-s5-state-sync-post-prep-catalog.md`
   (this file, NEW).
2. `research/problems/ehrhart-cube-proven-oq-05/state.md` (UPDATE: head
   block refreshed to reflect 5-PR cumulative state, iteration 1 → 2
   (catalog-only bump, not an ACT), session log appended with this
   S5 entry; no narrative edits to existing content).
3. `src/data/research/problems/ehrhart-cube-proven-oq-05.json` (UPDATE:
   `lastUpdated` → `2026-06-03` + `knowledge.progressSummary` prepend;
   no edits to phase, status, tier, researcher, claim fields).

**No Lean source modified. No `lake-manifest.json` modified. No parent
gallery JSON modified. No new sorries. No new axioms.**

## §8 Honest scope

* Refreshes the canonical state pointer (`state.md`) which was
  21 days stale and missing 4 merged PREP iterations.
* Catalogues the 5 merged PRs in one place for the next iteration
  agent.
* Documents the AXIOM-FIX as the concrete next deliverable (per
  S2b/S2c PREPs).
* Documents the Docker / disk-pressure blocker.
* **Does NOT** ship the AXIOM-FIX (infra-blocked).
* **Does NOT** ship S2 ACT (infra-blocked, and depends on AXIOM-FIX).
* **Does NOT** discharge any open mathematical goal.
* **Does NOT** modify the existing 4 session memos or any parent file.
* Iteration counter advances **1 → 2** (catalog-only bump to reflect
  cumulative PREP progress; this is not an ACT bump).

The single load-bearing output of this SYNC is the refreshed
`state.md` head and the §3 cumulative catalog. The §4 next-action
restatement is supporting material that translates S2b/S2c PREPs'
recommendations into a concrete next-PR specification.

## §9 References

* Predecessor PRs (5): #18384 (S1 OBSERVE), #18475 (S2 PREP), #18492
  (S4 PREP), #18535 (S2b PREP), #18617 (S2c PREP).
* Existing session memos: `2026-05-13-s2-prep-lean-blueprint.md`,
  `2026-05-13-s4-prep-q2-bridge-construction.md`,
  `2026-05-13-s2b-prep-axiom-audit-inconsistency.md`,
  `2026-05-13-s2c-prep-ripple-scope-correction-zero-consumers.md`.
* Sibling slug with the same infra blocker observation:
  `spherical-law-of-sines-oq-03` S5 PREP (this session, PR #22209).
