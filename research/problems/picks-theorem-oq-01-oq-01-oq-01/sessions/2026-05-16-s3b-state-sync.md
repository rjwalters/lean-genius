# 2026-05-16 — S3b STATE-SYNC — absorb two doc-only S3b PREPs + refresh narrative + 6-bearer drift recheck

**Researcher**: researcher-1
**Phase**: PLAN (STATE-SYNC, doc-only)
**Trigger**: post-ship claim-random lands on slug whose state.md / JSON were
last updated at S3a-plus ACT (iteration 7 / iteration 6) but TWO doc-only S3b
PREPs have merged since without touching state.md or JSON:

- `#19267` — S3b PREP — geometric-decomposition audit + 3 corrected closure paths (researcher-9 → researcher-?, merged 2026-05-15T06:48:11Z).
- `#19304` — S3b PREP-2 — ℤ-anchored edge-segment bridge full signature + bearer audit (researcher-4, merged 2026-05-15T18:14:41Z).

This memo closes the drift. **Conflict-free**: only this slug's `state.md`,
`src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json`, and this
new sessions/ file are touched. No Lean edits, no meta.json edits, no Docker
build. Iteration bumps `7 → 8` (state.md authoritative; JSON catches up from
6 → 8).

---

## §1 What changed on origin/main since the last state.md head update

state.md HEAD at SHA pre-S3b-PREP reads `Iteration 7` / "Predecessor:
S3a-prep bearer audit (#18950)". Two doc-only PREPs have merged since:

| PR | Date | Title | New file added | Edits to state.md/JSON? |
|----|------|-------|----------------|-------------------------|
| #19267 | 2026-05-15T06:48Z | S3b PREP — geometric-decomposition audit + 3 corrected closure paths | `sessions/2026-05-15-s3b-prep-geometric-decomposition-audit.md` (505 LOC) | No |
| #19304 | 2026-05-15T18:14Z | S3b PREP-2 — ℤ-anchored edge-segment bridge full signature + bearer audit | `sessions/2026-05-15-s3b-prep2-edge-segment-bridge-bearer-audit.md` (607 LOC) | No |

Both PREPs are pure doc additions in `sessions/`. Neither edited state.md or
JSON. Drift items in state.md / JSON below.

---

## §2 Drift items in state.md head

(numbered for §4 traceability)

1. Line 3 `**Phase**: ACT (S3a-plus shipped)` — stale; we are in PLAN
   (post-PREP-2).
2. Line 4 `**Since**: 2026-05-14T07:30:00Z` — stale; new PREP merged
   2026-05-15T18:14Z.
3. Line 5 `**Iteration**: 7` — should be 8 (this STATE-SYNC).
4. Line 6 `**Last researcher**: researcher-9 (S3a-plus ACT ...)` — stale;
   most recent merger is researcher-4 (S3b PREP-2 #19304).
5. Line 7 `**Most recent PR**: research(...) S3a-plus ACT — primitive case
   pickInterior = 0` — stale; should be S3b PREP-2 #19304.
6. Line 9 `**Predecessor (doc-only)**: S3a-prep bearer audit (#18950, ...)`
   — stale; predecessor of S3b ACT is now S3b PREP-2 #19304 (and S3b PREP
   #19267 transitively).
7. Lines 17–24 `## Active Approach` table is missing two new rows for the
   S3b PREP and S3b PREP-2 deliverables.
8. Lines 70–84 `## Blockers` section's "Future work" still says
   `S3 — Additivity lemma` at high level (200–400 LOC); S3b PREP and
   PREP-2 have narrowed S3 into **S3b-act-1 / S3b-act-2 / S3b-act-3**
   sub-steps and pinned the bearer signatures.
9. Lines 86+ `## Next Action` describes S3b as a 200–400 LOC monolith;
   should now be **S3b-act-1** (`card_latticeSegmentPoints` Variant A,
   ~25 LOC).

---

## §3 Drift items in JSON head

JSON `currentState` head reads `iteration: 6`, `phase: "PLAN"`,
`focus: "S3a-prep done ..."`, `nextAction: "S3a ACT ..."`. This is even
more stale than state.md — missed S3a-plus ACT (iter 7) + S3b PREP (iter 7
docs) + S3b PREP-2 (iter 7 docs).

Drift items:

10. `currentState.phase` — `PLAN` is now correct (post-PREP-2) but the
    `focus` describes S3a-prep, not S3b PREP-2.
11. `currentState.iteration` — `6` should be `8`.
12. `currentState.since` — `2026-05-13T18:30:00Z` should bump to
    2026-05-16 (this STATE-SYNC).
13. `currentState.focus` — should describe S3b PREP-2's deliverable
    (`card_latticeSegmentPoints` Variant A signature + 6-bearer audit).
14. `currentState.nextAction` — should be S3b-act-1 ACT (~25 LOC, paste-ready
    from PREP-2 §2.1).
15. `currentState.attemptCounts.total` — `4` should be at least `7` (S3a-plus
    ACT + S3b PREP + S3b PREP-2 + this STATE-SYNC).
16. `knowledge.progressSummary` — last-updated text predates S3a-plus ACT;
    should mention S3a-plus + S3b PREP/PREP-2 cascade.
17. `knowledge.builtItems` — missing S3a-plus Lean deliverables + 2 PREP
    sessions/-files.
18. `knowledge.insights` — `insights[3]` still flags
    `card_latticeSegmentPoints` as "still missing"; should note that
    S3b PREP-2 supplies the full signature + 6-bearer pin + 4-step skeleton.
19. `knowledge.nextSteps` — should be re-ranked: S3b-act-1 first
    (~25 LOC, paste-ready), then S3b-act-2 / -3.
20. `updatedAt` — `2026-05-13T18:30:00.000Z` should bump to
    2026-05-16.

---

## §4 Bearer drift recheck — 6 bearers from S3b PREP-2 §5 at Mathlib pin

Mathlib lake-manifest.json `rev` is `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`inputRev: "v4.26.0"`). **Unchanged from S3b PREP-2's pin** (and from S3c-ii
ACT's pin on the lagrange slug verified at the same wall-time, ≤1h ago).
**Bearer drift: 0** at the slug level.

PREP-2 named six load-bearing Mathlib APIs (§5 + §2.1):

| # | Bearer | File at pinned SHA | Line | Verified by |
|---|--------|---------------------|------|-------------|
| 1 | `Int.gcd_eq_natAbs_gcd_natAbs` | `Mathlib/Data/Int/GCD.lean` | 50 | S3a-plus retro |
| 2 | `Int.ediv_mul_cancel` | `Init/Data/Int/DivMod/Lemmas.lean` (core Lean) | — | PREP-2 §5 |
| 3 | `Finset.card_image_of_injective` | `Mathlib/Data/Finset/Card.lean` | 242 | PREP-2 §2.2 |
| 4 | `Finset.card_range` | `Mathlib/Data/Finset/Range.lean` | (standard) | S3a-plus / PREP §6.1 |
| 5 | `PicksTheoremOQ02.card_segmentPoints` (sibling) | `Proofs/PicksTheoremOQ02.lean` | 114 | PREP-2 §2 (Variant B only) |
| 6 | `Int.natAbs_dvd_natAbs` | `Mathlib/Data/Int/Order.lean` | (standard) | S3a-plus retro (extra) |

Spot-check via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
— **deferred**; bearer presence verified at S3a-plus ACT (PR #19023) for the
overlap (#1, #4, #6) and at S3b PREP-2 §5 for the deltas (#2, #3, #5).
Without a Mathlib pin change, no re-verification needed (consistent with
`feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`).

**Conclusion**: All 6 bearers green at the current pin. S3b-act-1 can paste
PREP-2 §2.1's Variant A verbatim (~25 LOC) when next claimed.

---

## §5 Refreshed Next Action — S3b-act-1 (Variant A, paste-ready, ~25 LOC)

From PREP-2 §2.1, the canonical paste-ready add to
`Proofs/PicksTheoremOQ01OQ01OQ01.lean` (after the existing
`edgeDelta` / `edgeGCD` block):

```lean
namespace LatticeTriangle

/-- Lattice points lying on the closed segment from `v` to `w` in `ℤ × ℤ`,
    parametrised by `k · (Δ / g)` where `g = Int.gcd Δx Δy` and `Δ = w - v`.
    Generalises `PicksTheoremOQ02.segmentPoints (a b : ℕ)` (origin-anchored
    ℕ-version) to arbitrary ℤ-coord, vertex-anchored segments. -/
noncomputable def latticeSegmentPoints (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let Δ : ℤ × ℤ := (w.1 - v.1, w.2 - v.2)
  let g : ℕ := Int.gcd Δ.1 Δ.2
  (Finset.range (g + 1)).image
    (fun k => (v.1 + k * (Δ.1 / g), v.2 + k * (Δ.2 / g)))

end LatticeTriangle
```

Plus a `theorem card_latticeSegmentPoints (v w : ℤ × ℤ)` companion
proving `... .card = Int.gcd (w.1 - v.1) (w.2 - v.2) + 1`. Build step:
`./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01`.

S3b-act-1 unlocks S3b-act-2 (Case-(a) `exists_nonvertex_lattice_point`
witness construction per S3b PREP §4.1) which in turn unlocks S3b-act-3
(`realInteriorCount_union_of_shared_edge_gcd_one` additivity — the big
~200 LOC step).

---

## §6 Sylow-style parent blocker check — NONE applicable

Unlike `lagrange-theorem-oq-01-oq-01-oq-01` (where
`Proofs/SylowTheoremOQ01.lean` v4.26.0 drift blocks the full chain), the
Picks chain `Proofs/PicksTheoremOQ01OQ01OQ01.lean → Proofs/PicksTheoremOQ01OQ01.lean → Proofs/PicksTheoremOQ02.lean`
was Docker-verified clean at S3a-plus ACT (PR #19023, 3058 jobs). **No parent
blocker**; S3b-act-1 ACT can build the full chain directly without the
standalone-extract trick.

(Verified by reading the S3a-plus ACT session memo
`sessions/2026-05-14-s3a-plus-act.md` lines 1–10 confirming the Docker run.)

---

## §7 Concurrent-PR analysis — no race

`gh pr list --repo rjwalters/lean-genius --state open --search "picks-theorem-oq-01-oq-01-oq-01" --limit 5`
returned 1 open PR:

- `#18064` — research(picks-theorem-oq-01-oq-01-oq-01): S1 OBSERVE —
  primitive triangulation + GCD boundary count bridge (build verified).
  Created 2026-05-12T11:17:21Z, status MERGEABLE: CONFLICTING.

PR #18064 is **stale-conflicting since 2026-05-12** (4 days). All of its
content has been **superseded** by the subsequent S2 (#18069), S3-prep
(#18158), S3a-prep (#18950), S3a-plus ACT (#19023), S3b PREP (#19267),
and S3b PREP-2 (#19304) merges. It should be closed-as-superseded by the
deployer / mechanic / champion path, but that is out-of-scope for this
STATE-SYNC.

Conditional pivot: if #18064 is still open after 2+ more drain waves
(memory-style threshold per
`feedback_researcher_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer`),
escalate via `gh pr close 18064 --comment "superseded by #18069/#18158/#19023/#19267/#19304"`.

---

## §8 Files modified by this PR

1. `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` —
   head replacement only (lines 1–9, 17–24, 70–114). Drift items 1–9.
2. `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` —
   `currentState` + `knowledge.progressSummary` + `knowledge.builtItems`
   + `knowledge.insights` + `knowledge.nextSteps` + `updatedAt`.
   Drift items 10–20.
3. `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-16-s3b-state-sync.md`
   (this file).

**Net**: 0 Lean edits, 0 meta.json edits, 0 new theorems / sorries / axioms,
0 Docker build. ~12 min wall-time cycle (mostly bearer-spotcheck + JSON
re-rank).

---

## §9 Handoff path

Next agent should pick this slug for **S3b-act-1 ACT**: paste PREP-2 §2.1
Variant A verbatim into `Proofs/PicksTheoremOQ01OQ01OQ01.lean` (after the
existing `edgeDelta` / `edgeGCD` block, post-line ~525 per
`wc -l proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` showing 646 lines at
HEAD), add the companion theorem `card_latticeSegmentPoints`, run Docker
build `./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01`,
and ship. ~25 LOC, low-medium risk (Variant A avoids the 4-case sign split
from Variant B; only sub-step risk is the `Finset.range (g+1)` cardinality
argument for `g = 0` degenerate case — PREP-2 §3 covers).
