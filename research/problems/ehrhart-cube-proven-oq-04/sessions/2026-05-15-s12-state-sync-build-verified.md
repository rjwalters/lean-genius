# S12 STATE-SYNC — Build-Verified Confirmation + Cascade Wrap-Up

**Date**: 2026-05-15
**Researcher**: researcher-12
**Phase**: S12 STATE-SYNC (doc-only; consumes merged S9 ACT mechanic fix)
**Depends on**:
- PR #19078 (S8 BUILD-VERIFY 7-error inventory, MERGED 2026-05-15T23:26:37Z)
- PR #19220 (S9 PREP mechanic kit, MERGED 2026-05-15T18:05:33Z)
- PR #19298 (S10 PREP audit, MERGED 2026-05-15T18:00:47Z)
- PR #19303 (S11 PREP ACT-readiness gate, MERGED 2026-05-15T19:00:33Z)
- PR #19101 (S9 ACT mechanic fix, MERGED 2026-05-15T22:59:15Z, commit `be08fef58bb`)

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged from
S11 PREP; verified via `proofs/lake-manifest.json`).

## 1. Purpose

PR #19101 (mechanic) applied the seven surgical fixes recommended by
the S8 inventory → S10 PREP audit → S11 PREP ACT-readiness gate
cascade, then ran a clean Docker build:

```
$ ./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04
✔ [7743/7743] Built Proofs.EhrhartCubeProvenOQ04 (10s)
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

This **discharges** the `state.md` "Phase: BUILD-VERIFY-FAILED" gate
and the "S9 BUILD-VERIFIED PR upgrading badge to `verified` and status
to `proved`" item the prior researcher (researcher-3, S11 PREP §11)
explicitly deferred. This S12 STATE-SYNC consumes the merged mechanic
fix and updates the slug's metadata + state.md to reflect the
verified state.

**Scope (doc-only, conflict-free)**: this PR touches exactly
- `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s12-state-sync-build-verified.md` (new file, this note)
- `research/problems/ehrhart-cube-proven-oq-04/state.md` (phase + next-action rewrite, body preserved)
- `src/data/proofs/ehrhart-cube-proven-oq-04/meta.json` (4 field updates: status, badge, lineCount, theoremCount + description trim)

No Lean source edits, no sibling-session edits, no parent-file edits.
No new open PR targets these three files as of S12 PREP write time
(`gh pr list --search "ehrhart-cube-proven-oq-04 in:title" --state open
→ 0` matches; #19078 / #19220 / #19298 / #19303 / #19101 all MERGED).

## 2. Zero-drift verification: mechanic fix vs S11 PREP recommendation

The mechanic's per-site choices (PR #19101 body table) match the S11
PREP §3 drop-in patch and the S10 PREP §6 audit Option-variant
recommendation `1A / 2B / 3A / 4A / 5A / 6 / 7` exactly. The drift
recheck table below is anchored to commit `be08fef58bb` (the merged
mechanic PR).

| Err | Line | S10 audit reco | S11 PREP final | Mechanic applied | Drift |
|---|---|---|---|---|---|
| 1 | 133 | 1A: `by induction d` tactic | `by induction d` with `succ d ih => exact ih` | `by induction d` with `succ d ih => exact ih` | 0 |
| 2 | 198 | 2B: `simp [Nat.mul_zero, Nat.add_zero]` (≥ 0.6 conf) | `rw [..., mul_zero, add_zero]` top-level lemmas | `rw [..., mul_zero, add_zero]` top-level lemmas | 0 |
| 3 | 368 | 3A: `rw [hkd, Nat.sub_self, hboundary, ...]` (no `subst`) | `rw [hkd, Nat.sub_self, hboundary, ...]` | `rw [hkd, Nat.sub_self, hboundary, ...]` | 0 |
| 4 | 411 | 4A: collapse to single `ring` (≥ 0.6 conf, no `rw [Nat.add_mul]`) | single `ring` after constant rearrangement | single `ring` (drops the trailing `rw [Nat.add_mul]`) | 0 |
| 5 | 478 | 5A: `show ... by ring` + `← worpitzky_step` chain (≥ 0.6 conf) | `calc` block via `mul_comm`, then `rw [← hws]` | `calc` block via `mul_comm`, then `rw [← hws]` | 0 |
| 6 | 584 | 6: `simp only [pow_two] at ih ⊢; nlinarith [ih]` | `simp only [pow_two] at ih ⊢; nlinarith [ih]` | `simp only [pow_two] at ih ⊢; nlinarith [ih]` | 0 |
| 7 | 656 | 7: `Finset.sum_ite_eq` (non-prime; `if k = x` form) | `Finset.sum_ite_eq` | `Finset.sum_ite_eq` | 0 |

All seven sites: **zero drift** between (a) the S11 PREP-recommended
edit, (b) the S10 PREP-audit Option-variant recommendation, and
(c) the mechanic's actual application. The S11 PREP §1 promise of
"upgrades S10's three MEDIUM-confidence Option-variant recommendations
to HIGH" held: errors 2, 4, 5 all landed exactly as the goal-state
walks predicted.

S11 PREP Bug B1 (Error 5 Option B `linear_combination` fails over ℕ
due to `SubtractionMonoid` requirement) and Bug B2 (Error 2 Option A
presentation-ambiguous) did not surface — the chosen variants
sidestepped both.

## 3. Build metrics (PR #19101)

| Metric | Value |
|---|---|
| Jobs built | 7743 |
| Wall time | ~10s (Mathlib cache warm) |
| Insertions / deletions | 16 / 13 (net +3 LOC) |
| Files touched | 1 (`proofs/Proofs/EhrhartCubeProvenOQ04.lean`) |
| New sorries | 0 (preserved) |
| New axioms | 0 (preserved) |
| Sites repaired | 7 |
| Iterations to build clean | 1 (no eighth-error surface) |

The "hidden eighth error" risk from `state.md` §"Open Questions / Risks"
#1 did not materialize — all seven errors were independent and the
fixes did not surface a successor.

## 4. Cascade timeline (S8 → S12)

```
2026-05-12  S1-S7  shipped under "(build pending)" convention (7 PRs)
2026-05-14  S8     PR #19078 BUILD-VERIFY — first Docker baseline
                   surfaces 7 errors; doc-only inventory + state.md update
2026-05-15  S9 PREP PR #19220 mechanic kit (doc-only; surgical-fix
                   candidates pre-staged for mechanic application)
2026-05-15  S10 PREP PR #19298 audit of S9 kit — confirms Option A
                   safety for errors 1, 3, 4, 5; flags Bug B1/B2;
                   verifies 6 Mathlib API pins; recommends
                   1A / 2B / 3A / 4A / 5A / 6 / 7 (MERGED 18:00:47Z)
2026-05-15  S9 PREP MERGED 18:05:33Z (#19220)
2026-05-15  S11 PREP PR #19303 ACT-readiness gate — assembles 7 fixes
                   into single drop-in patch + walks goal state for the
                   three medium-confidence sites (errors 2, 4, 5)
                   (MERGED 19:00:33Z)
2026-05-15  S9 ACT  PR #19101 mechanic applies the 7-site repair,
                   Docker build clean (MERGED 22:59:15Z)
2026-05-15  S8 PREP MERGED 23:26:37Z (#19078, body owned state.md
                   until merge)
2026-05-15  S12 STATE-SYNC (this PR) consumes the cascade, syncs
                   state.md + meta.json + new session note
```

## 5. state.md update rationale

Three changes:

1. **Phase**: `BUILD-VERIFY-FAILED (S8 ...)` → `VERIFIED (S9 ACT
   #19101 merged; S12 STATE-SYNC absorbs cascade)`.
2. **Iteration**: `8` → `12` (S8 BUILD-VERIFY, S9 PREP, S10 PREP,
   S11 PREP, S12 STATE-SYNC counted as separate iterations; S9 ACT
   was a mechanic-scope sibling).
3. **Next Action** rewritten: drop the "S9 mechanic repair / S10
   audit-sync meta.json" entries (now done); add **S13 (optional)**:
   Mathlib upstream contribution path, see §7 below.

The "What's Built" inventory body is preserved (the seven `[Error N]`
annotations on the listed theorems are stripped to remove stale
build-pending markers — every theorem now build-verified) and the
"Open Questions / Risks" body is preserved (the three risks are
retrospectively retired by build success; preserved for historical
context).

The 7-error inventory in §"Blockers (S8 BUILD-VERIFY INVENTORY)" is
preserved in full — it remains the canonical surgical-fix record
should v4.26.0 → v4.27.0 (or later toolchain bumps) regress any of
the seven sites. The `Surgical fix candidate` blocks become a
reference table for future mechanic agents.

## 6. meta.json update rationale

Four field updates + one prose trim:

| Field | Before | After | Reason |
|---|---|---|---|
| `meta.status` | `formalized` | `verified` | 0 sorries, 0 axioms, 0 structure-encoded assumptions (per `grep -E "^axiom \|^structure " proofs/Proofs/EhrhartCubeProvenOQ04.lean` returning 0 lines + docstring-only "sorry" mentions); Docker build clean (per PR #19101 evidence); meets CLAUDE.md `verified` status definition |
| `meta.badge` | `wip` | `verified` | matches status; sample peer slugs (`birthday-problem-oq-01-oq-01`, `binomial-theorem-oq-02-oq-01-oq-01-oq-02`) use `badge: verified` with `status: verified` |
| `meta.lineCount` | `677` | `775` | actual `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean` post-PR-#19101 = 775; prior 677 reflected the S1-era count and never got synced through S2-S7 (a 98-line cumulative drift `fix(meta)` audit would have caught earlier) |
| `meta.theoremCount` | `27` | `30` | `grep -cE "^theorem \|^lemma " proofs/Proofs/EhrhartCubeProvenOQ04.lean` = 30 (3 PR-#18768/#18939 corollaries — `worpitzky_identity_cube_palindrome`, `cubeHStarPoly_eval_one`, `cubeHStarPoly_palindromic` — were never synced into `theoremCount` post-S6/S7) |
| `meta.definitionCount` | `2` | `2` | `grep -cE "^def \|^noncomputable def " proofs/Proofs/EhrhartCubeProvenOQ04.lean` = 2 (`eulerianNumber` at line 97 + `noncomputable def cubeHStarPoly` at line 637) — **no change**; matches reality |
| `meta.description` | "...Source has 0 sorries; build verification pending." | "...Source has 0 sorries; Docker build verified (PR #19101, 7743 jobs clean)." | retire the "build verification pending" qualifier honestly |

`assumptions: ""` is preserved — empty assumptions field already
matches a "verified" slug profile. `axiomCount: 0` is preserved.
`mathlib_version: "4.26.0"` is preserved (Mathlib pin unchanged
through the cascade).

**Axiom Integrity Policy check**: `grep -E "^axiom \|^structure " proofs/Proofs/EhrhartCubeProvenOQ04.lean` returns 0 lines, confirming no
structure-encoded hypotheses (no `NSAxioms`/`SelbergClassAxioms`/`RHAxioms` analogues). The parent file `EhrhartCubeProven.lean` has 0
sorries and 0 axioms per `grep -c "^axiom \|sorry" proofs/Proofs/EhrhartCubeProven.lean = 0`. Mathlib imports are
the only external dependency. `status: verified` is therefore the
correct call per CLAUDE.md §"Axiom Integrity Policy".

## 7. Next-step plan (S13 optional — Mathlib upstream contribution)

The Worpitzky identity for Eulerian numbers (`worpitzky_identity_cube`)
is a textbook combinatorial identity (Knuth, *Concrete Mathematics*
Eq. 6.42; Petersen, *Eulerian Numbers* Theorem 1.5). Mathlib's
`Mathlib.Combinatorics.Enumerative.Composition` and
`Mathlib.Combinatorics.Permutation` cover descents and permutation
statistics but do not currently include the Eulerian-number polynomial
identity. Three candidate Mathlib contributions surface from this
slug's verified file:

1. **`Nat.eulerianNumber`** (S3 inventory): the recurrence-based
   definition + concrete `rfl`-checks could go into
   `Mathlib.Combinatorics.Enumerative.Eulerian` (new file).
2. **`Nat.eulerian_row_sum_factorial`**: the row-sum identity
   `Σ A(d, k) = d!` is a one-paragraph proof in the verified file
   (lines 181-256). Useful as the bridge from
   `Mathlib.Combinatorics.Composition` permutation statistics.
3. **`Nat.worpitzky_identity_cube`**: the main Worpitzky identity is
   a self-contained proof (lines 442-566) using only `Nat.choose`,
   `Finset.sum`, and the Eulerian recurrence. Connects to existing
   `Polynomial.Combinatorics` infrastructure via `cubeHStarPoly`.

Upstreaming is **OUT OF SCOPE** for this STATE-SYNC PR — listed here
as the canonical follow-up so future iterations have a documented
exit ramp. The slug is now `verified` and `proved` from the Lean
Genius gallery's perspective; the Mathlib contribution path is a
separate, optional, multi-month effort.

If no S13 work is undertaken, the slug terminates here with the
existing 30 theorems + 2 defs, 0 sorries, 0 axioms, Docker-verified.

## 8. Orthogonality manifest

Files touched by this PR vs files in flight on `ehrhart-cube-proven-oq-04`:

| File | This PR | Open PR(s) targeting | Conflict risk |
|---|---|---|---|
| `proofs/Proofs/EhrhartCubeProvenOQ04.lean` | NOT touched | 0 (last touched by PR #19101 commit `be08fef58bb`, merged 22:59:15Z) | 0 |
| `proofs/Proofs/EhrhartCubeProven.lean` (companion) | NOT touched | 0 | 0 |
| `research/problems/ehrhart-cube-proven-oq-04/state.md` | UPDATED | 0 (last touched by PR #19078 23:26:37Z) | 0 |
| `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s12-state-sync-build-verified.md` | NEW | 0 | 0 |
| `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s11-prep-act-readiness-gate.md` | NOT touched | 0 (last touched by PR #19303 19:00:33Z) | 0 |
| `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s10-prep-audit-kit-pinverify.md` | NOT touched | 0 (last touched by PR #19298 18:00:47Z) | 0 |
| `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-14-s9-prep-mechanic-kit.md` | NOT touched | 0 (last touched by PR #19220 18:05:33Z) | 0 |
| `src/data/proofs/ehrhart-cube-proven-oq-04/meta.json` | UPDATED | 0 (last touched by `audit(...) PR #17878` 2026-05-12 06:11:39Z; no current `fix(meta)` in flight) | 0 |
| `src/data/proofs/ehrhart-cube-proven-oq-04/problem.md` | NOT touched | 0 | 0 |

`gh pr list --repo rjwalters/lean-genius --search "ehrhart-cube-proven-oq-04 in:title" --state open --limit 30` returns 0 matches at
write time, confirming zero overlap.

Sibling slugs touching `Mathlib` infrastructure (`Nat.choose`,
`Polynomial.coeff`, `Finset.sum_range_succ`) — e.g.
`bezout-identity`, `binomial-theorem`, `pnt-*` — are
**unaffected**: this PR makes no changes to Mathlib API consumers.

## 9. Open questions / Risks (post-verify)

1. **`theoremCount` 27 → 30 jump**: the `+3` reflects S6/S7
   corollaries (`worpitzky_identity_cube_palindrome`,
   `cubeHStarPoly_eval_one`, `cubeHStarPoly_palindromic`) that
   the prior `fix(meta) #17850/#17868/#17878` audit chain (2026-05-12)
   pre-dates. A Hermit-scope scan could check whether other slugs
   have similar count drift after multi-PR S## cascades — flagged
   for the Auditor / Hermit, not blocking this STATE-SYNC.

2. **lineCount 677 → 775 jump (+98)**: the cumulative drift across
   S1-S7 is large. None of the intervening `fix(meta)`
   audits caught it because they relied on the merged
   pre-build line count, not the post-build figure. With S12
   STATE-SYNC capping at 775, future `fix(meta)` PRs should hit
   `wc -l` parity. Not blocking.

3. **Mathlib v4.27.0 (and later) drift risk**: the 7-error pattern
   surfaced because S1-S7 shipped under "(build pending)" without
   Docker verification. With S9 ACT now Docker-verified at
   v4.26.0 (Mathlib SHA `2df2f0150c275...`), the next toolchain
   bump (whenever Mathlib pins move) should be checked via Docker
   baseline before any new S## research lands. Memory's silent-regression
   heuristic ("4+ consecutive build-pending PRs = mandatory baseline")
   applies prospectively.

4. **Upstreaming the Worpitzky identity to Mathlib**: see §7;
   optional follow-up, separate effort.

## 10. Conflict-free guarantees

This PR ships exactly three files (one new session note, two
existing-file updates). It does **not** touch:
- The Lean source (`Proofs/EhrhartCubeProvenOQ04.lean`, owned by
  merged mechanic PR #19101 — finalized)
- Any prior session file (S8/S9-PREP/S10-PREP/S11-PREP,
  finalized in their merged PRs)
- The slug's `problem.md` (canonical statement, untouched since
  initial seeker creation)
- Any sibling slug's metadata or Lean source (this PR's diff is
  fully contained within
  `ehrhart-cube-proven-oq-04/{state.md, sessions/2026-05-15-s12-*, meta.json}`)

The next iteration owner (researcher-N taking on S13 Mathlib
upstreaming OR retiring the slug) will inherit this state.md as
the canonical reference. State.md and meta.json updates are
self-contained — they do not depend on any other in-flight PR
merging first.
