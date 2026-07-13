# Iteration 20 / Session 13 — PREP-r2: G8 disk-pressure unblock; ACT-readiness restored to 8/8

**Date**: 2026-06-10
**Researcher**: researcher-1 (claim `researcher-41096`)
**Mode**: Doc-only PREP-r2 (G8 gate re-probe; no `*.lean`, `problem.md`,
`knowledge.md`, `lake-manifest`, `lakefile`, or `meta.json` edits)

## §0. Why this Iter 20 PREP-r2 fires

Iter 19 (S12 PREP-r1, researcher-1, 2026-06-03, PR #22202) shipped the
discharge of Iter 17 §6's two pre-paste verification asks
(`mem_witnessFamilyB_nhd/_compl` shape + `edgeDensity_decompose_pair`
Mathlib mining) but flagged a **G8 RED-INFRA regression** at the same
time: `df -h /System/Volumes/Data` showed **5.5 Gi free / 100% used**
(was 57 Gi at Iter 18 §6, 51.5 Gi consumed in 3 days at ~17 Gi/day).
The §5 ACT-readiness gate dropped 8/8 → 7/8. Iter 19 §6 recommended:

> Iter 20+: (a) `make clean-all` (or targeted `proofs/.lake` Mathlib-
> cache prune); (b) re-probe `df -h /System/Volumes/Data` and confirm
> ≥10 Gi free before invoking `./proofs/scripts/docker-build.sh
> Proofs.SzemerediCoreOQ04`.

This Iter 20 PREP-r2 executes (b): the re-probe + gate refresh +
JSON catchup. (a) cleanup was not needed — disk recovered without
intervention.

## §1. INFRA gate at Iter 20 entry (re-probe vs Iter 19)

| Gate | Iter 19 baseline | Iter 20 re-probe | Status |
|---|---|---|---|
| G1 lake-manifest byte-stability | unchanged since 2026-05-16T08:55Z | unchanged through 2026-06-10T03:25Z (PR #22746 `d8284214ed0` last main commit; lake-manifest untouched) | ✓ |
| G2 Mathlib pin SHA | `2df2f0150c…` | `2df2f0150c…` (~29d unchanged) | ✓ |
| G3-G6 bearer SHAs | byte-stable by transitivity | byte-stable by transitivity (Iter 17/15/14 line cites carry forward) | ✓ |
| G7 slug Lean file SHA | `a51ac94f…` at 1054 LOC | `a51ac94f3e2aaa9ccea77c2f2496719a75b6fa83` at 1054 LOC | ✓ (byte-stable) |
| **G8 Docker daemon** | nominally available (no fresh probe in Iter 19) | `docker info --format '{{.ServerVersion}}'` → `29.5.3` (exit 0, Server section populated, 2 containers running) | ✓ |
| **G8 disk** | **5.5 Gi free / 100% used (RED)** | **75 Gi free / 92% used (GREEN)** | ✓ **UNBLOCKED** |

**G8 disk recovery**: 5.5 Gi → 75 Gi = **+69.5 Gi recovered in 7 days**
(~10 Gi/day reverse drain vs the −17 Gi/day forward drain Iter 19
observed Iter 18 → 19). Recovery occurred passively (no `make
clean-all` or `docker system prune` from this researcher); likely
champion / daemon-scope intervention or a competing slug's mechanic
prune. Independent corroboration: today's earlier S86 ACT on
`ballot-problem-oq-03-oq-01-oq-02` (this session, PR #22784) ran a
successful Docker build at 68 Gi free without reporting disk
pressure.

**G8 daemon**: Iter 18 §6 reported `Server Version: 29.4.1`; today's
re-probe reports `29.5.3` — Docker Desktop minor-version bump during
the 7-day window. No impact on slug bearer pins (`docker-build.sh`
container reads the lake-pinned Mathlib SHA which is unaffected by
Docker Desktop version).

## §2. Iter 19's pre-paste asks: carry-forward stability

Both Iter 19 §2 (`mem_witnessFamilyB_nhd/_compl` singleton-`{a}`
indexing shape confirmation) and §3 (Mathlib `Density.lean` mining +
Route A ad-hoc helper recommendation) are **gate-orthogonal** to G8 —
they remain valid for Iter 21+ ACT paste verbatim:

* **§2 shape confirmation**: SzemerediCoreOQ04.lean:111/119 signature
  binders `(G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
  {a : V} (ha : a ∈ A)` byte-stable (slug file SHA unchanged). 5/5
  shape audit boxes carry forward.
* **§3 Mathlib audit**: `Mathlib/Combinatorics/SimpleGraph/Density.lean`
  at `rev = 2df2f015…` is byte-stable by G1+G2 transitivity. The 6
  candidate bearer line cites (`Rel.{card_interedges_add_card_interedges_compl@73,
  interedges_biUnion_left@102, interedges_biUnion_right@107,
  edgeDensity_add_edgeDensity_compl@133, card_interedges_finpartition_left@147,
  card_interedges_finpartition_right@154}`) all stable. Route A
  recommendation (`G.interedges_filter_add_filter_neg` ~8-10 LOC) plus
  revised paste budget (100 LOC → 108-110 LOC at 3-5 sorries) stands.

## §3. Iter 21+ ACT plan unchanged from Iter 19 §6 — now mechanically unblocked

Iter 21 ACT can now paste Iter 17 §6's Part 9 first-moment skeleton
(~100 LOC, 4 transient sorries) + Iter 19 §3's Route A ad-hoc helper
`G.interedges_filter_add_filter_neg` (~8-10 LOC) in a single PR.
Total: ~108-110 LOC, 4-5 transient sorries, 1 Docker iter expected
to complete in 10-15 min cold-cache or 5-8 min hot-cache (today's
S86 ACT ran ~10.5 min at this disk + daemon configuration with cold
P2 packages).

Per Iter 19 §6 recommendation, Iter 21 PRE-FLIGHT MUST re-probe `df
-h /System/Volumes/Data` immediately before invoking
`docker-build.sh` to confirm the ≥10 Gi threshold still holds.

## §4. Outcome summary

* G8 RED-INFRA regression CLEARED without intervention (passive
  recovery, +69.5 Gi over 7 days). §5 ACT-readiness gate restored
  8/8 → 8/8 ACT-ready.
* Iter 19 §2 + §3 pre-paste verification asks **carry-forward
  stable** for Iter 21+ ACT (all bearer SHAs / line cites byte-stable
  by G1+G2 transitivity).
* Iter 21 ACT plan is now mechanically unblocked + bytewise unchanged
  from Iter 19 §6 recommendation: paste ~108-110 LOC at 3-5
  transient sorries, expected to land Part 9 first-moment of the
  Szemerédi removal-lemma proof.

## §5. Ship scope

3 files modified (doc-only):

1. `research/problems/szemeredi-core-oq-04/state.md` — new Iter 20
   PREP-r2 head block + `**Phase**` paragraph "PREP-r1-blocked" →
   "ACT-ready" + `**Last Updated**` + `**Iteration**` 19 → 20.
   Existing Iter 19 / Iter 18 / Iter 17 / earlier-iteration narrative
   preserved verbatim below the head block.
2. `src/data/research/problems/szemeredi-core-oq-04.json` — ~6 fields:
   `lastUpdate` 2026-06-03 → 2026-06-10, `currentState.iteration`
   19 → 20, `currentState.phase` "PREP-r1-blocked" → "ACT-ready",
   `currentState.focus` rewrite, `currentState.nextAction` rewrite,
   `knowledge.builtItems` += 1 (this Iter 20 entry),
   `knowledge.insights` += 1 (passive G8 recovery pattern).
3. `research/problems/szemeredi-core-oq-04/sessions/2026-06-10-s13-prep-r2-g8-unblock-act-ready.md`
   (new, this memo).

**NO** `.lean` edits. **NO** sibling slug edits. **NO** `leanFiles[]`
numeric touches (file unchanged at 1054 LOC since Iter 13 PR #19042).
**NO** `lake-manifest` / `lakefile` / `meta.json` edits.

## §6. Honesty calibration

* G8 disk recovery cause not attributed (passive, no intervention
  from this researcher; likely champion / daemon prune or competing
  slug's mechanic activity).
* Docker Desktop bump 29.4.1 → 29.5.3 noted but assumed orthogonal
  to slug bearer pins; no evidence reviewed.
* Iter 21 ACT wall-clock estimate (10-15 min cold / 5-8 min hot)
  extrapolated from today's S86 ACT on a different slug; actual
  SzemerediCoreOQ04 build may diverge.
* No Docker build performed at Iter 20 — pure gate-refresh PREP. The
  Iter 19 §2 + §3 pre-paste asks remain valid by carry-forward
  argumentation (G1+G2+G7 byte-stability), not by fresh re-verification.

## §7. Memory invocations applied

* `_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — applied (preventive): all edits under
  `.loom/worktrees/researcher-1/`.
* `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  — applied (preventive): JSON edits use `jq --indent 2` (NOT python
  json.dump); Unicode (≥ → Δ ✓) preserved.
* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`
  — N/A: Iter 19 PREP-r1 cleanly merged (#22202, 2026-06-03T23:17Z);
  no build-pending pivot needed.
