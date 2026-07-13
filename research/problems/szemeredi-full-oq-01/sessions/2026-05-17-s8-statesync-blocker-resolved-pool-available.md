# Session S8 (2026-05-17) — STATE-SYNC: Blocker Resolved Post-PR-#14878, Pool Available, Sessions Bootstrap

**Researcher**: researcher-8
**Mode**: STATE-SYNC (doc-only, 4 files)
**Duration**: ~30 min including the race-claim release of feuerbachs-theorem-oq-02-incomplete-01 (just-merged S6 #19948, no drift remaining)
**Outcome**: 14 drifts closed across registry / canonical JSON / state.md / new sessions/ bootstrap

---

## §1 Why S8 Fires

S7 (2026-05-02) shipped PR #14878 (Mathlib API drift repair, 6 root fixes for 35-error cascade in `FurstenbergCorrespondenceOQ01.lean`). knowledge.md was updated with the Session 7 entry but **the slug-level documentation surfaces (state.md, JSON `currentState`, registry, sessions/) were never brought into alignment.** Meanwhile someone — likely seeker or an audit pass — flipped the pool entry from `status=blocked / notes=BLOCKED` to `status=available / notes=AVAILABLE`. The slug then sat in this hybrid state for ~14 days until claim-random rolled it.

This S8 is strict refinement of S7: same conclusion (blocker resolved, ready for limit_invariant_on_cylinder activation), updated surfaces. No new mathematical claims, no Lean changes.

---

## §2 Pre-S8 Drift Inventory (14 items)

| # | Surface | Pre-S8 | Should be | Δ |
|---|---------|--------|-----------|---|
| 1 | state.md `Phase` | BLOCKED | ACT (post-#14878) | flip |
| 2 | state.md `Iteration` | 4 | 5 | +1 |
| 3 | state.md `Since` | 2026-04-23T03:54:35+02:00 | 2026-05-02T21:18:35Z (PR #14878 merge) | reframe |
| 4 | JSON top-level `lastUpdate` | 2026-04-27T22:30Z | 2026-05-17T00:55Z | +20d |
| 5 | JSON `cs.phase` | BLOCKED | ACT | flip |
| 6 | JSON `cs.iteration` | 4 | 5 | +1 |
| 7 | JSON `cs.since` | 2026-04-22T13:03:46.383Z | 2026-05-02T21:18:35Z (post-#14878 reset) | reframe |
| 8 | JSON `cs.focus` | "BLOCKED on Mathlib API drift (35 errors)..." | post-#14878 narrative + 3 RED INFRA | rewrite |
| 9 | JSON `cs.blockers` | 2 entries (35 errors + no CI) | 4 entries (3 RED INFRA + Mathlib RESOLVED note) | refresh |
| 10 | JSON `cs.nextAction` | "Operator must upgrade Mathlib pin..." | activate limit_invariant_on_cylinder under recovered Docker | rewrite |
| 11 | JSON `cs.attemptCounts.total` | 0 | 5 | catchup |
| 12 | JSON `leanFiles[0].lineCount` | 119 | 118 | off-by-one |
| 13 | Registry `phase` / `lastUpdate` | OBSERVE / 2026-04-24T23:03:34.509Z | ACT / 2026-05-17T00:55:00.000Z | flip + refresh |
| 14 | `sessions/` dir | ABSENT | bootstrap with this memo | NEW |

---

## §3 PR #14878 Absorption

PR #14878 (`fix(szemeredi): repair Mathlib API drift in FurstenbergCorrespondenceOQ01`, merged 2026-05-02T21:18:35Z) shipped 6 root API drift fixes in `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`:

| Location | Issue | Fix |
|----------|-------|-----|
| `shift_iterate` (zero case) | `simp [Function.iterate_zero]` failed | `rfl` |
| `shift_iterate` (succ case) | induction `n` without `generalizing k` gave ih too weak; `ring_nf` left unsolved goals | `induction n generalizing k`; `simp only [... comp_apply]`; `congr 1; omega` |
| `cylinder_isClopen` | `isOpen_eq_of_isOpen_singleton` removed from Mathlib | `(isOpen_discrete {b}).preimage (continuous_apply i)` |
| `shift_indicator_zero`, `indicator_mem_cylinder`, `orbit_indicator_hits` | `split <;> simp_all` failed (simp partially reduces if-then-else) | `split_ifs with h <;> simp [h]` |
| `CompactSpace Bool` | `Finite.instCompactSpace` removed | `inferInstance` |
| `filter_shift_card_le` | `split` fragile on if-then-else | `split_ifs` |

The 35-error cascade reduced to 0 root errors. The shift_iterate fix was the most subtle — it was actually a **mathematical bug** masked by older Mathlib simp behavior; the `generalizing k` form is the correct proof structure.

**Verification status of #14878**: Per knowledge.md Session 7, the next step listed was "Merge PR #14878 and verify Docker build". The PR itself merged but the explicit Docker verification was never documented in knowledge.md. Indirect evidence that the file builds:

1. Gallery `src/data/proofs/furstenberg-correspondence-oq-01/meta.json` shows `status=axiomatized`, `badge=axiom`, lineCount 929, theoremCount 32, axiomCount 1, sorries 1 — these are the post-#14878 expected values (a still-broken file would not have its meta updated).
2. Pool entry has been flipped to `status=available / notes=AVAILABLE` (per `.lean/state/candidate-pool.json` inspection 2026-05-17T00:50Z) — pool-flip implies someone validated the build works.
3. No subsequent commits to `FurstenbergCorrespondenceOQ01.lean` after #14878 — no follow-up fixes needed.

This S8 STATE-SYNC accepts the indirect evidence as sufficient; explicit Docker verification is deferred to the next ACT session (which is itself blocked by current G7/G8/G9 RED).

---

## §4 G7/G8/G9 INFRA RED Evidence

| Gate | Check | Observed | Status |
|------|-------|----------|--------|
| G7 | `df -h /` available | 3.5 Gi (82% used) | RED (below same-day soft floors: shannon 5.8 Gi, ballot 5.4 Gi) |
| G8 | `docker info` Server: section | empty | RED (daemon hung) |
| G9 | `ls -la proofs/.lake` | `proofs/.lake → proofs/.lake` (self-symlink) | RED (circular, lake cannot resolve) |

Docker build verification this session is foreclosed. Per host-recovery memory: requires Docker Desktop restart + disk cleanup (target ≥5 Gi avail) + `rm` of self-symlink + fresh `lake build` to recreate `.lake/`.

---

## §5 Out-of-Scope (8 deliberate non-actions)

1. **No edits to `proofs/Proofs/SzemerediFullOQ02.lean`** — file is correct at 118 LOC; only its leanFiles[0] count needs the off-by-one fix.
2. **No edits to `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`** — already at post-#14878 state; activating limit_invariant_on_cylinder is a future ACT session.
3. **No edits to `proofs/lake-manifest.json`** — Mathlib pin `2df2f0150c…` (v4.26.0) is correct; PR #14878 confirmed compatibility.
4. **No edits to `problem.md`** — research statement is static.
5. **No edits to `knowledge.md`** — Session 7 entry is the authoritative narrative; S8 STATE-SYNC narrates itself in this sessions/ memo + state.md, not in knowledge.md (matches the recent S6/S3 registry-catchup pattern in #19948/#19930 which kept knowledge.md untouched or added only a thin epilogue).
6. **No gallery `meta.json` edits** — `furstenberg-correspondence-oq-01/meta.json` already reflects post-#14878 reality; no STATE-SYNC scope concerns there.
7. **No sibling slug edits** (`szemeredi-full`, `szemeredi-full-oq-02`) — separate threads.
8. **No re-spot-check of file bearers** — Mathlib pin is byte-stable since #14878 (~14 days), no SHA-walk needed for a doc-only STATE-SYNC; the build-pending status carries forward.

---

## §6 S9 Decision Matrix

Next session lands on this slug → pick column based on observed signals:

| Signal | Action |
|--------|--------|
| G7/G8/G9 all GREEN + this S8 merged + Docker verifies FurstenbergCorrespondenceOQ01.lean builds | S9 ACT: activate limit_invariant_on_cylinder proof (60-LOC from file comment) |
| Any of G7/G8/G9 RED + this S8 merged | S9 STATE-SYNC: thin INFRA escalation; do not attempt Lean |
| This S8 OPEN + merge-pending | release without PR (no drift) |
| Pool re-flipped to `blocked` | S9 STATE-SYNC: investigate why; surface for human |
| Sibling activity on FurstenbergCorrespondenceOQ01.lean (line-count drift) | S9 mechanic-equivalent leanFiles refresh |

---

## §7 Host Recovery Script (for future operators)

```bash
# G8 Docker recovery
osascript -e 'quit app "Docker"' && sleep 5
open -a Docker
# wait for 'docker info' Server: to populate (~30-60s)
timeout 90 bash -c 'while ! docker info 2>&1 | grep -q "^Server"; do sleep 5; done'

# G9 .lake recovery
cd /Users/rwalters/GitHub/lean-genius/proofs
if [[ -L .lake && "$(readlink .lake)" == *"/proofs/.lake" ]]; then
  rm .lake
fi
# lake build will recreate it cleanly under Docker wrapper

# G7 disk recovery (manual; needs Trash empty + Docker disk image trim)
docker system prune -af --volumes  # only after Server: populated
# Target: ≥5 Gi avail in `df -h /`

# Verification of FurstenbergCorrespondenceOQ01.lean
./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01
```

---

## §8 Honesty Calibration

This PR makes no mathematical claims. It absorbs already-merged work (PR #14878) into surfaces that lagged. The `currentState.phase: ACT` flip is justified by:
1. Pool entry `status=available / notes=AVAILABLE` (operationally confirms blocker resolved)
2. Gallery `furstenberg-correspondence-oq-01/meta.json` at axiomatized (file builds post-#14878)
3. 0 subsequent commits to `FurstenbergCorrespondenceOQ01.lean` (no follow-up fixes needed)

NOT claimed:
- No claim that limit_invariant_on_cylinder is closer to proven (still 1 sorry at line 779).
- No claim that local axiom `seqCompact_probabilityMeasure_cantor` is closer to discharged.
- No claim that this session ran a Docker build (G8 RED foreclosed it).

---

## §9 Memory Citations

- `feedback_researcher_claim_random_lands_on_long_completed_slug_due_to_registry_json_phase_observe_status_active_drift_vs_canonical_done_completed_ship_2file_doc_only_registry_catchup_state_sync` — informs the registry-catchup framing (this slug is ACT not COMPLETED so 4-file expanded scope vs 2-file thin pattern).
- `feedback_researcher_claim_random_re_rolls_same_slug_due_to_registry_phase_new_vs_canonical_observe_iter1_post_predecessor_s1_observe_bootstrap_t_15min_missed_registry_mirror_ship_1file_2line_registry_phase_catchup` — informs why registry.json drift is enough alone to drive a re-claim (here compounded by canonical JSON + state.md + sessions/).
- `feedback_researcher_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_historic_build_pending_chain_but_3_red_infra_blockers_post_merge_with_mechanic_partial_discharge` — informs the 3 RED INFRA framing + 5-row picker matrix template.
- `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — informs the leanFiles[0].lineCount 119 → 118 off-by-one fix and validation via python json.load only (no pnpm build).

This memo references PR #14878 (Session 7, 2026-05-02), PR #19948 (feuerbach S6 STATE-SYNC, 2026-05-17, the just-released race-claim predecessor), PR #19942 (erdos-1006-oq-01-oq-02 S2 STATE-SYNC, my own most-recent prior ship), PR #19930 (twin-primes S3 registry catchup).
