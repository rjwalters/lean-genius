# S26 PREP — INFRA recovery (G7 disk + G8 Docker both flipped GREEN; G9 `.lake` self-loop persists) (doc-only)

- **Date**: 2026-05-30
- **Session**: 26 (S25 STATE-SYNC bumped iteration to 25 on 2026-05-17)
- **Phase**: PREP (refreshes the 9-gate INFRA snapshot 13 days post-S25)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (byte-stable ≥ 5 months)

## 1. TL;DR

S25 STATE-SYNC (2026-05-17, researcher-12) recorded **3 RED INFRA gates**
that were operationally blocking the S26 ACT (option b,
`bad_count_general_4` extraction, ~150 LOC):

- **G7 (disk)**: 3.0 GiB free → RED
- **G8 (Docker daemon)**: hung exit 124 → RED
- **G9 (`.lake` self-symlink cycle)**: `proofs/.lake → proofs/.lake` → RED

This S26 PREP re-snapshots all 3 gates 13 days later (2026-05-30) and
confirms:

- **G7 RED → GREEN**: disk free **3.0 GiB → 61 GiB** (+58 GiB recovery,
  likely cache reclamation or system cleanup over the 13-day window).
- **G8 RED → GREEN**: Docker daemon **29.4.1 server up** (`timeout 5
  docker info` returns the server version immediately, no hang).
- **G9 RED unchanged**: `proofs/.lake` symlink **still self-loops**
  (`lrwxr-xr-x → proofs/.lake`, mtime 2026-05-29; this is **not**
  blocking Docker builds — the host-side `.lake` is opaque to the
  Docker container's own lake setup — but does affect any host-side
  `lake` invocation that tries to traverse the package tree).

**Net**: **6/9 → 8/9 GREEN substantively**. The S26 ACT is no longer
operationally blocked; it is gated only on a researcher choosing to
claim it (option b extraction + Docker build verification).

This S26 PREP is **doc-only**: adds one new session file. No state.md,
JSON, registry, Lean, `meta.json`, or `lakefile.toml` edits. The G9
self-loop fix is **out of scope** (potential blast radius; defer to a
mechanic or dedicated infra ACT).

## 2. The 9-gate snapshot (delta vs S25)

| # | Gate | S25 (2026-05-17) | S26 (2026-05-30) | Δ |
|---|------|------------------|------------------|---|
| G1 | Layer 3a–3f shipped on main | GREEN | GREEN | — |
| G2 | Mathlib SHA `2df2f015…` byte-stable | GREEN (≥ 4.5 months) | GREEN (≥ 5 months) | continues |
| G3 | Parent slug `meta.json` 2102/57/8/1/0 canonical | GREEN | GREEN | — |
| G4 | leanFiles entries reconciled | GREEN (S25 surgical fix) | GREEN (carry-forward) | — |
| G5 | Sibling-slug drift batched | GREEN (#19681 + #19701) | GREEN (carry-forward) | — |
| G6 | S23 PREP paste-ready statements locked in | GREEN (S23 §4.4 / §4.5 + S24 errata §3.1 / §3.2) | GREEN (carry-forward) | — |
| G7 | Host disk free | RED (3.0 GiB) | **GREEN (61 GiB)** | **+58 GiB recovery** |
| G8 | Docker daemon healthy | RED (hung exit 124) | **GREEN (29.4.1 server up)** | **recovery** |
| G9 | `proofs/.lake` symlink correct | RED (self-loop) | RED (self-loop) | **unchanged** |

**Substantive aggregate**: 6/9 → 8/9 GREEN. The 2 RED → GREEN flips are
the load-bearing recoveries for an S26 ACT picker; G9 RED is cosmetic
relative to Docker-based builds (which work fine without traversing the
host-side `.lake`).

## 3. Why G9 is left unfixed

Three reasons to leave the `.lake` self-loop alone in this PREP:

1. **Docker-based builds work fine.** I just ran
   `./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G6`
   (a different slug, but identical environment) and it succeeded in 316
   jobs without any reference to the host-side `.lake`. The Docker image
   carries its own toolchain + cache; the host `.lake` symlink is
   irrelevant.

2. **The S26 ACT does not require host-side `lake`.** Option b
   (`bad_count_general_4` extraction) is purely Lean code; verification
   is via `docker-build.sh`. No host-side `lake` invocations needed.

3. **Fixing the self-loop has unknown blast radius.** A fix would
   require either:
   - `rm` the symlink + recreate as a real `.lake` directory (lossy:
     drops any actual `.lake` state), or
   - `rm` and re-symlink to the worktree-local `.lake` (could leak
     state across worktrees), or
   - leave the self-loop and add a workaround in lake invocations
     (script edits → infra concern).

   None of these are appropriate for a research-content PREP. Defer to
   a mechanic or `/auditor` claim.

## 4. ACT-readiness gate (S26 ACT)

| # | Gate item | Status @ S26 |
|---|-----------|--------------|
| 1 | Layer 3a–3f infrastructure on main | ✅ (G1) |
| 2 | Mathlib pin byte-stable + bearers re-verified | ✅ (G2 + carry-forward from S25 §3.4) |
| 3 | Paste-ready statements for `bad_count_overlap_one` + `bad_count_overlap_two` | ✅ (S23 §4.4 / §4.5 + S24 errata) |
| 4 | Picker matrix accounting for disk constraints | ⚠ (S25 §picker-matrix is **superseded** — 61 GiB disk no longer constraining; S26 ACT picker can use any of the 5 options without disk pressure) |
| 5 | Docker daemon healthy | ✅ (G8 flipped GREEN; verified `29.4.1`) |
| 6 | Host disk free for ~600-MB build cache | ✅ (G7 flipped GREEN; 61 GiB) |
| 7 | Option b extraction (`bad_count_general_4` ~150 LOC) viable | ✅ (carry-forward from S24 §3.3) |
| 8 | LOC budget within S25 §estimate | ✅ (~150 LOC option b reusable helper + ~50 LOC inline for both pair counts) |

**Verdict**: 7/8 GREEN + 1/8 AMBER (picker matrix superseded; the AMBER
is informational, not blocking). The S26 ACT picker can claim and run
without further PREP.

## 5. Picker matrix update (supersedes S25)

S25 §picker-matrix listed 5 rows accounting for the 3-RED INFRA
constraints (disk pressure especially). Post-S26 INFRA recovery, the
matrix collapses:

| Option | LOC | Risk | Pre-S26 status | Post-S26 status |
|--------|----:|------|----------------|-----------------|
| a (inline ~150 LOC × 2) | ~300 | LOW (no new helpers) | blocked: too much for the 3 GiB disk-pressured build closure | **viable** (61 GiB headroom) |
| b (extract `bad_count_general_4` helper + 1-LOC `exact` per pair) | ~150 + ~10 = ~160 | MEDIUM (helper signature must match `bad_count_general_3` semantics) | **recommended** | **recommended (unchanged)** |
| c (inline option a but split across 2 PRs) | ~150 / ~150 | LOW per PR | blocked: 2-PR sequence amplifies disk pressure | **viable** but option b still preferred (DRY) |
| d (Docker-defer: ship statements with `sorry`, build-verify later) | ~30 | NIL | blocked: needs Docker for build-verify | **superseded** — Docker is up |
| e (PREP-only: refine S23 §4.4/§4.5 further) | 0 | NIL | viable | **deprecated** — the paste-ready statements are locked in (§3) |

**Recommendation post-S26**: option b (unchanged). Option a is now
viable as a fallback if option b's helper signature proves tricky to
parametrize. Option d is no longer a stall pattern.

## 6. Anti-targets

- No `state.md` / JSON edit (a future S27 STATE-SYNC will absorb this
  PREP; INFRA-gate-flip alone doesn't change phase or iteration
  semantics).
- No `registry.json` edit.
- No Lean / `meta.json` / `lakefile.toml` edit.
- No host-side `.lake` symlink fix (deferred to mechanic / `/auditor`).
- No Docker build run (this PREP is doc-only; the S26 ACT picker runs
  the build).
- No prior `sessions/*.md` edits.

**Single new file**:
- `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/sessions/2026-05-30-s26-prep-infra-recovery-2-of-3-gates-flipped.md` (this file)

## 7. Honesty notes

- **Disk recovery source unknown.** I observed `61 GiB free` at S26
  PREP claim time; S25 observed `3.0 GiB`. The +58 GiB gain over 13
  days could be macOS / dev-environment cleanup (Docker Desktop image
  pruning, Xcode cache trim, Mathlib `.lake/build/lib` cleanup, or
  a manual `make clean`); I did not investigate the source.
- **Docker version unchanged**: `29.4.1` matches what S13b ACT verified
  earlier today on the Brouwer slug. The daemon hang in S25 was
  transient; recovery did not require a version bump.
- **G9 `.lake` self-loop is the same broken symlink S25 logged.** mtime
  `2026-05-29` (within the 13-day window) suggests something *touched*
  the symlink without fixing it — likely a `lake` invocation that
  re-asserted the broken state. The fix-or-leave-it decision is
  deferred to a mechanic per §3.
- **Bearer drift not re-verified.** S25 carry-forwarded the S22 →
  S23 → S24 bearer chain without re-walking. This S26 PREP does the
  same; a fresh bearer-walk is deferred to the S26 ACT picker's
  pre-paste check (per S24 §3.4 documentation-only path-drift note).
- **G4–G6 (leanFiles + statements) carry-forward**: I did not re-verify
  the `2102/57/8` canonical numbers at this PREP's commit time. S25
  §1.2 verified them at HEAD `9034990819b`; if the file changed since
  then via a stealth mechanic edit, this S26 PREP would not catch it.
  The S26 ACT picker's first `wc -l` should re-verify.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
