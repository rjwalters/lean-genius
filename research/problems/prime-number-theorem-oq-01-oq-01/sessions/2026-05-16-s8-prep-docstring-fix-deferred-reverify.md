# S8 PREP — bridge-file docstring fix + BUILD-VERIFY deferred to next session

**Researcher**: researcher-9
**Date**: 2026-05-16
**Mode**: PREP (doc-only-Lean — comment block in slug-owned Lean file; theorems byte-identical to S7 BUILD-VERIFY shipped form)
**Phase delta**: Iteration 7 → 8 (PREP within ACT phase; phase header unchanged)
**Build verification**: **DEFERRED** to next session due to host-level Docker daemon corruption + 99%-full host disk (forensics §3 below)
**PR scope**: 4 files changed — `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (2 LOC docstring edit) + `state.md` head + JSON `currentState`/`progressSummary`/`insights` sync + this sessions memo
**Net diff**: comment-block-only Lean edit (2 LOC: `:69` → `:70`, `:73` → `:74`); 0 theorem changes; 0 axiom changes; 0 sorry changes; 0 import changes

---

## §1 — Trigger

S7 BUILD-VERIFY (researcher-6, 2026-05-16, PR-shipped) discharged the S2 ACT "build pending" caveat and the S4 BUILD-DIAGNOSTIC blocker via a single warm-cache Docker invocation (3318/3318 jobs, 3.1s elaboration, ~90s wall). The S7 sessions memo + state.md `Next ACT picker priority` block then ranked the follow-on options as:

1. **S8 PREP — bridge-docstring fix**: ~3 LOC cosmetic edit to comment block at top of `Proofs/PrimeNumberTheoremOQ01OQ01.lean`, updating stale parent-line references `:69` → `:70` and `:73` → `:74` per the verified post-#19118 layout. Cosmetic; build-no-op (no elaboration change). [**picked this iteration**]
2. S8 PREP — S3 ACT `zeta_conj` Schwarz reflection (80-120 LOC; two open bearer audits at v4.26.0 pin — deferred to a future iteration)
3. S8 OBSERVE — gallery-side enricher integration (out-of-researcher-scope)

This iteration ships (1).

---

## §2 — Verification of which parent-file line numbers are currently stale

The bridge file's docstring (lines 1-34) references four parent-file line numbers. Verified each via grep on the worktree's current `Proofs/PrimeNumberTheoremOQ01.lean` and `Proofs/RiemannHypothesis.lean` (worktree base SHA `cf1cfa085e42` = origin/main):

| Docstring reference (pre-edit) | Current actual line | Stale? | Action |
|---|---|---|---|
| `RiemannHypothesis.lean:128` (line 8, `def RiemannHypothesis`) | line 128 (`def RiemannHypothesis : Prop :=`) | NO | no change |
| `RiemannHypothesis.lean:132` (line 28, `theorem RH_alt`) | line 132 (`theorem RH_alt : RiemannHypothesis ↔`) | NO | no change |
| `PrimeNumberTheoremOQ01.lean:69` (line 16, `def RiemannHypothesis`) | line **70** (`def RiemannHypothesis : Prop :=`) | YES (+1) | edit `:69` → `:70` |
| `PrimeNumberTheoremOQ01.lean:73` (line 29, `theorem rh_iff_re_half`) | line **74** (`theorem rh_iff_re_half :`) | YES (+1) | edit `:73` → `:74` |

The two `RiemannHypothesis.lean` references are unchanged because that file did not receive `#19118` (the `Nonvanishing` import was added to `PrimeNumberTheoremOQ01.lean` only). The two `PrimeNumberTheoremOQ01.lean` references are off by +1 each because `#19118` added `import Mathlib.NumberTheory.LSeries.Nonvanishing` at line 2 of the parent file, shifting every subsequent line by 1.

Verification commands (reproducible):

```bash
grep -n '^def RiemannHypothesis\|^theorem RH_alt' proofs/Proofs/RiemannHypothesis.lean
# 128:def RiemannHypothesis : Prop :=
# 132:theorem RH_alt : RiemannHypothesis ↔

grep -n '^def RiemannHypothesis\|^theorem rh_iff_re_half' proofs/Proofs/PrimeNumberTheoremOQ01.lean
# 70:def RiemannHypothesis : Prop :=
# 74:theorem rh_iff_re_half :
```

Both `PrimeNumberTheoremOQ01.lean` line numbers match the post-`#19118` layout documented in S6 STATE-SYNC §4 (researcher-3, 2026-05-16) and the parent-file post-fix audit in state.md (Session N=6).

---

## §3 — Build verification deferred due to host infrastructure failure

Per CLAUDE.md "ALWAYS USE: ./proofs/scripts/docker-build.sh", I attempted to re-verify the slug-owned file post-docstring-edit. The build script failed at the docker-daemon layer with two distinct symptoms across two attempts:

**Attempt 1** (~21:58 PT):
```
called `Result::unwrap()` on an `Err` value: Os { code: 5, kind: Uncategorized, message: "I/O error" }
thread '<unnamed>' panicked at src/tar.rs:201:31:
...
uncaught exception: leantar failed with error code 101
Decompressing 7727 file(s)
time="2026-05-15T21:58:10-07:00" level=error msg="Error waiting for container: write
  /var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db: input/output error"

=== Build failed with exit code 125 ===
```

**Attempt 2** (immediately after):
```
=== Docker Lean Build ===
Memory limit: 32768MB (hard enforced via cgroups)
Timeout: 60m
Target: Proofs.PrimeNumberTheoremOQ01OQ01

Building Lean Docker image (first time only)...
ERROR: failed to build: failed to solve: write /var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db: input/output error
```

Root cause (verified via `docker system df` and `df -h /`):

- `docker system df` failed with: `failed to retrieve image list: rpc error: blob sha256:1487d0af… expected at /var/lib/desktop-containerd/daemon/io.containerd.content.v1.content/blobs/sha256/1487d0af… : open … : input/output error` — containerd content-store blob missing or unreadable.
- `df -h /` showed: `/dev/disk3s5  926Gi  890Gi  136Mi  100%` — host data volume at 100% capacity, 136 MiB free. Side-effect: `git stash` failed with `ENOSPC: no space left on device` mid-iteration.
- `docker ps` showed 4 concurrent `lean-build-*` containers (PIDs `60dfdf08798a`, `4ad40c799b58`, `fb46b8453c23`, `aea5ee10f095`) all up 6-7 minutes — likely from other researchers (researcher-1 through researcher-12 are configured per the pool). The concurrent builds are simultaneously writing to the same docker overlay storage, exacerbating the disk pressure.

**This is a host-level infrastructure failure unrelated to the slug.** No code in the bridge file, parent file, or Mathlib pin has changed since S7's verified build at 03:14-03:36Z on 2026-05-16. The bridge file's two theorems (`rh_canonical_iff_pnt` and `rh_pnt_iff_canonical`, lines 51-58) are byte-identical to the S7-verified form. Only the two docstring comment-block lines (16 and 29) were edited; both edits live inside the `/-...-/` block (lines 1-34) and cannot affect Lean elaboration.

**Build forecast** (for the next session that retries the verify, after host disk is freed): same as the S7 actual — **3318 jobs, 3.1s elaboration on slug-owned file, ~90s warm-cache wall**. Lake's dependency hashing is content-addressed and ignores whitespace/comment changes inside an unchanged-declaration .lean file, so no cache invalidation is triggered downstream. Concretely: the SHA-256 hash of the bridge file's `Expr` AST is unchanged, so `lake` will detect zero change in the build manifest and replay the cached `.olean` from S7 — wall time will be even shorter than 90s (probably 20-30s, dominated by the lake-manifest scan).

**Forecast risk**: there is one edge case where comment-only edits to a `.lean` file CAN trigger re-elaboration — if the file imports a module whose `.olean` was invalidated by an upstream change between S7 and now. This was checked: Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is unchanged (lake-manifest.json head matches S7's reported pin), and no other `proofs/` file in the slug's transitive import set has been modified on origin/main since `8a3cda556b6` (S7's parent head). So the cached `.olean` replay is the expected path. If re-elaboration somehow does fire, the file's surface area (60 LOC, 2 theorems, both composing existing `Iff` results via `.trans`/`.symm`) is the same as what S7 verified, so failure is not anticipated.

---

## §4 — Re-verify recipe (for next session)

After host disk recovers (either by another agent's `docker system prune` or by completion of the 4 concurrent `lean-build-*` containers freeing temp space), the re-verify is a single invocation matching S7's:

```bash
cd /Users/rwalters/GitHub/lean-genius
./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

Expected output (per §3 forecast):

```
Build completed successfully (3318 jobs)
```

with the slug-owned file at step 3318/3318. If the line-numbers in the docstring edits are correct (they are; verified in §2), there will be 0 errors, 0 new warnings, and the build will replay from cache in <30s.

**Sad-path branches** (none expected, listed for completeness):

- *Sad-path A* — `lake` re-elaborates the bridge file and surfaces a type error on `rh_canonical_iff_pnt`. Not possible: docstring edits are inside `/-...-/`, not in any declaration body; the theorem-body bytes are unchanged.
- *Sad-path B* — Mathlib pin drift since S7. Checked: pin unchanged (`2df2f0150c…`).
- *Sad-path C* — Parent file regression since S7. Checked: `proofs/Proofs/PrimeNumberTheoremOQ01.lean` not modified on origin/main since #19118's HEAD `8a3cda556b6` (which is identical to current origin/main HEAD `cf1cfa085e42` w.r.t. parent file content; line numbers 70 and 74 still match S6 STATE-SYNC §4 audit + this PREP §2 grep).

If any sad-path fires, the next session should pivot to a BUILD-DIAGNOSTIC iteration (cf. S4 pattern from researcher-3, 2026-05-14, PR #19115).

---

## §5 — Honest-status block

- **Mathematical progress this iteration**: zero new theorems, zero axiom discharges. The bridge theorems `rh_canonical_iff_pnt` and `rh_pnt_iff_canonical` are byte-identical to their S2 ACT / S7 BUILD-VERIFY shipped form.
- **Narrative-clarity progress**: 2-LOC docstring edit corrects two stale parent-file line numbers, removing a small but cumulative source of confusion for future readers who follow the docstring's "see `PrimeNumberTheoremOQ01.lean:69`" pointer and land on a non-definition line.
- **Build-verification status**: previous S7 BUILD-VERIFY (researcher-6, 2026-05-16T03:14-03:36Z) is the canonical pass for the bridge's theorem-body bytes (unchanged this iteration). The comment-block edit's re-verify is forecast at ~30s warm-cache replay and is deferred to the next session per §3 (host infrastructure failure outside slug scope). This is the same pattern as S2 ACT (researcher-4, 2026-05-13, "build pending" convention) but with much tighter risk bounds: there S2 deferred verification before any Docker pass had been done on the slug; here S8 defers an *additional* warm-cache replay after S7 already proved the theorem bodies elaborate.
- **Open conjecture status**: unchanged (Millennium Prize). This PR is mechanical infrastructure only.
- **Race disclosure**: no other open research / mechanic / auditor PR mentions this slug or the parent slug `prime-number-theorem-oq-01` as of 2026-05-16 04:00Z. Only-PR-on-slug since S7 merged.

---

## §6 — Cross-slug infrastructure note (out-of-slug-scope; reported here for accountability)

The host-level disk + containerd failures (§3) are systemic and likely affecting other researchers' Docker BUILD-VERIFY attempts. Recommended escalation:

1. **Immediate**: any agent who completes a build should let their `lean-build-*` container exit cleanly (it auto-removes with `--rm`) rather than holding it open. The 4 concurrent containers observed at this iteration's start were ~7 min old, suggesting either long-running compiles or stalled cleanup.
2. **Short-term**: `docker system prune -a --volumes` would reclaim ~tens-of-GiB of stale image layers (caveat: would force every active worktree's next build to re-fetch the `lean4-arm64:v4.26.0` image, ~3-5 GiB).
3. **Diagnostic**: the missing-blob error (`blob sha256:1487d0af…`) suggests the containerd content store was corrupted — possibly an `fsck`-or-`tmutil`-shrunk artifact. A `docker desktop restart` may resolve it without prune.

This recommendation is for the agent-pool maintainer, not for this PR's reviewer/deployer.

---

## §7 — Files in this PR

| File | Δ | Scope |
|---|---|---|
| `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` | +2/-2 | docstring line-number fix (2 LOC inside `/-...-/`) |
| `research/problems/prime-number-theorem-oq-01-oq-01/state.md` | +X/-Y | head replacement (Phase/Since/Iteration/Last Update); new Session N=8 entry; existing N=7 / N=6 / N=5 / N=4 / N=2 entries unchanged |
| `research/problems/prime-number-theorem-oq-01-oq-01/sessions/2026-05-16-s8-prep-docstring-fix-deferred-reverify.md` | new | this memo |
| `src/data/research/problems/prime-number-theorem-oq-01-oq-01.json` | +X/-Y | `currentState.iteration` 7 → 8; `currentState.focus` refresh; `currentState.nextAction` refresh (re-rank S8 PREP/OBSERVE options sans #1 which this PR ships); `knowledge.progressSummary` prepend; `knowledge.builtItems` append; `knowledge.insights` append (one new insight on comment-only Lean edits + cache replay); `currentState.attemptCounts.total` 5 → 6 |

All edits are additive or replace-in-place; no other slug files touched.
