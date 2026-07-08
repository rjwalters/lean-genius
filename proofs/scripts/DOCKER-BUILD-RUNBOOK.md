# Docker Build Cache Corruption Runbook

Operational runbook for the recurring **exit-135 / SIGBUS** Mathlib olean
corruption class in the Lean build tooling.

## Symptom

A `docker-build.sh` run fails with **exit code 135** (SIGBUS), typically with a
message like:

```
... unexpected end of input
offset 0: unexpected end of input
```

The failure often appears on a target that **previously built green** and whose
own source did not change. It may also surface as `invalid header` when
`LEAN_SKIP_CACHE=true` is set.

## Root cause

`docker-build.sh` mounts two **persistent, fleet-shared** named Docker volumes
across every concurrent build container:

| Volume | Mount | Contents |
|--------|-------|----------|
| `lean-mathlib-cache` | `/workspace/proofs/.lake/build` | compiled `.olean`/`.trace` |
| `lean-mathlib-packages` | `/workspace/proofs/.lake/packages` | Mathlib source checkout |

When a build container is **OOM-killed** (hits the `--memory` cgroup limit)
mid-write to an `.olean`/`.trace` file, the volume can retain a **truncated**
(often zero-byte) file. Any *subsequent* build — even an unrelated, previously
green target — that imports the truncated module hits **SIGBUS** when Lean
`mmap`s it. Because the volumes are shared fleet-wide, one OOM'd build can poison
every concurrent/future build until the corrupt file(s) are repaired or the
volume reset.

The host OOMs at ~4 concurrent 32 GB builds, so this is triggered by
concurrent-fleet memory pressure.

## First-line recovery — Option B (in-place, no volume deletion)

`lake exe cache get!` — the **bang** variant force-restores/overwrites individual
corrupt/truncated oleans from the upstream Mathlib cache **without deleting the
volume**. Corrupt files are clobbered with good copies; non-corrupt files are
left alone. This is the recovery that repeatedly cleared exit-135/SIGBUS across
the research fleet without any `docker volume rm`.

```bash
# Preferred: via docker-build.sh flag
./proofs/scripts/docker-build.sh --repair-cache

# Equivalent: standalone script
./proofs/scripts/docker-repair-cache.sh
```

Properties:

- **Safe under concurrent load** — per-file overwrite, so other agents may keep
  building. No maintenance window required.
- Retries up to 2 attempts automatically.
- After it succeeds, re-run the failing build to confirm exit 0:
  ```bash
  ./proofs/scripts/docker-build.sh Proofs.ElementaryQuadraticReciprocityOQ03OQ02
  ```

If `lake exe cache get!` does **not** converge after 2 attempts, the volume may
have filesystem/metadata-level corruption (rare) rather than just individual bad
oleans — fall back to Option A.

## Fallback recovery — Option A (full volume reset)

`docker volume rm` both volumes for a guaranteed clean slate. The next build
recreates both volumes and does a full `lake exe cache get && lake build` from
empty — a large one-time cost (full ~7700-module Mathlib re-download + rebuild
of anything not covered by the upstream cache).

```bash
./proofs/scripts/docker-build.sh --repair-cache --nuke
# or:
./proofs/scripts/docker-repair-cache.sh --nuke
```

### SAFETY PRECONDITION (hard-enforced)

`--nuke` **refuses to proceed** unless `docker ps -a --filter name=lean-build`
shows **zero** containers (running or stopped). Deleting a shared volume while a
build is in flight could strand or poison it. The script performs this check and
exits non-zero with guidance if any `lean-build-*` container exists.

Verify manually before invoking:

```bash
docker ps -a --filter name=lean-build   # must be empty
```

## Prevention notes

- Prefer keeping concurrent 32 GB builds **below 4** on the shared host
  (`docker ps | grep -c lean-build`) to avoid the OOM that seeds corruption.
- The corruption is a **shared-volume** phenomenon: fixing it once (Option B)
  clears it for every agent, but a fresh OOM can re-seed it — so this is an
  operational recovery, not a permanent code fix.
- This runbook does **not** change the normal (non-repair) build path. Everyday
  `docker-build.sh Proofs.Foo` invocations are unaffected.

## Related

- Issue #35184 — this runbook / repair tooling.
- PR #35159 — same failure class (`RothTheorem.olean` SIGBUS for downstream
  importers).
- PRs #35296, #35295 — "repair masked broken build" landings that demonstrated
  the toolchain compiles cleanly again after the acute 2026-07-08 episode
  self-healed.
