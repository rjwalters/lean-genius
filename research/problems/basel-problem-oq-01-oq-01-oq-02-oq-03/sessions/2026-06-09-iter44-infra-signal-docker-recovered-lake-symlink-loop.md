# Iteration 44 INFRA-SIGNAL — Docker host RECOVERED; `.lake` self-loop is the new blocker

**Date**: 2026-06-09
**Researcher**: researcher-1
**Phase**: INFRA-SIGNAL (doc-only; signals partial unblocking of the Iter 43
PREP's `## Infrastructure` ACT gate.)
**Type**: Doc-only. No edits to
`Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, `knowledge.md`,
`problem.md`, or gallery `meta.json`. Edits limited to this session log,
`state.md` (Iter 44 narrative + header refresh), and
`src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`
(`currentState.iteration`/`phase`/`focus`/`nextAction` + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since Iter 36).
**Base HEAD**: `535c25c5e60` (current `origin/main`).

## Headline

Iter 43 PREP (2026-06-03) flagged ACT as blocked on the Docker host's
degraded state: corrupted-blob I/O error on the
`lean4-arm64:v4.26.0` backing image `9026c55995f4`, plus a wedged
`lean-build-57602` container reporting "Up 31 hours" via `docker ps`
but "dead" via `docker inspect`. Iter 44 confirms **the Docker host
has recovered**:

* `docker info`, `docker ps`, `docker run --rm` all succeed cleanly.
* `lean4-arm64:v4.26.0` is present with new image ID
  **`sha256:8768de35b1f4cb4b947670b2003e029e9a79bc25931c76fb3a5583c53e64c493`**
  (≠ Iter 43's corrupted `9026c55995f4`); the image was rebuilt or
  re-pulled at some point between 2026-06-03 and 2026-06-09. `docker
  images` reports `lean4-arm64:v4.26.0` 4.08GB disk usage / 902MB
  content size, created 4 days ago.
* A test `docker run --rm lean4-arm64:v4.26.0 echo "docker exec OK"`
  succeeds.

**However**, ACT remains blocked by a **distinct, newer infrastructure
issue** that was *not* present at Iter 43 time and that the iter43
remediation checklist does not address: the host's
`/Users/rwalters/GitHub/lean-genius/proofs/.lake` is a **self-referential
symlink loop**, mirrored into all researcher worktrees (whose
`.loom/worktrees/researcher-N/proofs/.lake` are symlinks to the broken
main-repo target). This is the same trap intermittently logged in the
shapley-folkman-oq-01 Session 16 / 17 records and in the
`feedback_researcher_lake_symlink_loop_and_wipe` user-memory note.
Docker mounts the host repo at `/workspace`, so the broken symlink
propagates into the container and `lake build` fails to resolve
`/workspace/proofs/.lake`.

The net effect: **Docker side of the ACT gate is GREEN; the host
`.lake`-symlink side is RED.** Iter 44 documents the new state so the
next researcher's pre-flight checklist starts from the right place.

## Verification record

### Docker host probes (2026-06-09 ~17:25Z)

```
$ docker info | head -5
Client: Docker Desktop ...
Server: Docker Engine, no daemon errors

$ docker images --no-trunc lean4-arm64:v4.26.0
REPOSITORY    TAG       IMAGE ID                                                                  CREATED      SIZE
lean4-arm64   v4.26.0   sha256:8768de35b1f4cb4b947670b2003e029e9a79bc25931c76fb3a5583c53e64c493   4 days ago   4.08GB

$ docker run --rm lean4-arm64:v4.26.0 echo "docker exec OK"
docker exec OK

$ docker ps
CONTAINER ID   IMAGE     COMMAND   CREATED   STATUS    PORTS     NAMES
(no running containers — the wedged lean-build-57602 from Iter 43 has
since been cleared)
```

All four signals contradict Iter 43's `## Infrastructure: Docker host
degradation (NEW, blocks ACT)` snapshot. The 11-GiB-disk-slack warning
from Iter 43 was specific to the corrupted-blob scenario; the new
healthy image's 902MB content size leaves plenty of headroom.

### `.lake`-symlink probes (host side)

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 Jun  9 12:36
  /Users/rwalters/GitHub/lean-genius/proofs/.lake
  -> /Users/rwalters/GitHub/lean-genius/proofs/.lake

$ ls /Users/rwalters/GitHub/lean-genius/proofs/.lake/
ls: /Users/rwalters/GitHub/lean-genius/proofs/.lake/:
   Too many levels of symbolic links
```

The main repo's `proofs/.lake` is a symlink **to itself**. Every
researcher worktree's `proofs/.lake` is a symlink to this broken main-
repo target and therefore equally unusable. A docker-build attempt
would have its `-v "${REPO_ROOT}:/workspace:delegated"` mount carry the
broken symlink into the container, and the cache-volume mount
`-v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated"` cannot
resolve its target inside the broken `.lake/` parent.

### What this is NOT

This is **not** a transient `docker pull` failure, not a corrupted-
blob recurrence, and not a fresh Docker daemon wedge. The Docker side
of the system is healthy. The blocker is a filesystem-level symlink
mistake on the host's main-repo working copy (likely from a botched
`make clean-all` or worktree cleanup that nuked the `.lake/` contents
and left a self-loop placeholder).

## Iter 43 PREP block — paste-readiness preserved

The Iter 43 PREP §"Consolidated paste-ready block (Iter 43 PREP §'The
full ACT')" (~85 LOC) is **mathematically unchanged**. No new Mathlib
bearer drift since 2026-06-03 (lake SHA is the same pinned
`2df2f0150c…`; no new Mathlib release between 2026-06-03 and
2026-06-09). The block is still the correct next-ACT target once the
`.lake` self-loop is remediated.

Iter 43's 13 bearers — `Complex.betaIntegral_eval_nat_add_one_right`,
`ascFactorial` identification chain, plus three NEW Mathlib-core
bearers `Nat.eq_of_mul_eq_mul_right` / `Nat.factorial_pos` /
`Nat.factorial_succ` — are entry-level and not at risk of drift.

## Remediation paths for `.lake` self-loop

Iter 44 records but does NOT attempt these — they involve mutating
the host-side `.lake` link and the right move is to let the next
ACT-capable researcher (or a dedicated doctor PR) handle it cleanly:

### Path A — clean re-init (recommended)

```bash
# From host shell, with repo at /Users/rwalters/GitHub/lean-genius:
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake   # delete the loop
cd /Users/rwalters/GitHub/lean-genius/proofs
# Run docker-build for any small target to let lake initialise:
./scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03
```

The first build will create a fresh `.lake/` directory and download
Mathlib cache into the persistent Docker volume `lean-mathlib-cache`.
Wall-clock estimate: 10-20 min on the cache-miss first run, then
~30s-10min for incremental builds.

### Path B — restore from a sibling repo

If another clone of the repo on the same host has a healthy `.lake/`,
copy that directory (with all its tree) over. Less safe; the
`.lake/build/` cache may not match the lake-pinned SHA's expectations.

### Path C — worktree-level workaround

Researcher worktrees inherit the broken link from the main repo. A
worktree-only fix (`rm worktree/proofs/.lake; ln -s
/path/to/healthy/.lake worktree/proofs/.lake`) requires a healthy
target to point at and so depends on Path A or B succeeding first.

## What this PREP does NOT include

1. **No Lean edits**. File byte-identical to Iter 38 ACT state
   (md5 `4b4ac86002cb4c60b7a2863c157dad48`, 1802 LOC).
2. **No build verification** (Docker is healthy but `.lake` self-loop
   precludes any actual build attempt regardless of Docker state).
3. **No edits to `knowledge.md`, `problem.md`, or gallery `meta.json`**.
4. **No re-derivation of the Iter 43 paste-ready block**. Iter 43's
   §"Consolidated paste-ready block" is the next-ACT target unchanged;
   only the infrastructure preconditions have shifted.
5. **No host-side filesystem mutations**. The `.lake` self-loop is
   documented but not deleted by this iteration — that mutation
   belongs in the ACT-attempting iteration.

## Honest framing / self-audit

* **Half-unblocking is real progress**. The Iter 43 remediation
  checklist had four steps: (a) `docker rm -f lean-build-57602`,
  (b) `docker system prune -a --volumes`, (c) re-pull / rebuild the
  lean4 image, (d) confirm `docker exec` works. Items (a) and (d) are
  confirmed satisfied; (b) and (c) were likely run between
  2026-06-03 and 2026-06-09 (new image ID is direct evidence). The
  Docker side is genuinely fixed.

* **The new `.lake` blocker may have been there all along**. The
  `feedback_researcher_lake_symlink_loop_and_wipe` user-memory note
  exists from prior incidents on different slugs (most recently
  shapley-folkman-oq-01 Sessions 16/17). It is possible — even
  likely — that the symlink loop was present during Iter 43 as well
  and Iter 43 attributed all ACT-side build inability to the Docker
  issue. With Docker now ruled out, the `.lake` loop becomes the
  visible failure mode.

* **This INFRA-SIGNAL is the right size**. Iter 44 is a 1-of-2
  STATE-SYNC-cap iteration (no prior STATE-SYNC this researcher this
  session). It records the genuine infrastructure-state change
  cleanly without claiming any Lean-side progress. Iter 45+ should be
  a fresh ACT attempt after the symlink remediation, OR another PREP
  if the next researcher prefers to wait until a doctor has confirmed
  the `.lake` reset.

* **Iter 43 paste-ready block bearer audit not redone**. Six days have
  elapsed since the Iter 43 bearer audit at lake SHA
  `2df2f0150c…`. No Mathlib bearer drift is expected (no new pin, no
  new Mathlib release between 2026-06-03 and 2026-06-09 at the
  lake-pinned SHA). The next ACT iteration may want to do a one-line
  sanity probe `grep ascFactorial_succ_left ...` against the lake
  clone once `.lake` is restored, but should not block on it.

## Cross-references

- Iter 36 PREP (2026-05-15, #19499): 28b-2 paste-ready discharge.
- Iter 37 INFRA-SIGNAL (2026-05-25, #20636): Docker gate RED→GREEN
  (first time); template for this iter's structure.
- Iter 38 ACT (2026-05-28, #20863): 28b-2 witness saturation shipped.
- Iter 39 PREP (2026-05-31, #21401): 28a paste-ready skeleton.
- Iter 41 PREP (2026-06-01, #22033): bearer re-verify + IBP probe.
- Iter 42 PREP (2026-06-02, #22114): cast-bridge consolidation.
- Iter 43 PREP (2026-06-03, #22167): linear_combination algebraic gap
  + corrected ℕ-descent discharge + Docker-host degradation flag.
- shapley-folkman-oq-01 Sessions 16/17 (2026-06-04): same `.lake`
  symlink trap, different slug.
- User memory `feedback_researcher_lake_symlink_loop_and_wipe`:
  the canonical write-up of this filesystem state.

## What the next researcher should do (Iter 45+)

**Pre-flight (infrastructure, two-step instead of Iter 43's four-step)**:

1. **Confirm `.lake` self-loop**:
   ```bash
   ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
   # Expected: -> /Users/rwalters/GitHub/lean-genius/proofs/.lake (broken)
   ```
2. **Reset via Path A** (delete the loop; let docker-build re-create
   `.lake/`):
   ```bash
   rm /Users/rwalters/GitHub/lean-genius/proofs/.lake
   cd /Users/rwalters/GitHub/lean-genius/proofs
   ./scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03
   # First run: 10-20 min for cache-miss + small target build.
   ```

**Lean ACT** (verbatim from Iter 43 PREP §"The full ACT"):

1. Add the two imports at the top of
   `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`.
2. Paste the Iter 43 ~85-LOC corrected block after
   `exists_witness_choose_saturates_log_succ` (line 1661).
3. `./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ03`.
4. Apply Iter 43 §"Honest framing" cast-syntax fallbacks if the
   terminal `linear_combination h_key_C` needs a `ring_nf; exact
   h_key_C` swap.

**Estimated wall-clock**: 10-20 min for the `.lake` re-init + 5-10 min
for the actual Iter 43 paste-ready ACT + 5 min for commit / PR.
Total: 20-35 min when the `.lake` host is freshly reset.
