# Remote Autoscaling `lake build` Server Pool — Design

Status: **Design / first increment.** Part of #38684 (parking-lot / future work — not
blocking the epic #37508 migration, which continues on localhost). No cloud resources are
provisioned by this document or the accompanying scaffolding; everything here is a plan plus
a dry-run-only job-submission stub.

---

## 1. Problem statement

Lean verification throughput is currently pinned to a single host. During the epic #37508
toolchain migration (v4.26 → v4.31) the residual failure ledger is burned down by running
many parallel Docker Lean builds, and we repeatedly hit hard localhost ceilings:

- **Docker VM RAM cap** — each Lean build's `--memory` limit means ~4 concurrent builds is
  the safe ceiling on the current VM; 8+ OOM with `EXIT=137` (e.g. Wolstenholme / TestApi203).
  Raising the VM allocation helps but is bounded by the one host.
- **Boot-disk pressure** — Docker's `Docker.raw` image (~143 GB incl. warm Mathlib caches)
  is the documented root cause of past SIGBUS build storms when the boot disk fills to 100%.
  (Mitigated by relocating the image to `/Volumes/Stripe/docker`.)
- **Per-slot cache volumes** — each concurrent container needs its own ~21 GB `.lake/build`
  cache volume to avoid write races, so localhost parallelism scales in disk too.

A remote pool lets the number of parallel verification jobs scale with demand (dozens of
single-proof jobs at once) instead of being pinned to one machine's RAM/disk, while scaling
to zero when idle to control cost.

**Scope note.** This is *deterministic verification* build capacity. It is orthogonal to
**Aristotle** (external proof *search*) and complements — does not replace — the local Docker
recipe in `proofs/scripts/docker-build.sh` / `proofs/batch2/STATUS.md`.

---

## 2. Prerequisite: AWS EC2 vCPU quota increase (BLOCKER)

**This wall was hit while scoping this issue and must be cleared before any worker pool can
run at useful scale.** For AWS account `221082181346`:

| Quota (us-west-2) | Current limit | Needed |
|-------------------|---------------|--------|
| Running On-Demand **X** instances (vCPUs) | **0** | ≥ the largest worker's vCPU count (e.g. 64 for an `x2gd`-class memory box) |
| Running On-Demand **Standard** (A, C, D, H, I, M, R, T, Z) instances (vCPUs) | **64** | raise to the target warm-pool ceiling (e.g. 256+) |
| Running On-Demand **All Standard Spot** requests | verify before relying on spot | ≥ per-wave concurrency ceiling |

Action items (do **not** run these blindly — they are the documented request path, executed
by a human with the AWS console/CLI authenticated to the account):

```bash
# Inspect current limits (read-only)
aws service-quotas get-service-quota \
  --service-code ec2 --quota-code L-1216C47A   # Running On-Demand Standard instances
aws service-quotas get-service-quota \
  --service-code ec2 --quota-code L-7295265B   # Running On-Demand X instances

# File an increase request (human-initiated; approval is async, hours-to-days)
aws service-quotas request-service-quota-increase \
  --service-code ec2 --quota-code L-1216C47A --desired-value 256
```

Because memory-heavy boxes (X family / `x2gd`) start at a **hard 0** limit, the interim pool
must be sized within the Standard bucket (64 vCPU) until the increase lands. Plan waves
accordingly: e.g. up to ~16 concurrent 4-vCPU Graviton workers, or ~8 concurrent 8-vCPU, fits
the 64-vCPU Standard ceiling.

---

## 3. Job-submission API contract

The contract **mirrors today's `proofs/batch2/runner2.sh` per-file recheck contract** so the
existing Doctor workflow and ledger flip (`verify-results.tsv`) plug in unchanged. `runner2.sh`
is, in essence:

```bash
# bulk parallel warm pass (ignore failures — populates the shared cache)
timeout 2400 lake build $(sed 's/^/Proofs./' "$LIST") >/dev/null 2>&1 || true
# per-target recheck (cached => instant); emit PASS/FAIL + first-5 error lines
while read t; do
  log=$(timeout 300 lake build "Proofs.$t" 2>&1)
  if [ $? -eq 0 ]; then echo "PASS $t"; else echo "FAIL $t"; echo "$log" | grep error | head -5; fi
done < "$LIST"
```

The remote pool exposes the **same shape** as a job:

### Request

```jsonc
{
  "job_id": "uuid",                       // client-generated, idempotency key
  "toolchain": "leanprover/lean4:v4.31.0",// pins the worker image tag
  "image": "lean4-arm64:v4.31.0",         // reuse the epic-37508 Dockerfile image
  "git_ref": "a1b2c3d",                   // commit that carries the .lean files under test
  "targets": ["Erdos1026OQ05Mirsky",      // bare module names (no "Proofs." prefix),
              "WeakGoldbachBounds"],        //   matching runner2.sh's <LIST> format
  "per_target_timeout_s": 300,
  "bulk_timeout_s": 2400,
  "memory_limit_mb": 32768                // per-container --memory, mirrors docker-build.sh
}
```

### Response (mirrors `<resultfile>` + `<diagfile>`)

```jsonc
{
  "job_id": "uuid",
  "worker": "i-0abc… (spot, us-west-2a)",
  "results": [
    { "target": "Erdos1026OQ05Mirsky", "exit": 0,   "status": "PASS", "errors": [] },
    { "target": "WeakGoldbachBounds",  "exit": 1,   "status": "FAIL",
      "errors": [ "…first 5 lines matching /error/…" ] }
    // exit 137 => OOM (retryable on a larger box); exit 124 => timeout
  ]
}
```

Two derived artifacts are emitted so the migration ledger consumes remote results with zero
format changes:

- `verify-results.tsv` rows: `<target>\t<PASS|FAIL>` — identical to `runner2.sh`'s `<OUT>`.
- `<diag>` blocks: `===== <target>` followed by the first-5 `error` lines — identical to
  `runner2.sh`'s `<DIAG>`.

**Contract invariant:** `{files, toolchain, git ref} → {EXIT, first-N error lines}`. Any
worker (local Docker today, remote Graviton tomorrow) that honours this invariant is a drop-in
backend for the Doctor / ledger-flip pipeline.

---

## 4. Worker image plan

Reuse the epic-37508 image, **no new Dockerfile**:

- Base: `proofs/Dockerfile` (native ARM64 Ubuntu + `elan` + pinned Lean toolchain), built and
  tagged `lean4-arm64:v4.31.0`. arm64 → **AWS Graviton** (`c7g`/`m7g`/`r7g`, or `x2gd` once the
  X-family quota is lifted) for best price/performance.
- **Pre-bake the Mathlib source checkout + warm `.lake/build` cache into the AMI/image layer**
  so cold-starts are cheap — the same two shared volumes localhost uses today
  (`lean-mathlib-packages`, `lean-mathlib-cache`) become baked read-only layers plus an
  ephemeral per-job overlay.
- On a mathlib rev bump, `lake` detects the manifest mismatch and re-resolves into the writable
  overlay (self-healing), exactly as the shared cache volume does on localhost.

The worker entrypoint is `runner2.sh` unchanged, run inside the container against a bind-mounted
`/workspace` synced to `git_ref`.

---

## 5. Cache strategy

| Layer | Backing | Mode | Rationale |
|-------|---------|------|-----------|
| Mathlib **source** (`.lake/packages`, ~6.8 GB) | baked AMI layer / EFS | read-only | Identical across all jobs (all pin same rev). |
| Mathlib **olean** warm cache (`.lake/build`, ~21 GB) | baked AMI layer + S3 restore | read-only base | Avoids re-elaborating Mathlib per job. |
| Per-job `.lake/build` writes | ephemeral overlay (`tmpfs`/instance store) | read-write | **Per-job ephemeral so no cross-job write races** — the same isolation localhost gets from per-slot cache volumes. |

Restore path for a cold worker: pull the shared olean tarball from S3 once at boot (or mount an
EFS access point read-only), then layer an ephemeral overlay for the job's own writes. S3 is
cheaper and simpler for scale-to-zero; EFS is lower-latency for a warm pool. Start with **S3 +
local restore**; revisit EFS if boot-restore dominates job latency.

---

## 6. Autoscaling approach

Queue-depth-driven, scale-to-zero:

```
 Doctor / migration lane
        │  submit {targets, git_ref, toolchain}
        ▼
   ┌─────────┐   depth   ┌───────────────────────────┐
   │  SQS    │──────────▶│ ASG target-tracking        │
   │  queue  │           │  (ApproximateNumberOf       │
   └─────────┘           │   MessagesVisible / worker) │
        │                └───────────────────────────┘
        │ long-poll                    │ scale 0..N
        ▼                              ▼
   ┌──────────────── Graviton spot workers ────────────────┐
   │  lean4-arm64:v4.31.0 · runner2.sh · S3 olean restore   │
   └───────────────────────────────────────────────────────┘
        │  results → S3 / DynamoDB → verify-results.tsv
        ▼
   Ledger flip (unchanged)
```

- **Trigger:** SQS queue depth. ASG target-tracking on
  `ApproximateNumberOfMessagesVisible / workers` (target ≈ 1–2 messages per worker), **or**
  Karpenter on EKS if we want per-pod bin-packing and faster scale-up. Start with SQS + ASG
  (fewer moving parts, no EKS control-plane cost); graduate to Karpenter only if pod-level
  packing is needed.
- **Scale to zero when idle**; **warm-pool a few workers** during active migration waves
  (ASG warm pool / min-size bump for the duration of a wave, then back to 0).
- **Idempotency:** `job_id` is the dedupe key; a job re-delivered after a spot interruption is
  a no-op if already recorded. Jobs are retryable because verification is deterministic.

---

## 7. Cost controls

- **Spot instances** for build workers — jobs are retryable/idempotent, so interruptions just
  re-queue. Expect ~60–90% savings vs On-Demand on Graviton.
- **Scale-to-zero** floor: min ASG size 0 outside active waves; nothing runs (and nothing is
  billed for compute) when the queue is empty.
- **Per-wave concurrency ceiling** (ASG max-size) sized to the current vCPU quota (§2) — hard
  cap on blast radius and spend.
- **Budget cap:** AWS Budgets alarm + a Lambda that sets ASG max-size to 0 when the monthly cap
  is breached.
- **S3 lifecycle:** expire job result/diag objects after N days; the ledger keeps the durable copy.

---

## 8. Relationship to existing infra & interim path

- **Interim single-box precursor:** `/repo:remote aws` (`.claude/commands/repo/remote.md`)
  already stands up (or reuses) a single tagged EC2 box with the repo synced and an
  idle-shutdown guard. That is the manual, one-box precursor to this pool — use it today for
  overflow capacity while the pool is unbuilt, and reuse its safety posture (per-repo resource
  tag, idle-shutdown, SSH-from-your-IP-only) in the pool's worker template.
- Complements (doesn't replace) the local Docker recipe (`proofs/scripts/docker-build.sh`,
  `proofs/batch2/STATUS.md`).
- Orthogonal to **Aristotle** (proof *search*).
- Removes the localhost RAM/disk ceilings that currently bound the migration's parallel-lane /
  one-proof-per-agent fan-out.

---

## 9. Increments delivered so far

**First increment (PR #39070):**
- This design doc.
- `scripts/remote-build/submit-job.sh` — a **dry-run-only** stub that builds a spec-conformant
  job request (§3) from a target list + git ref and prints it. It makes **no** AWS calls unless
  `REMOTE_BUILD_LIVE=1` is set **and** a real endpoint is configured — and even then it only
  `curl`s a submit URL you provide; it never provisions infrastructure. Default invocation is a
  pure request-shape preview, safe to run anywhere.

**Second increment:**
- `infra/remote-build-pool/` — an **unapplied** Terraform skeleton for the queue +
  result-store half of §10 item 1 (SQS job queue + DLQ, S3 result bucket, worker IAM
  role/instance profile). No `terraform init`/`plan`/`apply` has been run against it;
  every resource is marked for human review. See `infra/remote-build-pool/README.md`
  for the safety constraints on this directory.
- `research/remote-build-pool-cost-estimate.md` — illustrative (unverified) cost shape
  for the queue/bucket (near-zero) vs. the not-yet-declared compute fleet (the real cost
  driver), to help a human scope whether pursuing the remaining §10 items is worthwhile.

## 10. Follow-up work (kept in #38684 / new issues)

1. ~~Provision SQS queue + result store (S3/DynamoDB) via IaC (Terraform/CDK)~~ —
   **skeleton drafted** in `infra/remote-build-pool/` (SQS queue + DLQ, S3 result
   bucket, worker IAM role). **Unapplied.** Still blocked on the §2 quota increase
   before it's useful to actually run, and needs human review + a real backend config
   before any `terraform apply`. See `infra/remote-build-pool/README.md`.
2. Build & publish `lean4-arm64:v4.31.0` AMI with baked Mathlib source + warm olean cache.
3. ASG launch template + target-tracking policy (or Karpenter provisioner). Would consume
   `worker_instance_profile_name` from the item-1 skeleton.
4. Worker-side result uploader that writes `verify-results.tsv` rows + diag blocks to the
   `result_bucket_name` output from the item-1 skeleton.
5. Wire `submit-job.sh` to the live endpoint behind `REMOTE_BUILD_LIVE=1`, once a real
   `job_queue_url` exists to submit against.
6. Budget-cap Lambda + AWS Budgets alarm (§7) — bundle with item 3, not before, so the
   cap is never deployed without the fleet it caps. See
   `research/remote-build-pool-cost-estimate.md` §4.

See `research/remote-build-pool-cost-estimate.md` for an illustrative (unverified) cost
shape to help scope how much of the remaining work is worth pursuing.
