# Remote Build Pool — Cost Estimate (Illustrative)

Part of #38684. Companion to `research/remote-build-pool-design.md` (architecture) and
`infra/remote-build-pool/` (unapplied Terraform skeleton for the queue + result store
only).

**Status: order-of-magnitude only, not verified against current AWS pricing.** Every
dollar figure below is a rough illustration to help a human decide whether this is worth
pursuing past the design stage — none of it has been checked against the AWS Pricing
Calculator or Cost Explorer at the time of writing. Before committing any budget, a
human should re-price the exact instance types/regions with
[the AWS Pricing Calculator](https://calculator.aws) — spot prices in particular
fluctuate continuously and vary by availability zone.

---

## 1. What actually costs money

From the design doc's cost-controls section (§7):

| Component | Cost driver | Idle cost |
|-----------|-------------|-----------|
| SQS queue + DLQ (`infra/remote-build-pool/sqs.tf`) | Per-request pricing, no idle charge | ~$0 |
| S3 result bucket (`infra/remote-build-pool/s3.tf`) | Storage (small JSON objects, `result_retention_days`-bounded) + requests | Negligible (cents/month at this repo's scale) |
| **Worker compute (not yet declared — §10 items 2-3)** | EC2/spot instance-hours while workers are running | **$0 if scaled to zero** |
| S3/EFS Mathlib olean cache restore | One-time-per-cold-boot data transfer + storage | Small, amortized across jobs in a wave |

**The compute fleet dominates cost by a wide margin whenever it's running; everything
else here is close to free.** This is why §7 of the design doc leads with scale-to-zero
and spot as the two primary cost controls — the queue and bucket in this skeleton are
not the risk.

---

## 2. Illustrative worker sizing

Per `research/remote-build-pool-design.md` §3, a job's `memory_limit_mb` defaults to
32768 (32 GiB) — mirroring this repo's own `docker-build.sh` default memory cap
(`CLAUDE.md`: "Custom limits (defaults: 32GB memory, 60min timeout)"). A worker sized to
run **one job at a time** needs roughly that much RAM headroom; a worker aiming for
**N concurrent jobs** (§10's warm-pool concept) needs roughly `N × 32 GiB` plus overhead
for the OS, Docker, and the read-only Mathlib olean base layer.

| Sizing goal | Illustrative Graviton (arm64) instance class | vCPU | RAM |
|---|---|---|---|
| 1 job/instance, memory-comfortable | `r7g.xlarge`-class | 4 | 32 GiB |
| 1 job/instance, generous headroom | `r7g.2xlarge`-class | 8 | 64 GiB |
| ~2 jobs/instance (tight; watch for the same OOM pattern §1 of the design doc describes for localhost) | `r7g.4xlarge`-class | 16 | 128 GiB |

The §2 quota wall (documented in the design doc) caps the **Standard** vCPU bucket at 64
in the account this was scoped against, i.e. at most **~16 concurrent `r7g.xlarge`-class
workers** (4 vCPU each) until a quota increase lands — well short of "dozens of
single-proof jobs at once" from the design doc's problem statement. Sizing beyond that
either needs the quota increase or accepting lower per-worker concurrency within the
existing 64-vCPU ceiling.

---

## 3. Illustrative per-wave cost shape (NOT verified pricing)

The numbers below are **placeholders for the shape of the calculation only** — do not
budget against them without re-pricing. As of recent AWS Graviton (r7g family)
on-demand list pricing, order-of-magnitude figures in `us-west-2` have been in the
**tens of cents per hour** for `xlarge`-class instances, with **spot typically running
~60-70% below on-demand** for Graviton (per the design doc §7's "Expect ~60-90% savings
vs On-Demand on Graviton" — that upper end is optimistic; treat 60-70% as the
conservative planning assumption).

```
wave_cost ≈ workers × hours_per_wave × spot_price_per_hour

Illustrative (NOT verified — re-price before using):
  16 workers × 2 hours × ~$0.10-0.20/hr (spot, r7g.xlarge-class) ≈ $3-6 per wave
  16 workers × 8 hours × ~$0.10-0.20/hr                          ≈ $13-26 per wave
```

Compare against: a single always-on r7g.xlarge running 24/7 at the same illustrative
rate would be on the order of a few dollars a day even before any spot discount — the
whole point of scale-to-zero (§7) is that a wave-shaped workload like this repo's
migration burn-down should cost closer to the "per wave" numbers above than to any
"always-on" number, because the ASG floor is 0 outside active waves.

**Other line items to re-price, not included above:**
- S3 data transfer for the olean cache restore on cold workers (§5) — depends on cache
  size (~21 GB per the design doc) and how often workers cold-boot vs. stay warm within
  a wave.
- SQS request pricing — negligible at this job volume (well under the free tier for any
  plausible number of verification jobs this repo would submit).
- Data transfer out, if results are pulled cross-region — avoidable by keeping the
  result bucket in the same region as the workers.

---

## 4. Budget-cap mechanism (already specified, not yet built)

Design doc §7 specifies the mechanism, not yet implemented in this skeleton: an AWS
Budgets alarm + a Lambda that forces ASG max-size to 0 when a monthly cap is breached.
That Lambda + Budgets alarm is real infrastructure (billing-related IAM permissions) and
is intentionally **not** included in `infra/remote-build-pool/` yet — it should land
alongside the ASG itself (§10 item 3), reviewed together as one unit, so the cap is
never accidentally deployed without the thing it's meant to cap.

---

## 5. Bottom line for a human deciding whether to proceed

- The **queue + result store** in `infra/remote-build-pool/` (this PR) cost effectively
  nothing to run, even continuously — a human could apply just that piece today with
  negligible risk if they wanted to unblock worker-side development.
- The **compute fleet** (not yet declared) is where real spend happens, but only while
  workers are running — the wave-shaped estimate above (single-digit-to-low-double-digit
  dollars per wave, order of magnitude) suggests the marginal cost of a migration
  burn-down wave is small relative to the parking-lot status of this issue, *if* the
  illustrative pricing holds up under a real AWS Pricing Calculator check.
- The gating factor remains the **§2 EC2 vCPU quota increase**, which is a human
  request-and-wait step (hours-to-days for approval), not a coding task — nothing in
  this repo can accelerate that.
