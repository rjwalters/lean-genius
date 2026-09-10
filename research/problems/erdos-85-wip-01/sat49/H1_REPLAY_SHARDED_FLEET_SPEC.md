# H1 sharded Lean replay fleet specification

Goal47 / board37, owner codex-sol-2, reviewer Fable. Prepared 2026-09-10 at **zero incremental spend**. No instance, upload, policy change, quota request, or lifecycle mutation was made. This is a specification and cost model, **not a launch-ready package or a completed multi-job rehearsal**. The funded run remains gated on Robb's seed-round go.

## Recommendation and boundary

Plan **32 independent r7g.2xlarge on-demand boxes**, each 8 vCPUs / 64 GiB, one Lean worker at a time, 300 GB gp3 scratch/root, in us-east-1. Keep the proven ARM image and exact tool-identity checks; refreeze source/overlay/bootstrap for every implementation change. Target about **9 days and $3,138 replay infrastructure** for 13,350 new certificates under the byte-weighted model below. This is not a hard runtime bound: twice the original pilot-per-job time raises infrastructure to $4,265; the byte-weighted forecast is already about1.47 times that original baseline. Storage, retrieval, the aggregate/cold build, and producer/H3/H5/H7 work are additional.

The live Standard On-Demand quota is **128 vCPUs** (L-1216C47A). N=32 needs 256 plus other running usage; N=16 consumes the full current quota before other usage. N=8 is the quota fallback, subject to actual free quota at launch. Quota approval and instance availability are prelaunch prerequisites, not assumed capacity. Spot has a separate Standard Spot quota, **L-34B43A08 = 300 vCPUs** at this read-only check; running producer capacity competes within that pool. Check both actual usage and desired headroom. No quota increase has been requested.

Prefer on-demand for the first full run: it preserves a bounded set of single-writer owners and reduces interrupted large proofs. Spot is an explicit cheaper sensitivity, not equivalent scheduling certainty. A replacement must wait for authoritative termination of its previous shard owner. Heartbeat timeout alone cannot authorize a second writer. This is host-local exclusion plus static ownership, not distributed leasing.

The successful production pilot compiled one 346 MB gzip certificate in 983.6 seconds. The three conflict-v6 checks classify LRATs with a different checker; their 65–633 second times are **not Lean leaf timings**. The reported 50.8 GiB conflict peak demonstrates a need to test large payloads, not a proven upper bound for all Lean leaves. Largest rescued inputs reach 19–26.5 GB raw. Include the largest available live input in rehearsal; if nested Lean peak exceeds48 GiB, route that size class to a separately frozen r7g.4xlarge (128 GiB) heavy shard and revise compute, quota, and local-rehearsal capacity. No128 GiB run has been performed. The64 GiB fleet model must not be used for an unmeasured heavy lane. A largest-leaf rehearsal can force a larger instance class and a new cost/freeze revision. No unmeasured 64 GiB guarantee is made.

## What is already present, and what sharding changes

Source audit: integration ac46eca9e4, whose h1fleet sources are unchanged from 7cbbe110b2. Pricing/lifecycle/API responses and source hashes are saved under `/Users/rwalters/lean-genius-h1-sharded-replay-spec-20260910/`, indexed by `evidence-index.json`.

| Existing component | Verified contract | Required fleet addition |
|---|---|---|
| `run_replay_queue.py` | exact queue hash/count, sorted unique tags/slots, max parallelism, host flock | immutable shard plan; one assigned instance per shard; all dispatches use P=1 |
| `build_replay_queue.py`, `build_replay_manifest.py` | canonical capacity ordinals, terminal/certificate hash joins, partial queue support | deterministic partition evidence and fresh per-shard queue-build receipts |
| `replay_worker.py` | receipt/ready/ledger, native ownership audit, preserved input tags | supervised scratch cleanup after independent acceptance; largest-leaf resource gate |
| `replay_common.py` | immutable single PutObject with full readback | conditional multipart publication for artifacts exceeding the single-request limit; streaming local backend for realistic large tests |
| `validate_replay_receipt.py` | validates a receipt against its original manifest and live objects | invoke for every shard receipt, retain its exact original bytes |
| `materialize_replay_leaf_tree.py` | partial materialization available; still one manifest per invocation | invoke per shard into separate staging roots, then verify and merge with per-row provenance |
| `run_replay_to_aggregate.py` | exact 13,351 leaves and profile counts; materialization v1 binds one manifest | reviewed multi-manifest materialization v2 input; preserve every existing capacity/source/raw-artifact check |

These additions are work to finish before funding, not options to omit. A successful pilot does not establish that concatenating ledgers makes the current aggregate driver accept shards.

## Freeze and ownership contract

1. Freeze one capacity inventory/index/reindex receipt and one joined certificate/terminal snapshot. The canonical target remains **13,351 slots with profile counts [1485,3617,4717,2693,839]**. Preserve global `(profile, local_index, tag)`; never renumber a shard locally. A listed S3 key alone is not an eligible queue row: it needs the existing builder's validated hash/table/terminal bindings. Missing, conflicting, quarantined, and already-accepted rows have explicit separate status.
2. Include the validated pilot receipt as a one-row **legacy input shard** with its original manifest/prefix. Exclude that exact accepted slot from new work only after fresh validation. The current-ready count 12,019 = 12,020 reported objects minus one accepted certificate is a planning quantity, not a validated queue. Full closure needs 13,350 new rows plus the legacy row. Recovered/newly solved certificates enter a new immutable wave; no running queue is edited.
3. Partition eligible rows deterministically by descending estimated weight, then tag, assigning each to the least-loaded shard (tie: shard id). Weight files use one explicitly declared unit/source: `compressed_gzip_bytes` from the complete object-size snapshot, `raw_bytes` for decompressed compact LRAT when available for every included job, or `estimated_milliseconds` after converting all rows to a common timing basis. Do not mix compressed and decompressed bytes or apply the1.47 mean factor again to individual byte weights. Weight uses measured Lean time when available, otherwise a declared byte estimate; it is scheduling data, never proof evidence. Sort each emitted queue by tag as the dispatcher requires. Save the weight source and resulting per-shard loads. Reject duplicate tags, slots, original certificate keys, or missing/extra parent rows. Exact union equality is mandatory; count equality alone is insufficient.
4. Keep the full canonical inventory/index on every shard. Filter the terminal and certificate index rows to the assigned set, use the existing queue builder's partial mode, and create a genuine queue-build receipt. Extend the freezer to distinguish filtered certificate-index hashes from the common capacity-index hash: current `validate_queue_build_receipt` equates them, so these proposed inputs do not yet pass unchanged. Preserve v1 behavior and validate every filtered row against the full capacity index. Then freeze each shard through the reviewed extension with incomplete-capacity mode; never edit a previously frozen manifest's queue/hash fields. A frozen fleet plan binds parent snapshot, partition algorithm/version, all shard queue+manifest hashes, legacy inputs, all prefixes, and runtime/source/overlay identities.
5. Use run ids of the form `YYYYMMDD-<prelaunch-input-identity-sha12>-waveNN`; freeze input identity before adding the prefix to manifests to avoid a self-hash cycle. The final fleet plan binds every full manifest hash, so a short naming hash is not an integrity check. Refuse a nonempty run prefix unless resuming that exact plan. Output prefix per shard: `sat49/campaign-20260825/h1-replay/fleet/<run-id>/shards/<NNN>/`. Original input keys stay under `h1/<tag>.compact.lrat.gz`. Set `single_dispatcher=true`, `max_parallelism=1`, `--parallelism 1`, and the pinned absolute host lock (e.g. `/opt/replay/state/lean-replay.lock`) on every host. The equal path is safe on distinct hosts; no shared network lock is claimed. Duplicate dispatchers on one host must fail even with different state directories.
6. Editor's launch journal binds run/shard/queue/manifest/bootstrap to exactly one live instance. Replacement preserves shard identity and prefix, resumes accepted or ready rows using the existing worker checks, and starts only after old ownership is terminal. A resumed dispatcher may reread earlier accepted rows; budget and measure that overhead. Failed dispatch records remain failures even if other rows finish. Worker return code alone does not replace independent receipt validation.

## Aggregation and lifecycle tags

Merge **references and evidence, never rewritten receipts**. For every planned slot, the fleet verifier selects exactly one `(original manifest hash, queue hash, receipt key/hash, ready key/hash, ledger key/hash)` tuple. Revalidate original receipts using the existing validator, verify the exact queue-job binding, common capacity/coverage/table/CNF/axiom policy, and reject duplicate or absent slots. Cross-wave reuse requires the same slot and input identities; changed runtime/source provenance remains explicit. No synthetic common manifest may be substituted into old receipts.

Each worker alone adds `replay=consumed` to its assigned input, preserving other tags. The merger checks those tags and per-shard ledgers; it does not blindly retag the global union. A source object's consumed tag without accepted evidence is insufficient. Legacy pilot evidence remains in its original namespace.

Run the existing materializer in partial mode per manifest into distinct fresh staging trees. A new merger emits the globally sorted leaf index and **materialization-v2 evidence containing per-row origin manifest/queue hashes and the fleet-plan hash**. It must retain all old raw source/olean/LRAT hash checks, module/theorem names, profile counts, exact slot coverage, path safety, and source reproducibility. The aggregate driver needs an explicitly reviewed v2 branch; v1 remains supported unchanged. Acceptance ends at a verified source/olean tree and transcript, followed by the existing aggregate/adapter, cold-build and final Lean socket audits. Shard completion alone does not prove the finite drop.

Read-only bucket lifecycle inspection found transition of tagged H1 originals to **GLACIER_IR at object age7 days**. This is not deletion and not seven days after tagging; many old objects become eligible immediately upon tagging. The validator downloads the certificate, and materialization validates then downloads it again. Preserve originals and include retrieval costs. The cost memo should offer editor/operator suspension of that transition for the run window (and a recorded restoration plan), or same-day validation/materialization before transition, as explicit alternatives to retrieval charges. This specification performs no policy change and cannot promise same-day completion for large jobs. Rule1 also transitions eligible bucket objects into Intelligent-Tiering at day0; account for its monitoring and any configured archive tiers. Do not silently change the lifecycle, source keys, receipts, or tag timing. S3 transitions and tag preservation are production-only checks in the rehearsal matrix.

## Disk and large-object gate

The current worker leaves raw LRAT, gzip, raw olean and compressed artifacts in `state/work/<tag>`. Accumulating hundreds of such jobs exhausts a 300 GB volume. Add a coordinator cleanup journal: only after accepted receipt + independent live validation, persist the validation/dispatch evidence, then remove that completed job's bulky local scratch. Preserve small logs/job descriptors. Failed/unvalidated work is retained within a bounded failure budget; stop scheduling before disk exhaustion. No shared freight or another job's files are deletion targets. Recovery after cleanup must succeed from remote accepted evidence without recompilation.

Budget each active job from raw LRAT bytes, raw olean estimate, compressed input/output, temporary readbacks, and static freight. 300 GB is a starting provision, not an inferred bound; require measured free-space headroom before dispatch and stop on unknown oversized jobs. Bound the local backend's memory with streaming copies/hashes, since its current `read_bytes()` path can skew a large test.

The replay store currently sends every `olean.zst` via a single PutObject. It therefore needs the same large-object treatment as the producer. Specify staged parts, final **CompleteMultipartUpload with If-None-Match `*`**, whole-file SHA-256 metadata and full readback, immutable winner verification, and abort/restart rules. A multipart ETag is not the file SHA-256. A HeadObject precheck followed by an unconditional upload does not preserve the contract. Coordinate this shared implementation with Fable; pin it into a new freight revision. [AWS's API contract](https://docs.aws.amazon.com/AmazonS3/latest/API/API_CompleteMultipartUpload.html) documents conditional completion and conflict handling. No live multipart test is claimed here.

## Required local multi-job rehearsal (pending)

Owner sol2, reviewer Fable. Use the real pinned Lean generator/compiler/auditor, four **distinct valid capacity jobs**, two queues with at least two jobs each, isolated local object storage, original hashes, and fresh shard prefixes. Select small, typical, and largest available raw/expected-output sizes; the semantic conflict checker is not a substitute. Run each host context at P=1 and production memory. On the 96 GiB workstation run host contexts sequentially if two large workers would exceed memory; disclose that this does not measure simultaneous EC2 performance.

Required observations:

- Exact parent/shard union, fresh builder/freezer receipts, sorted queues; reject duplicate tag/slot/input and wrong shard/manifest/hash.
- Actual job1→job2 transition on each shard; two accepted receipts per queue, no `sorryAx`, the reviewed explicit native obligation policy.
- Attempt a second dispatcher while the first holds the lock: reject it before any worker; test a different state directory too.
- Stop after one accepted job, clean only its validated scratch, and resume the same shard: accepted receipt validated without recompile, remaining job executes, unique ledger rows retained.
- Interrupted incomplete/ready transaction resumes correctly; altered artifact/receipt or wrong origin manifest makes the merger fail; no lifecycle tag on failed proof.
- Merge both shards plus a legacy fixture; verify exact expected slots and materialized raw artifacts. Demonstrate missing/duplicate coverage rejection. A miniature merge does not claim the production driver's 13,351-leaf gate passed.
- Streaming local backend and multipart transport fault tests include a >5 GiB file, failure/retry and immutable collision; no S3 call is hidden behind a local PASS.
- Record per-job compile and end-to-end wall time, **nested Lean** RSS (not Docker-client RSS), disk high-water mark, transfer counts/bytes, cleanup evidence and all command hashes. Restore temporary Docker settings afterward.

Production-only: fresh EC2 identities, exact kernel-dependent CLI identity, live IAM/conditional multipart/readback, AZ availability/quota, lifecycle transition charges, and interruption replacement. Static checks and the old one-job pilot do not count as this gate. Until its reviewed evidence exists, launch readiness is **NO**.

## Cost and wall-time model

Use [estimate_h1_replay_fleet.py](estimate_h1_replay_fleet.py); its exact output is [h1_replay_fleet_costs_20260910.json](h1_replay_fleet_costs_20260910.json). Live AWS Pricing API in us-east-1 returned: r7g.2xlarge Linux shared $0.4284/hour (effective2026-09-01), gp3 $0.08/GB-month, S3 first50TB storage $0.023/GB-month, Glacier IR retrieval $0.03/GB. Public IPv4 is [$0.005/hour](https://aws.amazon.com/vpc/pricing/). EBS arithmetic uses a30-day/720-hour month and baseline IOPS/throughput. No NAT Gateway or paid endpoint is included; use existing routing/direct same-region S3 access. Reprice at funding.

Let J be new jobs, H=J×984/3600 box-hours, N boxes. Ideal wall=H/N. Planning box-hours=1.25H+0.5N, allowing a **hypothetical**25% noncompile/retry overhead and30min bootstrap per box. Planned infrastructure multiplies this by (0.4284+300×0.08/720+0.005). Allocated vCPU-hours=8×box-hours; this is not measured useful CPU time. True load imbalance, large-payload failures and I/O may exceed25%. LPT balance and the rehearsal must replace this provisional assumption before a fixed quote.

| New jobs | N | vCPUs | Ideal days | Planned days | On-demand infrastructure | Spot sensitivity |
|---:|---:|---:|---:|---:|---:|---:|
|12,019 current-ready estimate|8|64|17.11|21.41|$1,919|$867|
|12,019|16|128|8.56|10.71|$1,920|$868|
|12,019|32|256|4.28|5.37|$1,924|$870|
|13,350 full closure|8|64|19.01|23.78|$2,131|$963|
|13,350|16|128|9.50|11.90|$2,133|$964|
|13,350|32|256|4.75|5.96|$2,136|$966|

**Primary planning adjustment after review1556:** Fable's newer read-only census reported12,050 objects, mean509MB, median332MB, p90 1.11GB, p99 3.11GB and max5.22GB; the pilot's346,105,417 bytes are near the median. Preserve the table above as the original count-only sensitivity, not the primary quote. Assuming compile time is proportional to compressed bytes, multiply H by509,000,000/346,105,417≈1.47 before overhead. This linearity is a stated hypothesis, not measured Lean throughput. Freeze-time input counts and size weights must be refreshed;12,019 is the historical ready-subtotal scenario, not today's validated queue.

| New jobs | N | Byte-weighted planned days | On-demand infrastructure | Spot sensitivity |
|---:|---:|---:|---:|---:|
|12,019 historical subtotal|8|31.48|$2,821|$1,275|
|12,019|16|15.75|$2,822|$1,276|
|12,019|32|7.88|$2,826|$1,277|
|13,350 full closure|8|34.96|$3,133|$1,416|
|13,350|16|17.49|$3,135|$1,417|
|13,350|32|8.76|$3,138|$1,419|

Byte-weighted full-closure compile work is5,366.4 box-hours. Actual run wall time is governed by the largest shard load, not total/N when imperfectly balanced. The full closure count baseline is3,649 compile box-hours (29,192 allocated vCPU-hours); planning adds overhead. Spot sensitivity uses the **observed us-east-1b $0.1535/hour at2026-09-10 04:00Z**, plus another10% work loss atop the25%; neither price nor loss rate is guaranteed. Other sampled AZ prices were0.1602–0.1722. Do not promote N32 to launchable on quota evidence from a different market.

Additional budget lines, not hidden in the table:

- Input compressed storage is reported6.06TB for12,020 objects, not a complete future byte inventory. Do not repay existing storage in the incremental replay estimate. If compressed oleans total6–7TB, one month of new frequent-access storage is roughly$138–161 at0.023/GB-month, plus requests/monitoring. This output-volume assumption must be measured.
- Glacier IR full-read cost is $30 per decimalTB: one6.06TB pass ≈$182; three post-transition passes ≈$545. Independent validation and materialization alone can require several reads; resumed/repeated checks add more. Reserve by measured byte counts, not GET request count alone. S3 transfers to same-region AWS services have no bandwidth charge, but retrieval and requests remain billable ([S3 pricing](https://aws.amazon.com/s3/pricing/)). Avoid downloading the full corpus to the Mac as a funded default.
- Aggregate materialization retains **raw LRAT plus raw olean**. With6.7TB eventual gzip and a hypothetical expansion ratio3–6 and raw olean similar to LRAT, final raw storage is roughly40–80TB, before staging overhead. This is a sensitivity, not a measured total. At50,000GB gp3,72hours costs$400 in storage alone; a single125MB/s pass over50TB takes about111hours. Final cold-build hardware, repeated hashing, I/O throughput, retention and wall time need a separate measured quote. A300GB replay box cannot hold the aggregate tree.
- Multipart requests, Glacier transition/minimum-duration charges, additional storage classes, taxes, aggregate compute, and H3/H5/H7/producer work are not included. Model them in the editor's total cost memo. Current on-demand table is a replay-line estimate, **not the total budget to prove f(49)<f(48)**.

## Next concrete work and handoff

Sol2 implements the deterministic partition/merge contracts, bounded scratch cleanup and the real multi-job rehearsal; Fable reviews and coordinates shared multipart code. Inventory owner supplies the reconciled eligible set and actual size distribution; editor owns quota/funding/launch decisions. The fleet specification received review1556 PASS-with-notes. The initial plan-only partitioner is now implemented in `h1fleet/plan_replay_shards.py`: its6 tests verify exact conservation, scheduling, rejection cases, capacity binding and fresh output. Review1558 passed the planner and revised cost assumptions. Its provenance now also records capacity versus canonical counts and hashes the unassigned capacity rows as UNRESOLVED; `accepted_set_sha256=null` deliberately leaves accepted-complement validation for the freezer/merger. This does not satisfy the actual four-job Lean gate or produce launch manifests. No new mathematics mechanism is opened. The same-day objective is readiness to **start** the funded run once these gates and capacity are satisfied, not a claim that thousands of serial-per-host Lean checks finish that day.
