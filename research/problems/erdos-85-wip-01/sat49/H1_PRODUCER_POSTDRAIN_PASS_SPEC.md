# H1 producer fleet — state at 2026-09-10 05:00Z and the post-drain multipart pass (v4)

Goal #47 lane (3), owner Fable. Zero incremental spend until the funded run; this
document is the spec and the numbers. Every count below was recomputed read-only
from the bucket on 2026-09-10 04:55–05:10Z (`aws --profile 2am-admin`); sources
are the objects named in each line. Nothing was launched, mutated or deleted.

## 1. State of the v3 producer fleet (h1-fleet-v3, queue of 1,698 rows)

| item | value | source |
|---|---|---|
| certificates under `h1/` | **12,020 objects, 6.06 TB** (mean 0.50 GB gz) | `aws s3 ls --summarize …/h1/` |
| capacity rows in the H1 inventory | 13,351 | `orderFortyNineStratumExcluded_one_of_capacityInventory_checked` (outline A.5.3) |
| rows still without a certificate | **1,331** | 13,351 − 12,020 |
| v3 queue size | 1,698 rows (both boxes' manifests: `jobs=1698`, `par=36`, `cap=14400`) | `h1-fleet-v2/nodes/<id>/manifest` |
| v3 claims | 667 | `h1-fleet-v3/claims/` |
| v3 ledger lines | 596 = 574 `UNSAT … upload=uploaded` + 22 `UNKNOWN rc=0` (all at the 14,400 s cap) | `h1-fleet-v3/ledger/` |
| v3 failure lines | 53 = **20 UPLOAD-FAIL** (trim VERIFIED, compact ok) + **33 TRIM-FAIL** (drat-trim did not verify; `raw_lrat_bytes=0`; `drat-trim.out` NOT uploaded, cause undetermined) | `h1-fleet-v3/failures/` |
| claimed rows with no ledger/failure line | 18 = **8 live slots on i-0ccf0dc6a398156d8** (claims 2026-09-09 18:11–21:57Z) + **10 ORPHANS from the lost box i-01f0d952483d8f066** (claims 2026-09-08 16:41–20:05Z) | claim bodies (= node id) + timestamps; `v3state/inflight_attrib.txt` |
| v3 rows never claimed | 1,031 = 1,698 − 667 | arithmetic |
| rows outside the v3 queue still uncertified | 207 = 1,331 − (1,031 + 20 + 33 + 22 + 18) — needs the inventory owner's reconciliation (v2 quarantine / host-grind leftovers / queue definition) | arithmetic; **open item for `DROP_CLOSURE_INVENTORY.md`** |

Boxes:

| box | type | state | slots | on-disk quarantine | notes |
|---|---|---|---|---|---|
| i-0ccf0dc6a398156d8 | c7g.16xlarge **spot**, us-east-1d, 1000 GB gp3 | running since 2026-09-06 16:55Z; heartbeat 2026-09-10 05:01Z, load 8, `slots_failed=28/36`, `disk_free=588G`, `oom=15` | 8 live | **13 UPLOAD-FAIL certificates** (`/scratch/h1/<slot>/orbit.compact.lrat.gz`, compact 19.0–26.5 GB each, ≈ 6 GB gz each; 15 TRIM-FAIL raw LRATs alongside) | **DO NOT TERMINATE** until the 13 are re-uploaded and verified; spot, so at reclaim risk |
| i-01f0d952483d8f066 | c7g.16xlarge spot | **GONE** — not in describe-instances; last heartbeat 2026-09-09 03:50Z, last worker.log 03:01Z, last ledger 03:52Z; no user termination in CloudTrail (editor 42228) → spot reclamation ≈ 03:50–04:00Z | 0 | **7 UPLOAD-FAIL certificates LOST** (f25a68f489294d7c, d67d8618bf933b97, 3de5f9e7f1d255e7, f363d5a068846aa3, 59b38d317ba10da8, 35958b08961b7cfc, be77d80a79a0dce6) → must be RE-SOLVED; its 18 TRIM-FAIL raws also lost; its 10 orphan claims must be released | |

UPLOAD-FAIL tags on the surviving box (13): 0a5acff54f93af2e 6b29a970f356c68b
9a5b6799a662168b 705d62c3af203bd8 1e946f8f3b6ffa06 329b85b7cdf2ab94
09a23a36fad47520 21835871e6144e95 dd2aa6a3da6eb429 4ed50fad4b613045
75b3c23623dcf9bf 74ce76acad2f4cf4 74fcc09b1b23a104 (`worker.log` CERT-PIPELINE-FAIL
lines; none of the 20 exists under `h1/` — checked per key 2026-09-10).

Root cause of UPLOAD-FAIL (unchanged from the 2026-09-08 diagnosis): the v3 worker
publishes with `aws s3api put-object --if-none-match '*'` (single PUT, 5 GiB
limit); the 20 failures are exactly the certificates whose compact gz exceeds
5 GiB (compact 18.5–26.8 GB, gz ≈ 0.29×); all 574 uploads are ≤ 18.1 GB compact.
Deterministic in certificate size, not transient. Each failure also STOPS its slot
(`exit 1` after writing `slot.N.failed`), which is why the boxes bled from 36 to
8 live slots.

Per-orbit cost observed on c7g.16xlarge (uploaded rows, n = 574): solve median
4,012 s (max 13,705), drat-trim median 6,204 s (max 19,116), compact size median
7 GB; the UPLOAD-FAIL rows are the tail: solve median 11,152 s, trim median
18,572 s. Throughput observed: 94 / 216 / 172 / 78 / 14 uploads on 09-06…09-10
(two boxes, slots decaying). Memory: `oom=15` and `oom=20` on the two heartbeats
— kissat peaks up to 82 GiB on hard profile-2 rows, and 36 slots on a 128 GiB
box oversubscribe; the 22 `UNKNOWN rc=0` rows and part of the TRIM-FAIL set may
be OOM casualties (raw DRAT 4.5–15.7 GB; drat-trim.out was never uploaded, so
the cause cannot be read back).

## 2. FIRST ACTION (zero incremental spend): rescue the 13 quarantined certificates

The box is paid for and running; the 13 gz files (≈ 80 GB) exist only on its
disk. This step needs a shell on i-0ccf0dc6a398156d8 (SSM Run Command or SSH —
operator/editor action; the Claude seat holds no key) and the box's existing
role, which already has PutObject on `h1/`.

```
# on the box, once per quarantined slot N (13 of them):
TAG=$(sed 's/^tag=\([0-9a-f]*\).*/\1/' /opt/h1/slot.N.failed)   # cert-pipeline-fail lines
GZ=/scratch/h1/N/orbit.compact.lrat.gz
sha256sum $GZ                      # must equal compact_gz_sha256 in failures/$TAG.line
aws s3api head-object --bucket 2am-erdos85-certs --key sat49/campaign-20260825/h1/$TAG.compact.lrat.gz && { echo EXISTS; exit 1; }
aws s3 cp --only-show-errors --expected-size $(stat -c%s $GZ) $GZ s3://2am-erdos85-certs/sat49/campaign-20260825/h1/$TAG.compact.lrat.gz
aws s3api head-object … | jq -r .ContentLength   # must equal local size
```

`aws s3 cp` uses multipart automatically above 8 MB (parts 8 MB by default; set
`multipart_chunksize = 256MB` in the CLI config for ≈ 25 parts per 6 GB file).
Create-only semantics: the HeadObject precheck plus a single writer is sufficient
here (nobody else writes these 13 keys); for the v4 worker use
`s3api create-multipart-upload` / `upload-part` / `complete-multipart-upload
--if-none-match '*'` so the create-only guarantee is atomic (awscli ≥ 2.15
supports `--if-none-match` on CompleteMultipartUpload; the fleet's pinned
2.36.34 does). Verification per file: local sha256 == `compact_gz_sha256` of the
failure line; S3 ContentLength == local size; recompute the multipart ETag
locally (md5 of the concatenated per-part md5s + `-<parts>`) and compare with
HeadObject's ETag; then PutObjectTagging `sha256=<gz sha>` like the replay stack
expects; finally write a corrected ledger line to
`h1-fleet-v3/ledger/$TAG.line` with `upload=uploaded-v4-multipart` and move the
failure line to `h1-fleet-v3/failures-resolved/`. Parallelism: 13 files, run
P = 4 on the box (network-bound, ~6 GB each; expect < 1 h total).

Only after all 13 show `uploaded-v4-multipart` may the termination hold be
lifted. If the seed-round gate is more than a few days away, the cost memo
should recommend doing this rescue NOW: it costs nothing beyond the already-
running box, and every day on spot risks the same reclamation that lost the
other seven.

## 3. Post-drain pass (v4 producer), launched when the gate opens

Work list (from §1): 7 lost UPLOAD-FAIL rows (re-solve), 33 TRIM-FAIL rows
(re-solve with diagnostics), 22 UNKNOWN-at-cap rows (finer Lean split or a
longer cap — decision for the inventory), 10 orphan claims (release, re-queue),
1,031 never-claimed v3 rows, and whatever the 207-row reconciliation adds.
Queue ≈ 1,100 rows plus the 22 hard ones.

Worker delta v3 → v4 (generate from the audited v3 worker, sha
c3db5ba90e4443dd… on the surviving box / 896ece1b93cada52… on the lost one,
same procedure as `generate_h1_v3_retry_worker.py`):
1. Publication = multipart with atomic create-only completion
   (`create-multipart-upload` → `upload-part` ×N → `complete-multipart-upload
   --if-none-match '*'`); on a 412 the key exists → treat as success only if
   HeadObject size and sha tag match, else quarantine.
2. UPLOAD-FAIL no longer stops the slot: move the gz to
   `/scratch/quarantine/$TAG/` with its ledger line, upload the failure line,
   and continue; a supervisor retries quarantined uploads every 10 min and
   publishes the quarantine inventory in the heartbeat.
3. TRIM-FAIL uploads `drat-trim.out` (and the kissat tail) to
   `h1-fleet-v4/diagnostics/$TAG/` so the cause is readable; then re-runs
   drat-trim once with `-w` (warning mode) before declaring failure.
4. Slot count bounded by MEMORY, not vCPU: `H1_PAR` = floor(RAM / 6 GiB) − reserve
   ≈ 18 on a 128 GiB box (kissat RSS 3–4 GB typical, 82 GiB worst case; the
   supervisor pauses new claims while free RAM < 16 GiB). This removes the OOM
   casualties (`oom=15/20`) that inflate UNKNOWN and TRIM-FAIL.
5. Spot interruption handler: poll the IMDS spot-interruption notice every 5 s;
   on notice, kill solvers, `aws s3 cp` every finished gz still on disk, upload
   heartbeat + worker.log, then release (delete) claim markers of the killed
   slots so they re-queue. Use on-demand (r7g/c7g.16xlarge) for the final pass if
   the budget allows — the loss above cost 7 certificates × ~6 box-hours each.
6. Orphan sweep before launch: any claim under `h1-fleet-v3/claims/` with no
   ledger or failure line AND whose node has no heartbeat in the last 60 min is
   deleted (the ten from i-01f0d952483d8f066 today), the same way the v2 orphans
   were swept (38508).
7. Local multi-slot dry run on the host (Docker 64 GiB VM) with two known-hard
   rows and one > 5 GiB synthetic gz is the gate, exactly as pilot-8 / conflict
   v6 gated the replay stack.

Cost (for the editor's memo; spot c7g.16xlarge ≈ $1.0–1.2/h, on-demand ≈
$2.32/h, us-east-1): per orbit ≈ 2.9 box-slot-hours median (solve + trim) with
the hard tail at 6–8 h; at 18 slots/box ≈ 6 orbits/box-hour on median rows.
≈ 1,100 rows → ≈ 190 box-hours + tail ≈ 230 box-hours: **one box ≈ 10 days,
four boxes ≈ 2.5 days, eight boxes ≈ 1.3 days; ≈ $250–300 spot or ≈ $550
on-demand for solving**, plus ≈ 0.6 TB of new certificates (S3 standard ≈
$14/month) and negligible egress (all in-region). The 22 UNKNOWN-at-cap rows
are not in this estimate; a 4× cap (16 h) on 22 rows ≈ 350 box-slot-hours ≈
$25 spot but only if the inventory owner accepts longer caps instead of finer
splits.

## 4. Replay-side numbers (for the inventory's Lean-replay sector)

Frozen replay stack: pilot-8 (goal #44) consumed 1 certificate end to end
(compile 983.6 s on r7g.2xlarge; 494 s on the host); conflict v6 classified 3
certificates canonical-valid on the production path (i-0b8bcc6dbb30ef053,
receipt 27ca05a7…, 39 min launch-to-publication, semantic replays 385/69/541 s
standalone and 480/65/633 s nested, sampled peak 50.8 GiB on a 64 GiB box,
certificates 0.5–3.1 GB gz / 2.0–10.6 GB decompressed). Single-writer
extrapolation: 12,020 certificates × ≈ 984 s ≈ 3,300 box-hours; the sharded
spec (lane (2), sol-2) is what turns that into wall time. Memory rule for the
replay fleet: ≥ 64 GiB per box (the largest certificates exceed 50 GiB in
replay). Replayed so far: 1 of 12,020 (pilot-8) + the 3 conflict rows
classified but not Lean-consumed.

## 5. Open items handed to the inventory (sol-1)

- Reconcile the 207 uncertified rows outside the v3 queue (§1).
- Decide UNKNOWN-at-cap policy (22 rows): finer checked split vs longer cap.
- TRIM-FAIL cause (33 rows): unknown until v4 uploads diagnostics; budget them
  as re-solves.
- Confirm that `h1/` object count (12,020) equals distinct certified capacity
  rows (no duplicates / no stale keys from v2 quarantine).
