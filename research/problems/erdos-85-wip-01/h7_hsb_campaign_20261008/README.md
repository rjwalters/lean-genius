# H7 t=0 hsb3 certificate campaign: estimate and runbook (2026-10-08)

**Status: prepared, NOT launched. Not launch-ready until the items in section 5 are cleared.** No instance, role, launch template or S3 object of this
campaign exists. Everything below was measured on the existing cloud builder
(`i-04a61ff360a07bef2`, r7g.4xlarge) with at most 8 threads.

Goal: the external evidence for `SevenHighT0CanonicalHsbEvidence 3 F i` for each of the 28
structural cubes, which Lean turns into `OrderFortyNineStratumExcluded 7`
(`…HsbStratumCapstone.lean`). Per cube that is one checked cover CNF and one checked CNF per leaf:
377,776 leaf CNFs and 28 cover CNFs in total.

## Summary

| | |
|---|---|
| Estimate | **about 3,900 CPU-hours** of solver + checker time (3,915; stratified bootstrap 5%–95%: 2,900–5,400). The tail is heavy, so plan for **4,000–5,500 CPU-hours** (section 3.2). |
| Cost | Spot at $0.0147 per vCPU-hour: **$68 (50–93)**. At the builder's on-demand rate ($0.0536 per vCPU-hour): $247 (180–340). |
| Proof volume | about 20 TB of binary LRAT, streamed into cake_lpr and never stored (largest sampled proof 5.2 GB) |
| Fleet | 3 × 64-vCPU Graviton spot nodes (`r8g.16xlarge` / `r7g.16xlarge`), us-east-1 without 1d, 64 slots each, 2 GB checker heap, 2 h solver cap; about 24 h wall (18–33 h) |
| Budget cap | controller hard stop **$160**; suggested operator ceiling $200 including a residual pass |
| Sample | 1,400 leaves (50 per cube, seed 20261008): 1,398 UNSAT and `s VERIFIED UNSAT` within the 1 h cap; the 2 that hit the cap were re-run with a 2 h cap and verified after 58 and 64 CPU-minutes. None SAT, none rejected. All 28 cover CNFs verified. |
| Blocks a launch | operator go and budget; the AWS path is untested (canary first); shared spot quota. See section 5. |

## 1. What is certified, byte for byte

All files have the header `p cnf 17633 <clauses>`; Std.Sat variable `v` is DIMACS `v + 1`.

| file | bytes | Lean term |
|---|---|---|
| cube CNF | `canonical.body` ++ 21 mask units (720,825 clauses) | `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` |
| hsb CNF | cube ++ `h7hsb hsb 3 mask` | `orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 F i` |
| cover CNF | cube ++ hsb ++ `h7hsb cover 3 mask` | `SevenHighT0CanonicalHsbCoverChecked 3 F i (leaves 3 mask)` |
| leaf `n` CNF | cube ++ hsb ++ one **positive** unit per literal of cover line `n`, in line order | `SevenHighT0CanonicalHsbLeafChecked 3 F i rows_n` (`cnfClauseNegUnits (clause rows_n)`) |

Identity receipts:

* **Base cube = Lean term, all 28 cubes** (`receipts/base_cube_lean_identity.json`, builder job
  `20261008T051026-…-211746`). `EmitCube.lean` prints
  `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i` with interpreted `lake env lean --run`
  in the pinned image; each of the 28 outputs has the sha256 of the frozen root hash of the
  reviewed Python generator (`h7-frontier-map-20260915/results.json`), 15,151,828 bytes and
  720,825 clauses each. The sha256 values are the `cube_cnf_sha256` fields of
  `receipts/inputs.json`.
* **hsb and cover lines = Lean term** (`../h7_structural_pilot_20261008/receipts/hsb_lean_identity.json`,
  earlier job). `build_inputs.py` re-ran the native `h7hsb` (sha256 `dd0e2ab8…70d9`, the binary
  built by the builder from this branch) and requires the same sha256 values.
* `receipts/inputs.json` (sha256 `f2d2be89…cb6c`) pins every input file, the three derived CNF
  hashes per cube, the per-cube leaf-manifest hash and the batch-manifest hash
  (`27799edd…e785`, 5,945 claim units).

### Leaf manifest

Leaf `n` of a cube is line `n` (0-based) of `<cube>.cover`; its units are the negated literals of
that line. The full manifest (377,776 lines: cube, leaf, units, leaf CNF sha256; about 80 MB) is
not committed. It is regenerated deterministically:

```bash
python3.12 build_inputs.py --h7hsb <native h7hsb> --out <dir> --leaf-manifest   # writes <cube>.leaves.jsonl
```

and each `<cube>.leaves.jsonl` must hash to `leaf_manifest_sha256` in `inputs.json`. The worker
never trusts a precomputed leaf hash: `h7_common.Cube` re-hashes the pinned inputs when a batch
starts, and `cert_item.py` hashes the CNF file the solver and checker actually read and compares
it with the value recomputed from those inputs.

## 2. Sample

`sample.py`, builder jobs `20261008T050835-commit-50a06c7c033a-210080` (6 slots) and
`20261008T062840-commit-7c44792528b0-260174` (1 helper slot, same seed, reverse order). Every
item ran the campaign path: leaf CNF with positive-only units, CaDiCaL 3.0.1 (sha256
`fd601b82…72a2`) with `--lrat=true --binary=true`, proof streamed through the hashing relay into
cake_lpr (sha256 `4d47ffdd…464b`, 2 GB heap), solver cap 3,600 s. Receipts:
`receipts/sample_results.jsonl` (1,428 lines), `receipts/cover_receipts.tsv`,
`receipts/estimate.json`. Leaves were drawn with `random.Random("20261008:<cube>").sample`.

* **Covers: 28 / 28 `s VERIFIED UNSAT`.** Solver at most 40 s each (226 s in total), checker 77 s in
  total, 0.59 GB of proof in total.
* **Leaves: 1,398 / 1,400 certified, 2 capped, 0 SAT, 0 rejected, 0 heap exhaustions.**
* **Capped at 1 h:** `cube_F7_t0` leaf 2061 (24.5 M conflicts, 4.7 GB of proof when stopped) and
  `cube_F7_t6` leaf 119 (14.8 M conflicts). Both were re-run with a 2 h cap and a 4 GB heap (builder job
  `20261008T081402-commit-4c8bab43fccd-328154`, `rerun_items.py`, `receipts/capped_followup.jsonl`):
  **both `s VERIFIED UNSAT`**, after 3,808 s (26.9 M conflicts, 5.19 GB of proof) and 3,474 s
  (15.7 M conflicts, 3.11 GB). The 1 h cap was a wall-clock cap on a loaded host; both leaves
  needed about one CPU-hour. The table below uses the follow-up times for these two leaves
  (`receipts/sample_results_with_followup.jsonl`; the capped version is
  `receipts/estimate_table_capped_at_1h.md`).
* So **all 1,400 sampled leaves are certified**; the longest took 64 CPU-minutes of solving.
* 146 leaves were run twice (once by each sampler process). All 146 pairs produced the same proof
  sha256, so the proofs are reproducible with this binary.

"s" columns are solver + checker CPU seconds per leaf; "checker share" is the checker's part of
that; the range is the bootstrap 5%–95% of leaves × mean.

| cube | leaves | n | UNSAT+verified | capped | mean s | median s | p90 s | max s | mean conflicts | checker share | CPU-h (5%–95%) | proof TB | spot $ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| F6_t14 | 893 | 50 | 50 | 0 | 24.2 | 1.9 | 54 | 410 | 205k | 17% | 6 (2–11) | 0.04 | 0 |
| F6_t15 | 893 | 50 | 50 | 0 | 160.7 | 25.8 | 428 | 2594 | 1057k | 11% | 40 (19–66) | 0.18 | 1 |
| F6_t16 | 9,442 | 50 | 50 | 0 | 37.0 | 3.9 | 103 | 328 | 267k | 15% | 97 (57–144) | 0.50 | 2 |
| F6_t17 | 9,442 | 50 | 50 | 0 | 9.3 | 2.1 | 28 | 166 | 73k | 27% | 24 (12–41) | 0.15 | 0 |
| F6_t18 | 9,442 | 50 | 50 | 0 | 12.9 | 2.1 | 38 | 109 | 101k | 22% | 34 (22–47) | 0.20 | 1 |
| F6_t5 | 3,456 | 50 | 50 | 0 | 37.9 | 8.2 | 173 | 285 | 301k | 15% | 36 (22–53) | 0.20 | 1 |
| F6_t8 | 20,225 | 50 | 50 | 0 | 11.5 | 2.4 | 43 | 209 | 83k | 24% | 65 (30–110) | 0.32 | 1 |
| F7_t0 | 32,538 | 50 | 50 | 0 | 107.9 | 2.6 | 145 | 4172 | 736k | 11% | 975 (142–2463) | 4.65 | 17 |
| F7_t10 | 50,772 | 50 | 50 | 0 | 13.4 | 3.1 | 4 | 498 | 107k | 27% | 189 (45–468) | 1.15 | 3 |
| F7_t11 | 20,225 | 50 | 50 | 0 | 17.5 | 2.5 | 40 | 316 | 135k | 20% | 98 (49–166) | 0.53 | 2 |
| F7_t13 | 20,225 | 50 | 50 | 0 | 3.6 | 2.2 | 4 | 49 | 14k | 54% | 20 (14–30) | 0.08 | 0 |
| F7_t14 | 9,442 | 50 | 50 | 0 | 137.3 | 18.3 | 326 | 2106 | 872k | 10% | 360 (164–597) | 1.56 | 6 |
| F7_t2 | 11,025 | 50 | 50 | 0 | 39.8 | 2.3 | 81 | 628 | 313k | 14% | 122 (49–208) | 0.66 | 2 |
| F7_t3 | 11,025 | 50 | 50 | 0 | 36.9 | 5.4 | 108 | 337 | 311k | 15% | 113 (70–161) | 0.61 | 2 |
| F7_t4 | 11,025 | 50 | 50 | 0 | 22.7 | 2.8 | 80 | 168 | 189k | 18% | 70 (44–99) | 0.42 | 1 |
| F7_t5 | 3,456 | 50 | 50 | 0 | 62.5 | 2.4 | 71 | 1871 | 443k | 13% | 60 (16–129) | 0.30 | 1 |
| F7_t6 | 3,456 | 50 | 50 | 0 | 178.2 | 17.7 | 118 | 3727 | 997k | 9% | 171 (48–328) | 0.67 | 3 |
| F7_t8 | 3,456 | 50 | 50 | 0 | 78.5 | 19.1 | 122 | 1926 | 555k | 12% | 75 (30–147) | 0.37 | 1 |
| F7_t9 | 3,456 | 50 | 50 | 0 | 31.1 | 4.1 | 21 | 1158 | 265k | 16% | 30 (6–74) | 0.19 | 1 |
| F8_t0 | 32,538 | 50 | 50 | 0 | 25.7 | 4.4 | 82 | 245 | 219k | 18% | 232 (140–339) | 1.41 | 4 |
| F8_t1 | 11,025 | 50 | 50 | 0 | 18.3 | 4.2 | 66 | 109 | 164k | 19% | 56 (38–75) | 0.33 | 1 |
| F8_t2 | 11,025 | 50 | 50 | 0 | 14.1 | 2.7 | 38 | 143 | 114k | 22% | 43 (26–63) | 0.25 | 1 |
| F8_t3 | 11,025 | 50 | 50 | 0 | 12.9 | 2.3 | 51 | 97 | 113k | 23% | 40 (24–57) | 0.23 | 1 |
| F8_t4 | 11,025 | 50 | 50 | 0 | 72.0 | 32.6 | 169 | 615 | 606k | 13% | 220 (152–303) | 1.26 | 4 |
| F8_t5 | 3,456 | 50 | 50 | 0 | 43.8 | 18.1 | 179 | 291 | 363k | 14% | 42 (28–58) | 0.24 | 1 |
| F8_t6 | 20,225 | 50 | 50 | 0 | 21.8 | 2.8 | 77 | 118 | 174k | 18% | 123 (83–167) | 0.68 | 2 |
| F9_t0 | 32,538 | 50 | 50 | 0 | 33.8 | 5.5 | 110 | 294 | 298k | 16% | 306 (194–432) | 1.80 | 5 |
| F9_t1 | 11,025 | 50 | 50 | 0 | 87.5 | 17.0 | 190 | 1406 | 701k | 13% | 268 (126–448) | 1.49 | 5 |
| **total** | **377,776** | 1400 | 1400 | 0 | | | | | | 15% | **3915 (2864–5392)** | **20.4** | **68** |

Spot $ is CPU-hours / 0.85 × $0.0147.

The table, `receipts/estimate.json` and every interval quoted in this README are the byte-exact
output of the committed script with its defaults (20,000 bootstrap replicates, `random.Random(1)`),
run with Python 3.14.8 on the Mac from this directory:

```bash
python3 estimate.py --inputs-json receipts/inputs.json \
    --sample receipts/sample_results_with_followup.jsonl \
    --json receipts/estimate.json --md receipts/estimate_table.md          # --boot 20000 is the default
python3 estimate.py --inputs-json receipts/inputs.json --sample receipts/sample_results.jsonl \
    --json receipts/estimate_capped_at_1h.json --md receipts/estimate_table_capped_at_1h.md
```

The point estimate (3,915.35 CPU-h, 20.44 TB) does not depend on the bootstrap. The interval does,
slightly: 20,000 replicates give 2,864–5,392, 5,000 give 2,865–5,369 and 2,000 give 2,859–5,383
(the last two are codex's independent runs, room messages 52896–52901). The numbers were first
published while the script's default was still 5,000 and the run used `--boot 20000` explicitly;
the default now equals what was run.

## 3. Estimate

### 3.1 Main pass

| | CPU-hours | spot ($0.0147 / vCPU-h) | builder on-demand ($0.8568 / h for 16 vCPU) |
|---|---:|---:|---:|
| point estimate | 3,915 (solver 3,339 + checker 576) | $68 | $247 |
| bootstrap 5%–95% | 2,864–5,392 | $50–93 | $180–340 |

Dollar figures divide by an assumed utilisation of 0.85 (bootstrap time, idle tail of a node,
and slower cores when all 64 are busy; not measured on a full node). `r8g.16xlarge` spot was
$0.47/h in us-east-1a when checked (2026-10-08 05:13Z), which is half the assumed rate;
`r7g.16xlarge` was $0.93/h, which is the assumed rate. The builder itself (16 vCPU) would need
about 12 days of continuous running, so "on-demand" means on-demand 16xlarge nodes at the same
price per vCPU.

### 3.2 Tail risk

The distribution is heavy-tailed, and the range above understates the upside:

* The largest 1% of the samples (14 leaves) carry 40% of the sampled CPU time, the largest 5%
  carry 64%. 16 samples took more than 10 minutes and 7 more than 30 minutes. The Hill tail
  index on the pooled normalised sample is about 1.5 (finite mean, infinite variance).
* `cube_F7_t0` is a quarter of the estimate (975 CPU-h, range 142–2,463) because of a single
  sample of 70 minutes that stands for 651 leaves.
* **Leaves near or over one hour.** Two of 1,400 samples needed about an hour. Weighted by cube
  size that is an expected 720 such leaves (651 in `cube_F7_t0`, 69 in `cube_F7_t6`), with a very
  wide error (one observation each). With a 1 h cap they would all be solved twice (about 770
  CPU-hours wasted). **The campaign default is therefore a 2 h solver cap.** No sampled leaf
  needed more than 64 CPU-minutes, so nothing is known about leaves beyond that: every 0.1% of
  the leaves (378) that takes 2 h more than the sample suggests adds about 760 CPU-hours ($13).
* A cube that showed no hard leaf in 50 samples can still have them: with 50 samples, a cube whose
  true capped fraction is 2% shows none with probability 36%.
* Not in the estimate: memory-bandwidth slowdown on a fully loaded 64-core node, spot reclaims
  (at most the unfinished part of a 64-leaf batch per slot is lost, and partial receipts are
  carried forward), and the 2 GB heap proving too small for some leaf (none in 1,428 items, and
  not tested on the two longest leaves, which were re-run at 4 GB; such leaves go to the
  residual pass).

Planning figure: **4,000–5,500 CPU-hours, $70–95 on spot**. The controller hard stop of $160
allows about 9,000 CPU-hours at the assumed rate, which leaves room for a tail twice as heavy as
the sample shows.

### 3.3 Fixed overhead per leaf and batching

Each leaf CNF has 730k–1.02M clauses (15.6–31 MB). Measured on the builder:

| step | per leaf |
|---|---:|
| write the CNF to tmpfs from the in-memory cube and hash it | 0.02 s |
| CaDiCaL parse | 0.25–0.35 s |
| cake_lpr parse + heap initialisation (2 GB heap) | 1.5–2.4 s (1.2–2.3 s at a 1 GB heap) |
| **total** | **about 1.8 CPU-s, i.e. about 190 CPU-hours for 377,776 leaves (5% of the estimate, about $3)** |

The median leaf takes 2–5 s in total, so half of the leaves are dominated by this overhead, but
the CPU time is dominated by the hard leaves, and the overhead is small in dollars.

What is implemented: **one process per batch of 64 leaves** (`cert_batch.py`). The cube's bytes
(cube ++ hsb, verified against `inputs.json` once) stay in memory, so regenerating a leaf CNF is
a 0.02 s write. The solver and the checker still parse every leaf. **The certificate is per
leaf**, exactly the shape `SevenHighT0CanonicalHsbEvidence` consumes; nothing in Lean changes.

Options that would remove the parse, with what they would cost:

* **Smaller checker heap.** 1 GB instead of 2 GB saves about 0.3 s per leaf (about 30 CPU-h) and
  halves the memory per slot (1 GB heap + 0.15 GB solver), which would allow 2 GiB/vCPU
  instances. Three of the longest sampled leaves were re-checked at 1 GB (1,106 s solve) and
  500 MB (487 s and 325 s) and verified (`receipts/heap_test.jsonl`), but the full sample ran
  at 2 GB only. Not adopted for the first pass.
* **Incremental solving (one solver per cube, leaf units as assumptions).** Saves the solver
  parse (0.3 s per leaf, about 30 CPU-h) and may save search through shared learned clauses.
  But the proof is then one stream per process, in which a leaf's refutation depends on clauses
  learned for earlier leaves. Per-leaf certificates would have to repeat that shared history, or
  the certificate becomes one long proof per cube or per chunk, checked serially and lost as a
  whole on a spot reclaim. A per-cube proof would be a direct refutation of cube ++ hsb, which
  Lean already accepts (`sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbUnsat`), so in that
  variant the Lean evidence shape changes from `SevenHighT0CanonicalHsbEvidence` (cover + leaves)
  to one `Unsat` hypothesis per cube; a per-chunk proof ("these blocking clauses follow") is not
  an UNSAT statement and would need a new Lean statement and a checker mode for it. Not
  recommended: about $1 of parse time against a redesign of the certificate.
* **Coarser leaves** (case split on the rows of two empties, keeping the hsb3 clauses) would cut
  the leaf count by a factor of 10–50. Lean supports it today, because
  `…SemanticExclusion_of_hsbLeaves` takes an arbitrary leaf list; only the `Evidence` structure
  fixes the list to `leaves 3 mask`. The pilot found depth 3 about right for solver time, and
  this was not re-measured. Not recommended without a measurement.

### 3.4 Fleet shape

* **3 spot nodes of 64 vCPU** (`r8g.16xlarge`, `r7g.16xlarge`, with `m8g`/`m7g.16xlarge` as
  fallbacks; price-capacity-optimized; us-east-1 without 1d; bid ceiling $1.20/h). 64 slots per
  node, 2 GB checker heap: 64 × 3.5 GB = 224 GB peak.
* Wall time for the main pass: 3,915 / 0.85 / 192 vCPU ≈ **24 h** (18–33 h for the bootstrap
  range). Node lifetime is 36 h, the fleet request expires after 37 h.
* Why 3 and not 6: the account's spot quota is 384 standard vCPUs and is **shared**. About 180
  were in use by CI runners and other batch jobs when checked (2026-10-08 05:50Z). Six nodes
  would need the whole quota. `launch` accepts up to 6.
* Residual pass: 1 node, cap 24 h, 8 GB heap (the bootstrap lowers the slot count to fit).
* Budget: controller hard stop $160 (3 nodes × 36 h at the bid ceiling, with the controller's
  10% margin, is $143). Expected spend $50–100.

## 4. Runbook

Paths are relative to `research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/`. The controller
runs on the Mac (AWS profile `2am-admin`, single seat, in tmux). Nothing here starts an instance
until step 4.4.

| file | role |
|---|---|
| `h7_common.py` | cube inputs, exact CNF assembly, leaf units, batch manifest |
| `build_inputs.py` | builds and pins the inputs directory (`inputs.json`), optional full leaf manifest |
| `EmitCube.lean`, `check_base_identity.{py,sh}` | base cube = Lean term, on the builder |
| `cert_item.py` | one CNF: write, hash, CaDiCaL → FIFO → relay → cake_lpr (imports the reviewed H1 `cert_row.solve_and_check`) |
| `cert_batch.py` | one claim unit (64 leaves or one cover), one process, per-leaf receipts |
| `cert_worker.py` | node supervisor: claims, partial uploads, ledgers, STOP / ALARM; `--local-store`, `--plan` |
| `cert_bootstrap.sh` | node bootstrap (pinned CaDiCaL and cake_lpr binaries by sha256, preflight, claim self-test, hard-stop timer, slots capped by memory) |
| `cert_controller.py` | Mac controller over the reviewed verdict-pass controller: `plan`, `setup`, `freight`, `launch`, `watch`, `status`, `residual`, `release-errors`, `stop` |
| `collect_receipts.py` | completeness check and per-cube receipt tables |
| `sample.py`, `estimate.py` | the cost sample and this estimate |
| `e2e_test.sh` | worker end-to-end test against a local directory store (12 checks) |
| `test_campaign.py` | metadata-only unit tests: codex's collector fixtures and batch-limit reservation fixtures, batch heap/STOP/alarm behaviour, binary pins, canary selection |

### 4.1 Lessons from the H1 census, and where they are applied

| lesson | here |
|---|---|
| cake_lpr exits 0 even on failure; only `s VERIFIED UNSAT` counts | `cert_row.solve_and_check` (unchanged) sets CERTIFIED only on that stdout line plus CaDiCaL exit 20 with `s UNSATISFIABLE`; the bootstrap preflight requires a truncated proof to be rejected; `e2e_test.sh` runs a fake checker that exits 0 without the line and requires ALARM + STOP |
| exclude us-east-1d (all 7 H1 reclaims) | `EXCLUDE_AZ = ["us-east-1d"]` is the default of `launch`; visible in `launch N --dry-run` |
| unique work directories (a duplicate claim deleted a live attempt) | `cert_item.py`: `<cube>.<item>.<pid>.<time_ns>` on tmpfs; `cert_worker.py`: `<batch>.<epoch>.s<slot>` |
| re-read claim owners every pass | `cert_controller.one_pass` clears the owner cache before the reviewed pass; claim body = instance id |
| "complete" means CERTIFIED, not "has a ledger" | controller stops the fleet only when every manifest row has a CERTIFIED ledger |
| `Popen.poll()` reaped the child (ECHILD) | inherited: the watchdog peeks with `waitid(WNOWAIT)` |
| a solver cap hit on the longest row | the default cap is 2 h (twice the longest sampled leaf); a cap is still a normal outcome: `SOLVER_TIMEOUT` is a status, the batch ledger is `INCOMPLETE`, and `residual` builds the second-pass manifest |
| spot reclaim costs rerun time | the claim unit is 64 leaves (about 25 CPU-minutes on average); receipts of a running batch are uploaded every 10 minutes to `partial/`, and the node that re-claims a released batch re-validates and carries the CERTIFIED ones forward |
| a receipt is only as good as the checker that produced it (codex review, room 52742–52751) | one approved cake_lpr binary (`h7_common.CAKE_LPR_SHA256` = `4d47ffdd…464b`, the builder's build of commit `a36874a8`, used for the sample and the covers) is shipped as freight; nodes do not compile it; worker, batch runner and collector all refuse any other solver or checker hash |
| memory budget must be the true peak (same review) | the checker heap is fixed for a run; `CHECK_HEAP_EXHAUSTED` is recorded and left to the residual pass (larger heap, fewer slots); the bootstrap sets slots = min(vCPUs, (RAM − 8 GB) / (heap + 1.5 GB)) and the worker refuses a configuration that does not fit |
| check-then-discard | no proof and no CNF is stored; the receipt keeps the CNF sha256, leaf id and units, proof sha256 and bytes, solver and checker CPU seconds, conflicts and binary hashes |

### 4.2 Receipts

Per item (one JSON line in `results/<batch>.<iid>.<t>.jsonl.zst`): `cube`, `kind`, `leaf`, `units`,
`cnf_sha256` (of the file read by solver and checker) and `expected_cnf_sha256`, `cnf_bytes`,
`proof.sha256`, `proof.bytes`, `solver.{returncode,cpu_seconds,wall_seconds,conflicts,…}`,
`checker.{verified_line,cpu_seconds,heap_mb,…}`, `binaries` (sha256 of CaDiCaL and cake_lpr),
`status`, `host`, timestamps. Per batch (`ledger/<batch>.<iid>.<t>.json`): status, counts,
`not_certified`, sha256 of the receipts file, sums of CPU and proof bytes, `inputs_json_sha256`,
`manifest_sha256`, repository commit.

S3 layout under `s3://2am-erdos85-certs/sat49/h7hsb-20261008/`: `freight/`, `claims/`,
`partial/`, `results/`, `ledger/`, `control/` (`STOP`, `ALARM-<batch>`), `nodes/<iid>/`,
`selftest/`. The node role can read and write only this prefix (and read the verdict freight for
the pinned CaDiCaL build).

### 4.3 Before any launch (no cost)

```bash
# identities (already receipted; re-run after any change to the generators)
e85-remote run erdos85/h7t0-formal-20261007 --full --mem 16 --threads 1 -- \
    bash ../research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/check_base_identity.sh
# pinned inputs on the builder, then onto Stripe (h7hsb = proofs/.lake/build/bin/h7hsb of this branch)
e85-remote run erdos85/h7t0-formal-20261007 --host --full -- python3.12 \
    research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/build_inputs.py \
    --h7hsb ~/h7pilot/bin/h7hsb.lean --out ~/h7camp/inputs --jobs 7
e85-remote ssh 'tar -C ~/h7camp/inputs -cf - . | zstd -q -3 -c' | zstd -dc | \
    tar -C /Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008/inputs -xf -
shasum -a 256 /Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008/inputs/inputs.json
#   must print f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c (= receipts/inputs.json)

# approved checker binary onto Stripe (freight source); must print 4d47ffdd…464b
e85-remote ssh 'cat ~/h7pilot/bin/cake_lpr' > /Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008/tools/cake_lpr
python3 test_campaign.py                                           # 16 unit tests, no solver

# dry runs: none of these creates or changes anything in AWS
python3 cert_controller.py plan
python3 cert_controller.py setup --commit <sha> --dry-run        # role policy, launch template, user data
python3 cert_controller.py freight --dry-run                      # packs inputs (2.6 MB), checks the cake_lpr hash, no upload
python3 cert_controller.py launch 3 --dry-run                     # the exact create-fleet request
python3 cert_controller.py status                                 # read-only
python3 cert_controller.py --pass canary host-launch --commit <sha> --dry-run   # controller host request + policy
# worker end to end on the builder, local directory store, about 6 minutes, 2 threads; last line E2E_ALL_PASS
e85-remote run <sha> --host --full -- bash research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/e2e_test.sh \
    ~/h7camp/inputs ~/h7camp/e2e ~/h7pilot/bin/cadical ~/h7pilot/bin/cake_lpr 2
# what a node would claim, without claiming
python3.12 cert_worker.py --inputs <inputs> --inputs-sha256 f2d2be89… --manifest-sha256 27799edd… \
    --iid i-plan --slots 64 --mem-gb 504 --local-store /tmp/empty-store --plan
```

### 4.4 Launch (operator go required)

`<sha>` is a pushed commit of `erdos85/h7t0-formal-20261007` that contains this directory; nodes
and the controller host clone that branch and check out exactly that commit. All commands run
from this directory on the Mac with profile `2am-admin`. `C="python3 cert_controller.py"`.

**Two passes, two prefixes.** The canary runs under its own S3 prefix
(`sat49/h7hsb-20261008-canary`), tag and launch template (`e85-h7hsb-20261008-canary`); the full
run uses `sat49/h7hsb-20261008` / `e85-h7hsb-20261008`. The persistent `control/STOP` that ends
the canary therefore never reaches the full run, and nothing is ever cleared (codex, room 52854).
`launch` refuses to start a fleet into a prefix that holds a STOP or an ALARM marker. An ALARM, a
budget stop or a STOP of unknown cause can never be cleared; a completion or operator stop can be
archived with `launch --clear-stop "<reason>"`, which is logged under `transitions/`.

**The controller does not run on the Mac.** `host-launch` starts a dedicated `t4g.small`
on-demand instance (about $0.017/h) with its own least-privilege role
(`Erdos85H7HsbController`: describe, terminate and delete only resources tagged with this
campaign, read/write/delete only the two prefixes; it cannot launch anything). It runs `watch`
in a loop until the watch acts (budget stop or everything CERTIFIED), uploads its report every
pass, then powers itself off (terminate). It has its own 72 h hard-stop timer. This was chosen
over the builder because the builder idle-stops after 60 minutes and its uptime wall resets to
10 h at 00:00 UTC, and because the builder's role has no EC2 rights.

```bash
# ---- Phase 1: canary (1 node, 8 pinned rows = 2 covers + 384 leaves, $10 hard stop, 5 h lifetime)
$C --pass canary freight                      # inputs + approved cake_lpr -> canary prefix
$C --pass canary setup --commit <sha>         # roles, security group, canary launch template
$C --pass canary launch 1
$C --pass canary host-launch --commit <sha>   # detached watch; stops the node when all 8 rows are CERTIFIED
$C --pass canary status                       # repeat; see "Status" below
#   expect: nodes/<iid>/bootstrap.log ends "bootstrap ok" within ~10 min; 8 CERTIFIED ledgers;
#   3 objects per cover under covers-retained/; >= 1 object under partial/; then the controller
#   writes control/STOP + control/STOP-CAUSE ("all batches CERTIFIED; stopping") and the node terminates.
aws s3 sync s3://2am-erdos85-certs/sat49/h7hsb-20261008-canary/results/ <Stripe>/run-canary/results/
python3 collect_receipts.py --inputs <Stripe>/inputs --results <Stripe>/run-canary/results --cubes cube_F6_t14
#   expect cover_certified true and certified_leaves 64 (exit 1: the cube is not complete, by design)
$C --pass canary transition --note "<who checked what>"   # must print "ok": true

# ---- Phase 2: full run (3 nodes, $160 hard stop, 36 h node lifetime)
$C freight
$C setup --commit <sha>
$C launch 3                                   # refuses without an ok transition record, or with STOP/ALARM present
$C host-launch --commit <sha>
$C status
```

**Status (run from the Mac at any time, read-only):**

```bash
cd research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008
python3 cert_controller.py status                 # full run;  add --pass canary before `status` for the canary
```

It prints the controller host's last report (`estimated_spend_usd`, `certified_batches` of
5,945, `certified_items`, `statuses`, `orphans_released`, `action`), `percent_batches_certified`,
the live nodes, the controller host, and whether a STOP or an ALARM marker exists. The report is
at most 5 minutes old while the host is alive; `controller_hosts: []` with no `action` in the
last report means the host died and must be restarted with `host-launch` (the nodes keep
working without it, bounded by their own lifetime and the fleet expiry).

**What the canary covers.** The main manifest lists the 28 cover rows first, so "the first N
batches" would run covers only. The canary pass instead pins eight ordinary manifest rows by id:
the covers of `cube_F6_t14` and `cube_F7_t10`, and leaf batch `b0000` (leaves 0–63) of
`cube_F6_t14`, `cube_F6_t18`, `cube_F7_t10`, `cube_F7_t13`, `cube_F8_t0` and `cube_F9_t0`:
**2 cover CNFs + 384 leaf CNFs = 386 items**, with the smallest and the largest hsb clause sets.
Partial receipts are uploaded every 120 s. It exercises: bootstrap and both binary hash checks,
the S3 store and the IAM policy, the launch template, claims, partial and final receipts, cover
retention, the collector, the controller host, and the completion stop against a live instance.
A leaf that hits the 2 h cap makes its batch `INCOMPLETE`; then the canary does not complete by
itself: stop it with `$C --pass canary stop --note ...` and judge the receipts by hand. Not
covered by the canary: a real spot reclaim with carry-forward and the ALARM path (local-store
`e2e_test.sh` only), and the budget stop at its real threshold (to exercise the code path against
live instances, run the canary host with `host-launch --hard-stop-usd 0.01`, which stops at the
first pass; that canary then has to be repeated for the receipts). Because the canary has its
own prefix, the full run solves these 386 items again (about $0.10).

**Hard stops, all independent of any session:** (a) the controller host's budget stop; (b) the
fleet request expires after node lifetime + 1 h and terminates its instances; (c) each node powers
itself off after its lifetime (`systemd-run`, shutdown behaviour = terminate) even if the worker
hangs; (d) a node powers off when nothing is left to claim; (e) `control/STOP` is read before
every claim and every 10 minutes inside a batch. If the controller host is lost, (b)–(d) bound
the spend at 3 nodes × 37 h × the $1.20 bid ceiling = $133.
`$C stop --note "<why>"` stops everything by hand and records the cause.

**Retained cover proofs (codex, room 53116).** Cover rows, and only cover rows, keep the exact
CNF bytes and the exact binary LRAT proof bytes: `covers-retained/<cube>.cover.{cnf,lrat,json}`
under the campaign prefix (the JSON holds sha256, sizes, depth 3 and the cube ++ hsb ++ cover
extension layout). For these rows CaDiCaL writes the proof to a file and cake_lpr checks that same
file. Leaves stay check-then-discard. The same function already produced all 28 on the builder
(`retain_covers.py`, job `20261008T153314-commit-b8bf078f3ef1-615947`): 28 / 28
`s VERIFIED UNSAT`, 0.55 GB of CNF and 0.59 GB of proof at `~/h7camp/covers-retained/` on the
builder, and every proof has the sha256 of the streamed proof in the cost sample
(`receipts/covers_retained_index.json`).

Milestones are not posted by the controller host (it has no access to the squad room); whoever
polls `status` posts them.

### 4.5 During the run

* A `control/ALARM-<batch>` object means a proof was rejected by cake_lpr (`CHECK_FAILED`) or the
  solver answered SAT. The node writes STOP and the whole fleet drains. Do not restart before the
  item is understood: SAT on a leaf would be a completion graph of the cube, or a generator error.
* `ERROR` ledgers are infrastructure failures; six on one node stop that node. After reading the
  `stderr_tail`, `python3 cert_controller.py release-errors --yes` frees those batches.
* A reclaimed node's claims are released by `watch` (owner instance no longer live). Top up with
  `launch N`; nodes started later skip claimed batches.
* `SOLVER_TIMEOUT` and `CHECK_HEAP_EXHAUSTED` leaves are not retried in this pass; their batch
  ledger is `INCOMPLETE` and they go to the residual pass.
* STOP is honoured before every claim and between items; an item that is already running finishes
  first (at most the solver cap). `stop` on the controller also terminates the instances.

### 4.6 After the fleet drains

```bash
python3 cert_controller.py status                 # certified_batches must equal 5945, or:
python3 cert_controller.py residual               # writes .../residual-manifest.jsonl (one leaf per row)
# residual pass, if any: longer cap and larger heap (the bootstrap lowers the slot count to fit),
# same code path, its own launch-template version
python3 cert_controller.py freight --manifest <residual-manifest.jsonl>
python3 cert_controller.py setup --commit <sha> --manifest <residual-manifest.jsonl> --cap 86400 --heap-mb 8000
python3 cert_controller.py launch 1 --manifest-pass --clear-stop "residual pass after completed main pass"
python3 cert_controller.py watch --manifest <residual-manifest.jsonl>   # short pass: from the Mac, or adapt host-launch
# completeness: every leaf of every cube and all 28 covers, hashes recomputed from the pinned inputs
python3 collect_receipts.py --inputs <Stripe>/inputs --results <Stripe>/run/results --out <Stripe>/collected
```

`collect_receipts.py` exits 0 only if all 28 cubes are complete. Commit its `summary.json` and the
per-cube `*.receipts.tsv.zst` under `receipts/` (about 377,776 lines in total); the raw results
stay in S3 and on Stripe.

A leaf that is still capped after the residual pass needs a deeper split. Lean already allows
that without new theory: `sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLeaves` takes an
arbitrary leaf list, and `cnf_unsat_of_blocking_clauses` composes per formula, so a hard leaf CNF
can itself be split by further positive-unit blocking clauses with its own cover CNF. That needs
a small new Lean wrapper (one level of nesting) and is not implemented here.

## 5. What blocks a launch

1. **Operator go and a budget.** Nothing has been created in AWS.
2. **The AWS path has not run.** Worker, batch runner, collector and the local store are tested
   end to end on the builder (`receipts/e2e_test_builder.txt`, 15 checks, builder job
   `20261008T153314-commit-b8bf078f3ef1-615947`) and by `test_campaign.py` (16 tests). The
   controller's `plan`, `status`, `residual`, and the `--dry-run` forms of `setup`, `freight` and
   `launch` ran on the Mac. **Not exercised:** `cert_bootstrap.sh` on a fresh spot node, the S3
   store class (the same aws-cli calls as the H1 worker), the IAM policy, the launch template,
   orphan release and the budget stop against live instances, `release-errors --yes`, the
   controller host (`host-launch`: its role, its user data, `watch` under an instance role), the
   `transition` record and `launch --clear-stop`. All of these exist only as dry runs. The
   one-node canary in 4.4 (386 items: 2 covers and 384 leaves) is mandatory.
3. **Shared spot quota** (384 vCPU, about 180 in use by other workloads). Three nodes fit; more
   needs a quota increase or a quiet period.
4. **The security group `erdos85-verdict-noingress` no longer exists.** `setup` now recreates it
   (no ingress rules), as the reviewed verdict-pass setup did.
5. **Leaves beyond the cap.** None of the 1,400 sampled leaves needed more than 64 CPU-minutes,
   and the default cap is 2 h. Leaves that exceed it go to the residual pass (24 h cap). A leaf
   that does not finish there would need a deeper split, which needs a small Lean wrapper that
   does not exist yet (section 4.6). This is a risk, not a known obstacle.
6. **The approved checker binary must run on the fleet AMI.** `cake_lpr` `4d47ffdd…464b` was linked
   on the builder (AL2023 arm64). The bootstrap preflight (accept a valid proof, reject a
   truncated one) fails the node cleanly if it does not run on the current AL2023 image.
7. **Pinned commit.** `setup --commit` must name a pushed commit of
   `erdos85/h7t0-formal-20261007` that contains this directory.

Not blockers, but open: the Lean side still has to state how 377,804 receipts become the
`SevenHighT0CanonicalHsbEvidence` hypotheses (as for H1, the receipts are external evidence);
STOP does not interrupt an item that is already running (bounded by the cap; `stop` terminates
the instances anyway); checker-heap exhaustion was tested with a stub, not with a real
exhausted checker.

## 6. Head profile (2026-10-08, INTERIM, after the canary)

The canary showed that the lexicographically first leaves of a cube are much harder than the
uniform cost sample suggested. `profile_index.py` (builder job
`20261008T183708-commit-30eef0821a39-712073`, 14 slots, 2 h cap, 2 GB heap, campaign path) ran
leaves at indices 0, 1, 2, 4, 8, … plus one random leaf per geometric stratum for eight cubes;
223 of 230 planned leaves are in `receipts/head_profile.jsonl`, with each leaf's tree position
(`leaf_tree.py`). `head_estimate.py` re-weights by index stratum
(`receipts/head_estimate_table.md`, `receipts/head_estimate.json`; canary leaves in
`receipts/canary_head_leaves.json`).

* **Hardness tracks the first two rows.** Leaves under the first canonical row with a small
  second-row index (roughly the first 50–500 leaves of a cube) cost 10–100 times the cube mean;
  beyond index ~1,000 the strata agree with the uniform sample. `cube_F7_t10` and `cube_F7_t13`
  have no hard head.
* **Total: 3,714 CPU-hours (3,392–4,672)**, against 3,915 from the uniform sample: the head is
  expensive per leaf but short, and the sample had over-weighted two long leaves. Unprofiled
  cubes carry the pooled factor 0.95 (range 0.71–1.67 seen on the profiled cubes).
* **Leaves over 2 h: 5 of 223 profiled** (all at indices 1–4 of the three 4-4-4 cubes `F7_t0`,
  `F8_t0`, `F9_t0`; 6.8–8.2 GB of proof when stopped), none among the 1,400 uniform samples. The
  stratified expectation is about 16 leaves in the campaign; with one or two observations per
  stratum the honest range is 10–200. They are counted at the cap, a lower bound.
* **Heap.** 3 of 223 leaves (`F7_t0` 256, `F8_t4` 8 and 128; solver UNSAT after 4,834–6,988 s,
  proofs 4.7–6.0 GB) ended `CHECK_HEAP_EXHAUSTED` at the 2 GB checker heap. That is a resource
  limit, not a rejection, but the solve is wasted. The longest verified proofs were 5.2 GB at a
  4 GB heap and 3.9 GB at 2 GB.
* **Batches.** A 64-leaf batch at the head of a hard cube is 10–30 CPU-hours in ONE slot
  (`F8_t4` leaves 0–8 alone took 8 h). It would straggle past the rest of the run and lose
  hours on a spot reclaim.

Recommended changes before the main pass (not yet implemented; they change the manifest sha):
checker heap 6,000 MB on r-type 16xlarge only (64 × 7.5 GB = 480 GB); head rows first and in
small batches (the first 1,024 leaves of every cube in batches of 4, at the front of the manifest);
2 h cap unchanged; residual pass with 12 h cap and 16 GB heap; main-pass hard stop stays $160.

## 7. Main-pass configuration after the head profile (manifest v2, 2026-10-08)

This section supersedes the earlier sections where they differ (2 GB heap, 5,945 batches, the
386-item canary, m-type fallbacks).

* **Manifest v2** (`h7_common.batches`): 28 cover rows; then head rows `<cube>-h<k>` (leaves
  below index 1,024 in batches of 4, interleaved over the cubes so leaves 0–3 of all 28 cubes are
  claimed first); then tail rows `<cube>-b<k>` (64 leaves from index 1,024 on). 12,605 rows, sha256
  `0deb438f9bd7f5cfb840fd799330e6b80e70a043b21f96fcf0737c826515290c`. A leaf is still (cube, leaf
  index) with the same units and CNF sha256; `inputs.json` is unchanged (`f2d2be89…cb6c`; its
  `batches` and `batch_manifest_sha256` fields describe the v1 manifest).
* **Checker heap 6,000 MB, `r8g.16xlarge` / `r7g.16xlarge` only.** The bootstrap sets slots =
  min(vCPUs, (RAM − 8 GB) / (heap + 1.5 GB)) = 64 on 512 GiB.
* **`CHECK_HEAP_EXHAUSTED`** is never re-solved at the same heap within a pass; the proof is
  streamed and not kept, so it cannot be re-checked without re-solving. The leaf goes to the
  residual pass.
* **Residual pass:** `setup --commit <sha> --manifest <residual-manifest.jsonl> --residual` sets a
  12 h cap and a 16 GB heap (28 slots on 512 GiB).
* **Canary selection** is now 2 covers, 2 head rows of `cube_F6_t14` and 6 tail rows = 394 items.
  The canary that ran on 2026-10-08 used the v1 manifest: 5 of 8 rows CERTIFIED before an operator
  stop, one spot reclaim with orphan release and partial-receipt carry-forward exercised.
* **Controller host** returns on any STOP marker and powers off (unit-tested with a mocked pass;
  not yet seen on a live host).
* **Split-leaf lemma:** `sevenHighT0CanonicalHsbLeafChecked_of_split` in
  `proofs/Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeafSplit.lean`, built on the builder
  (job `20261008T220255-…-821964`, axioms `propext`, `Quot.sound`). No split tooling exists yet.
* Tests: `test_campaign.py` 21 tests; `e2e_test.sh` 15 of 15 (builder job
  `20261008T220330-commit-ff46715e06e0-822935`).

## 8. Final head profile (230 leaves, 2026-10-08 23:18Z) — revises section 6

The last six profile leaves were the slowest and change the capped-leaf picture
(`receipts/head_profile.jsonl`, `receipts/head_estimate.json`, `receipts/head_estimate_table.md`):

* **Total 4,109 CPU-hours (3,653–5,241)**, capped leaves counted at the 2 h cap (a lower bound).
* **10 of 230 leaves hit the 2 h cap**, no longer only at indices 1–4: `F9_t0` 1, 2, 3, 4, 118,
  164; `F8_t4` 3, 107; `F8_t0` 4; `F7_t0` 1. Four more were solved but ended
  `CHECK_HEAP_EXHAUSTED` at 2 GB (`F8_t4` 8, 12, 128; `F7_t0` 256).
* **Expected leaves over 2 h: about 140 in the eight profiled cubes, about 270 in the campaign**
  if the other cubes behave alike. This rests on single capped observations in strata of 64–128
  leaves (`F9_t0` and `F8_t4`, indices 64–256), so the range is wide: tens to several hundred.
  None of the 1,400 uniform samples exceeded 2 h, which bounds the campaign-wide fraction at
  about 0.2% (roughly 800 leaves) with 95% confidence.
* **Residual load is not measured**: no leaf has been run beyond 2 h. At 4–12 h each, 270 leaves
  are 1,100–3,200 CPU-hours ($19–55 on spot); 800 leaves at 12 h would be 9,600 CPU-hours ($166).
  A leaf that exceeds 12 h needs the split of section 4.6 (the lemma exists, the tooling does not).
