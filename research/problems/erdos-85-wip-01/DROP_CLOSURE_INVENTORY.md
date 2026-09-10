# Drop closure inventory

Working inventory for operator goal47 / board37. Owner: codex-sol-1;
independent coverage review: codex-sol-3; fleet/storage numbers: Claude;
replay-shard specification: codex-sol-2, reviewed by Claude.
Status: SOURCE-AUDITED DRAFT; live fleet counts, artifact reconciliation,
and cost estimates remain open. No solver or fleet launch authorized by
this inventory. Preparation is at zero incremental spend until the funding gate.

## Subsequent local replay addendum (2026-09-10)

All270 surviving root candidates (256 positive cubes plus14 covers) now
pass both pinned local checkers, with540 successful invocations and no
missing, failed or timed-out receipts. The complete receipt audit joins
current reconstructed CNF hashes, compressed/raw proof hashes, checker pins
and explicit acceptance markers. All45 H5 header mismatches are reconciled.
See `closure-inventory-evidence/local-replay-20260910/README.md`.

This updates the baseline metadata-only status below. It does not establish
remote durability, a rebuilt current-source certificate bank, or final grid
assembly. The136 missing local direct-root proofs remain. One H3 cover has
also compiled as a generated-CNF UNSAT theorem against existing imports;
its printed native_decide axiom dependency is preserved in the receipt.
The local H1 empty-artifact anomaly is resolved as unusable; it was already
counted among the178 outside-v3 gaps. Addendum peer review is pending.

## Required mathematical output

Prove `minDegreeForC4 48 = 8` and `minDegreeForC4 49 = 7`, hence the strict
drop. This finite result does not settle eventual monotonicity (Erdős85).
The source socket is
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks`
in `Erdos85OrderFortyNineSmallHighVerifiedFrontier.lean`.
Its four inputs are H1 exclusion, two canonical H3 LRAT checks, three
canonical H5 LRAT checks, and H7 exclusion. The five check indices are
bounded natural numbers (H3 index<=1, H5 index<=2).
`Erdos85OrderFortyNineSmallHighDropFrontier.lean` consumes these inputs
via `minDegreeForC4_fortyEight_fortyNine_exact_of_smallHighLratChecks`.
All these are conditional interfaces until actual evidence fills the inputs.

Source inspection: integration checkout at 7cbbe110b2; no new Lean build
claimed. A file existing or a source theorem signature is not evidence that
its certificate hypotheses have been supplied.

## Obligation map

| Sector | Existing interface/evidence | Missing closure obligation | Owner | Compute and storage basis |
|---|---|---|---|---|
| H1 producer | Exact pinned metadata join:12,054 unique listed objects, all in13,351-row capacity inventory; three conflicts classified canonical-valid by review1538 | Validate contents/receipts and reconcile advancing publication; producer certification is not Lean consumption | Claude fleet, sol-1 coverage | 1,297 lack listed objects:1,119 inside v3,178 outside; these are metadata gaps, not a launch queue |
| H1 lost-box recovery | Editor reports seven UPLOAD-FAIL tags on vanished spot instance i-01f0d952483d8f066 | Check S3 and any persistent EBS/snapshots for copies; if absent, put each tag exactly once in re-solve queue; recover orphan mid-solve claims separately | Claude | Reported 4.5–6 h solve+trim each, 11–20 GB DRAT each; seven slots imply 31.5–42 task-hours, NOT automatically 31.5–42 whole-instance hours when concurrent |
| H1 surviving quarantine | Claude dated readback at2026-09-10 05:01Z reports13 quarantined proofs on i-0ccf0dc6a398156d8, plus eight live slots | Revalidate liveness and files; preserve and multipart-upload durable copies before any allowed termination; verify create-only publication and content hashes | Claude | Upload sizes and duration unverified; memo hold remains until recovery; no launch here |
| H1 Lean consumption | Frozen replay validated by pilot and conflict-v6; memo says one certificate consumed on current route | Reconcile exact consumed-tag manifest and imports; sharded single-writer replay; merge without duplicate or omitted inventory rows; close checked-bank residual | codex-sol-2, Claude review; sol-1 coverage | 983.6 s/cert pilot basis gives 3,284.13 box-hours for 12,020, excluding production, failures, startup, transfer and aggregation; do not multiply this into core-hours without assigned vCPU count |
| H3 | Two canonical LRAT inputs at the top-level socket; finer cube-cover source has four scout cells, each 7x8 | Match old paused jobs to exact current CNFs; supply leaf checks and cover proofs, then consume the four scout-base UNSAT results through the alternate cube-grid terminal | sol-1 coverage; executor owner to assign | Finer source defines 224 positive cubes and eight negative cover obligations, before any recursive split; solve time/GB unknown |
| H5 | Three canonical LRAT inputs; finer cube-cover source has three cells, each 7x8 | Match artifacts to current CNFs; supply leaf checks and cover proofs, then consume the three base UNSAT results through the alternate cube-grid terminal | sol-1 coverage; executor owner to assign | 168 positive cubes and six negative cover obligations, before recursive split; solve time/GB unknown |
| H7 | Canonical empty-cube capstone requires evidence vectors of lengths19,15,7,2 | Fill all43 entries with accepted direct or split-tree evidence and identify assembled consumer | sol-1 coverage, codex-sol-3 review | 43 top-level evidence entries, NOT necessarily43 solver jobs; split-tree leaf count/time/GB not yet reconciled |
| Final Lean closure | Checked-bank aggregation and finite drop consumer interfaces exist | Compile complete evidence modules and final theorem; inspect axiom set and ensure no unresolved hypothesis or sorry; publish final manifest | Claude integrator; sol-1 audit | Final compile/aggregation budget unmeasured; no unconditional claim until done |

## Landed alternate route for the finer cube campaign

`Erdos85OrderFortyNineSmallHighCubeGridTerminal.lean` already contains
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighCubeBaseUnsat`.
It consumes H1 and H7 exclusions plus seven base UNSAT proofs: H3 scout
B1, C1, C2 and dist2, and H5 masks T0, T1, T2. For each base, the checked
cube-grid theorem supplies UNSAT from its cover and leaf evidence. This
route directly constructs `hno49`, which the finite-drop core consumes.
It does NOT require reconstructing five monolithic canonical LRAT arrays.
The original five-check socket remains a valid alternative interface;
its certificate bank and the seven-base cube route must not be double-counted.

The concrete generated seven-base endpoint module still needs evidence
assembly and compilation. The existence of the generic terminal does not
establish that any of the seven base obligations is discharged.

## Queue counts must not be conflated

The operator memo's 132 paused Tier-A H3/H5 jobs are a historical queue
count. The landed file `Erdos85OrderFortyNineSmallHighCubeCover.lean`
defines four H3 cells plus three H5 cells, each with selector sizes(7,8),
and proves a positive-cube count of392. Each cell also requires left/right
cover UNSAT, giving14 cover obligations. The file provides a checked-grid
implication, not a completed bank of certificates. No mapping from132 to
392 has yet been established here. Do not sum or substitute those counts
until canonical CNF hashes and selector assumptions are joined.

Historical room records give a specific reason not to revive the132 count:
message36891 identifies `run_tierA_396_restart.py` as a separate264+132
H3-B1 lineage. Message36805 reports that the old H5 DIMACS bases declared
29,500 variables while containing literal29,632. Those legacy files cannot
be substituted for the corrected Lean-exact bases. These are historical
provenance findings, not fresh artifact readbacks.

The current `sat49/build_small_high_socket_artifacts.py` hard-pins the
following reviewed lineage (read directly from `APPROVED_PINS`):

| Item | SHA256 |
|---|---|
| Root manifest | `05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76` |
| Queue receipt | `fa07876764990816f4d7a5940b09958c33d86676edcc3cddcbabad32b482d103` |
| Queue | `91cd2b14a3d0f5a3b9d30d94a4765928a885da74f428a754aadcda5c9ada504b` |
| Worker receipt | `35d1f8a4f616630ca60cd37ee364d9bb81080299695f11d0a6fbac11656db108` |
| Worker | `137e57dc3884fc2f61986cb0ed56762e3fe93708331e8f600fc83aa535e5d22a` |

These constants identify the expected artifact lineage. They do not prove
that the referenced files or completed certificates survived the outage.
The local readback below verifies these five files. The remaining audit
is to join every required root or split leaf to durable accepted evidence.

### Surviving local406-root metadata, current readback

The approved manifest, queue, queue receipt, worker and worker receipt were
located under `/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex`
and all five hashes above matched. The approved worker filename is
`tierA-root-worker-dff2402069.py`; similarly named older workers differ.
The queue has406 unique IDs and exactly matches the manifest's root job set.

| Local metadata | Count |
|---|---:|
| Required root IDs / existing root directories | 406 /406 |
| Root directories with ledger.line | 274 |
| Root directories with job.lrat.gz | 270 |
| Ledger claims saying lratcheck=VERIFIED and upload=uploaded | 270 |
| Root IDs without any ledger | 132 |
| Root IDs without local compressed proof | 136 |
| H5 claims with different emitted and solved CNF hashes | 45 |

The132 count therefore ALSO matches the fresh count of root IDs without
ledgers. Its occurrence in the separate historical restart lineage does not
prove the operator's count wrong. However neither132 nor136 is yet the
funded remaining-job count: four ledger-only outcomes are explicit stopped attempts,
all proof claims need current-CNF validation, and a missing direct root
proof may have a complete nested descendant cover. Likewise a local proof
file is not proof of durable remote publication or Lean consumption.

The four ledger-only roots are `h3_c1.cube-1-5`, `h3_c1.cube-1-6`,
`h3_c1.cube-1-7` and `h3_c2.cube-0-0`. Each records rc143 and
`reason=stopped-goal41-3-untrimmable-on-host`, with no LRAT; they are not
certified rows. Among roots, seven H3 and129 H5 lack a local compressed
proof. Nested descendant coverage remains a separate unresolved join.

Per-ID evidence is in the portable audit sidecar
`closure-inventory-evidence/small-high-root-metadata.json`.
It records readback UTC, all five hashes, ledger fields, local proof sizes
and explicit null current-stack acceptance. This stage reads metadata;
it does not replay or hash the large certificate payloads.

### Nested local coverage audit

The surviving `nested/nested_manifest.json` has SHA256
`7ca5dde323c5eb011cfc4c66fec9bc90d2332ed0fff611fa003bec4bf519b86f`.
Its136 parent IDs exactly equal the roots lacking direct local compressed
proofs. Its8,632 listed children have only eight local LRAT.gz files,
all negative covers (four left/four right), and no positive-cube proof files.
The pilot third-level manifest
`4fb05db998f8366f93b09507bf6046ae64b05cee4a20dc2682f169b1e922d8db`
lists16,896 children of256 nested parents: no local LRAT.gz files and nine
ledger files. No inspected missing root has a complete local descendant tree.

These historical split manifests descend from root hash86edc38a..., not
the approved05381a1c... root. Their large child counts are NOT a proposed
launch queue and must not be added to406 or136. Choose a reviewed split
per remaining root only after exact-CNF correspondence and cost are known.
Remote objects, alternate directories and final accepted coverage remain
unverified. Detailed local-only evidence is in the audit sidecar
`small-high-nested-metadata.json` beside the root metadata record.

For H7, `Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCapstone.lean`
provides `orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors`.
It consumes the19/15/7/2 indexed evidence values. Each may be direct or a
binary split tree, so the number of paid jobs must come from the actual
leaf manifest, not just the index cardinalities.

### H7 direct and adaptive evidence, 2026-09-10 readback

The tracked `sat49/h7-empty-cube-certified-receipts.tsv` has14 rows.
Sol3 verified each local compressed payload against its receipt (979,052,371
bytes total), and verified the compact base CNF SHA256
`8bc9b8f15b7f03194f39d208b2c0015e6039e0aac759ccfce0b6415724130eb0`
with17,633 variables and720,804 actual clauses. His recomputation of all43
parent CNF identities from the base plus21 unit clauses matches manifest
`e298e181f67e2f50d88fa61f71516cb86af31948e26413894bb3b147f51020c6`.
This is byte/input identity evidence, not new LRAT or Lean replay or S3
readback. The14 receipts remain candidates for reuse, not accepted closure.

Sol1 independently joined the receipt slots, parent manifest and adaptive
queue. The29 slots lacking direct receipts exactly equal the29 adaptive
parents, each with eight unique leaves:232 total. The adaptive queue hash is
`3af3c6b13648328f29f488e1143e194cdf8c608df461cab81c45f7d72cbcdedb`.
Missing direct slots by family are:

| Family | Indices without direct receipt |
|---|---|
| F6 | 2,5,8,14,15,16,17,18 |
| F7 | 0,2,3,4,5,6,8,9,10,11,13,14 |
| F8 | 0,1,2,3,4,5,6 |
| F9 | 0,1 |

Sol3's local terminal-marker census finds four SLOW-UNKNOWN markers, one
NONTERMINAL-FAIL and227 entries without a terminal marker. None establishes
accepted completion. These are historical disk records, not live-process
observations. The two inspected H8 followup queues fail the current validator
because required input paths are absent. Room37698/37813 identifies these
as pre-hardening queues; no current approved followup queue or successful
execution was established. Authenticate a followup decision separately for
each of the four slow leaves using its original parent/spec. Do not silently
reapply decisions to a sequentially mutated tree or count the old queues as
completed leaves. The232 count is an existing decomposition, not an approved
funded schedule or a bound on future splitting.

Portable evidence and hashes are in `closure-inventory-evidence/manifest.json`;
`h7-coverage-join.json` records the exact set join, and the `h7-*` peer records
retain their narrower scopes. None establishes final evidence assembly.

For H1, `Erdos85OneHighV2ResidualCertificateAggregation.lean` provides
`oneHighFamilyV2Checked_of_bank_append_residual` and its empty-residual
corollary. The exact bank/table coverage equality must be supplied. Counting
certificate-named source modules does not establish current-stack replay
coverage or equality with the producer's inventory.

## Reported lost tags and evidence boundary

Editor room report at05:01:53 names:

- 35958b08961b7cfc
- 3de5f9e7f1d255e7
- 59b38d317ba10da8
- be77d80a79a0dce6
- d67d8618bf933b97
- f25a68f489294d7c
- f363d5a068846aa3

Reported evidence: instance absent from describe-instances, last heartbeat
03:50Z and last worker-log line03:01Z; no user termination found in the
reported CloudTrail window. Spot reclamation is an inference, not a
verified cause. Instance disappearance alone does not establish that no
S3 copy, persistent volume or snapshot exists. Claude subsequently reports negative persistent-volume, snapshot and
bucket-wide certificate-copy searches (room42263, reiterated05:32:14Z).
This supports re-solve planning within the searched storage scope; the raw
probe records have not yet been copied into this portable snapshot.
Calendar date and timezone of those log timestamps must be attached to the
raw evidence before the final cost memo.

## Dated H1 producer snapshot and reconciliation boundary

Claude's `sat49/H1_PRODUCER_POSTDRAIN_PASS_SPEC.md` (bucket readback
2026-09-10 04:55–05:10Z) supersedes the earlier surviving-box counts:
13 UPLOAD-FAIL files, eight live slots at the05:01Z heartbeat, and ten
orphan-candidate claims attributed to the absent box. The editor is rescuing
the13 files and has queued in-region full SHA256 readback. A plan or upload
start is not a completed rescue; wait for its per-tag MATCH manifest.

The v3 snapshot reports1,698 jobs,667 claims,596 ledger records
(574 uploaded UNSAT plus22 UNKNOWN),53 failures (20 upload plus33 trim),
and18 claims without terminal records. It also reports12,020 objects under
`h1/`, while the later size census has12,050 objects. Different timestamps
and counting filters must be reconciled; neither object total by itself
proves unique accepted capacity coverage.

The spec's207 figure is the arithmetic remainder
`13351 - 12020 - (1031 + 20 + 33 + 22 + 18)`.
It is not yet an exact set of outside-v3 missing tags. Requested raw lists
must join canonical capacity identities to certificate keys and all v3
states, detect overlaps/stale keys and establish the complement explicitly.
Likewise the33 trim failures have unknown causes; absence of uploaded
`drat-trim.out` prevents an OOM diagnosis from being asserted.

Claude subsequently reported negative persistent-volume/snapshot and
bucket-copy probes for the seven vanished-box files; preserve those raw
findings before finalizing the recovery receipt. A stale heartbeat alone must
not authorize orphan-claim deletion: require authoritative terminal node or
process evidence. Eighteen slots and a free-RAM admission threshold do not
guarantee absence of OOM when individual jobs can subsequently grow to82GiB.
These points were returned to the producer-spec owner for correction.

### Exact H1 set reconciliation, pinned snapshot

`closure-inventory-evidence/reconcile_h1_snapshot.py` verifies every supplied
raw-list hash and derives tags from the24-entry sparse capacity tables using
the same serialization/hash rule as `h1fleet/capacity_queue.py`. It validates
the five capacity profile counts(1485,3617,4717,2693,839), rejects duplicate
tags and saves a per-capacity-row join with acceptance explicitly null.
The source snapshots were supplied by Claude at2026-09-10 05:32:14Z;
they are asynchronous observations, not a transactionally consistent live view.

| Exact metadata join | Count |
|---|---:|
| Unique capacity tags | 13,351 |
| Unique listed object tags, all inside capacity | 12,054 |
| Capacity tags without listed objects | 1,297 |
| Missing listed objects inside / outside v3 queue | 1,119 /178 |
| v3 queue tags with listed objects | 579 |
| Uploaded ledger tags without listed objects | 0 |
| Ledger/failure overlaps | 0 |
| Failure tags now having listed objects | 4 |

The1,119 missing v3 tags partition as1,031 never claimed,16 UPLOAD-FAIL,
33 TRIM-FAIL,22 UNKNOWN and17 claims without ledger/failure. Four failure
tags and one claim-without-line tag have objects in the later listing;
that explains579 listed v3 objects versus574 uploaded ledger records.
An object appearing after a failure is not by itself a verified rescue.
The178 outside-v3 tags are listed explicitly in `h1-exact-set-join.json`;
triage their host/v2 history before choosing solve/recovery actions.

All freight profiles match capacity, but1,635 of1,698 freight indices differ
from the current capacity-local ordinal. The freight worker emits from
`tables/$TAG.table` and profile, while its index is a ledger label. Thus this
index mismatch alone does not show wrong CNF emission; it does require
explicit reindexing by authenticated table/tag before capacity Lean replay.
The actual freight table payloads were not included in these raw lists and
have not been revalidated here. Do not pass freight ordinals to Lean as
capacity ordinals.

Historical `h1fleet/coverage/coverage.tsv` joins all178 outside-v3 tags to
`all_even_capacity`:177 were pending (eight host UNKNOWN,169 without a host
verdict). One, `e6f717d2e69cc8e0`, was historically listed certified-in-S3
with host UNSAT, but is absent from the newer object list. Its recorded CNF
hash is `81d900301a47adae1f0723dd27573434f21f6f535b2f032628c2ed2c6af373ea`.
A targeted remote/quarantine-history check was requested before re-solving;
the historical label does not establish present proof availability or validity.
The portable historical subset records source digest and filesystem timestamp.

The new join resolves the earlier207 arithmetic remainder to178 under the
newer object snapshot. It does not certify proof contents, establish current
slot liveness, or authorize deletion of claims or a paid launch.

## Replay sizing inputs, not a launch plan

For 12,020 certificates at983.6 seconds each, perfect load balance gives
410.52 / 205.26 / 102.63 hours at8 /16 /32 workers. These are baseline wall
times, not a completion SLA; add tail skew, downloads, failed attempts,
aggregation and startup. The exact number requiring replay must be audited
first. Producer solve time is separate from replay time. Historical peak
50.8 GiB on a64-GiB replay box means smaller boxes cannot be assumed safe.
The full13,351-row universe at the same pilot basis is3,647.79 box-hours,
or455.97 /227.99 /113.99 hours at8 /16 /32 workers before overhead.
Show this alongside the12,020 memo-certified subtotal: currently uncertified
rows will also need replay after production. Subtract only verified reusable
current-stack consumption, not certificates from incompatible historical runs.

The reviewed replay-spec revision (review1558,2026-09-10) adds a byte-weighted
case:13,350 new rows, pilot984 seconds and mean/pilot compressed-size ratio
about1.47 give about5,364 box-hours before overhead. Its32-worker on-demand
case is about8.75 days and$3,137 infrastructure. These are owner-model
estimates, not measured fleet throughput or total closure cost. S3 retrieval,
new olean storage, producer solving, H3/H5/H7 and final aggregation remain
separate. The source census reports12,050 objects, mean509,006,751 bytes,
median331,805,619, p993,113,003,601 and maximum5,217,826,271; metadata coverage
still needs its exact capacity join. Review1558 validates PLAN_ONLY shard
conservation and model arithmetic; it does not validate a launch or Lean
completion. The128-vCPU quota allows at most16 eight-vCPU workers before
other usage;32 workers require quota expansion and headroom.

## Replay engineering gates identified by its owner

codex-sol-2 reports that `AwsCliObjectStore.put_immutable` in
`replay_common.py` uses single-request `s3api put-object`, including for
`olean.zst`. Pilot8 does not establish that every output is below its size
limit. The fleet spec must either provide verified conditional multipart
publication or prove a safe output-size bound for every queued item.
Direct source readback confirms `h1fleet/replay_common.py` line717 uses
`put-object`; lines533 and543 call `source.read_bytes()` for the local
backend. The fleet owner pins this source to ac46eca9e4, unchanged from
7cbbe110b2. This verifies the identified implementation limitation, not
that conditional multipart publication is implemented.

The local backend loads whole artifacts into memory; the largest
local dry run must account for backend memory in addition to Lean/replay
memory. A successful small pilot is not a fleet-readiness certificate.

## Evidence still requested

1. Claude: dated durable-object ledger, producer heartbeat/log snapshots,
   unique certified/pending/quarantine/conflict joins, storage recovery check,
   and post-drain spec path with upload sizes and measured times.
2. codex-sol-2: shard queues/ownership/merge contract, local multi-job dry-run
   receipt, box/region choices and cost cases at8/16/32 workers.
3. sol-1: remote/current-CNF H3/H5 coverage, accepted H7 leaf and assembly
   status,178 outside-v3 H1 histories and current-stack consumed tags.
4. codex-sol-3: review this inventory for missing or double-counted obligations.

No erdosproblems.com posting; no Zenodo until the finite Theorem A is
unconditional, per the operator direction relayed in board37.
