# H3 triple-profile campaign plan

Status: **plan and deterministic metadata tooling prepared; no fleet launched**.
The cloud worker, artifact collector, fleet lifecycle and final Lean aggregation
are still implementation/readiness gates. `controller.py` is a read-only
capacity and queue planner, not an execution controller. This package supports
budget and architecture review; it is not yet a launch-ready campaign.

## Work unit and exact inventory

Use one complete `(branch, U-index, R-index)` as the first-pass claim unit.
The existing split pipeline retains a successful native certificate even if
its later consumer fails. It has four independently audited completed pairs:

| Branch/pair | Certificate wall minutes | Maximum RSS KiB |
| --- | ---: | ---: |
| Full U1/R15 | 97.400 | 8,337,112 |
| Full U3/R3 | 3.983 | 6,562,176 |
| Deficient U26/R2 | 3.207 | 6,549,052 |
| Deficient U369/R11 | 74.045 | 8,332,452 |

The final diagnostic Full U54/R20 is running separately. It must not be
claimed by a campaign worker while that run is live. Its future PASS needs
independent audit before reuse; a timeout stays unresolved.

The original verified reduced census is 261 full + 1,554 deficient = 1,815
pairs. `manifest.py` reconstructs the literal set formulas and representative
vectors from pinned source, checks the cardinalities, and emits `MANIFEST.json`
with a unique case ID, compact parameters, exact module names and source hashes
for every pair. The four audited computations are credited explicitly, leaving
1,811 pending computations, of which one is in flight. The current formal
connections Full260 + Deficient1552 still expose 1,812 hypotheses: the U3/R3
computation has passed but its further full-census connection is prepared,
not compiled. Keep compute credit and formal aggregation status distinct.

`MANIFEST.json` SHA-256 at preparation:
`11ded9568ddc0497b8fd58d9107bc35f50caca0fd9064e9f85db18f98f614445`.
It also pins transitive project proof sources, all research census sources,
Lean/Lake configuration, immutable prerequisite receipts, and the generator.
The actual launch additionally pins a source commit, container image digest,
cache-freight inventory and collector/worker code hashes. No mutable branch
name alone is an execution pin.

Whole-pair units are the established starting point. First-column branching
has one measured native branch and structural inventory checks, but no
representative performance comparison or complete remaining-pair branch
campaign. Keep it as a separately validated residual strategy after actual
whole-pair timeouts. Do not sum branch receipts without a compiled complete
branch-cover theorem; never infer rejection from exhausted time or memory.

## Per-pair module contract

`common.py` deterministically emits four sources; emission runs no search:

1. Inputs defines U from its exact compact code and R from its representative.
2. Membership imports the matching full/deficient census and proves census
   membership and U identity using standard axioms, before any native search.
3. Certificate checks `threeHighNativePairSearch U R = false` with native_decide.
4. Consumer imports Membership and Certificate, proves rejection at the actual
   census representative, and excludes its distinct joint witness.

The two census roots both contain `Pruning`; they require separate import
paths. Inputs/Certificate are library targets under `Proofs`; Membership and
Consumer use direct Lean invocation with their branch's audited census objects.
Consumers must keep `threeHighCrossDomain` locally irreducible, as in the
verified diagnostic pipeline. The newly emitted campaign namespace and added
consumer bridge have not yet had a cloud canary; successful diagnostic modules
are evidence for the underlying pipeline, not for these new source bytes.

Generate a source bundle for review, without Lean:

```sh
python3 -B manifest.py --emit-case full-u003-r03 --output /tmp/h3-case-review
```

The output must be fresh. A worker must regenerate and compare every byte's
hash to the frozen manifest before building. Prior credits keep their original
names and receipts; do not rerun or relabel them to fit campaign namespaces.
See `RECEIPT.md` for the required artifacts, trust sets, failure states and
independent acceptance rules.

## Resource and controller design

Start with 16 GiB hard memory per active Docker job, a hard two-vCPU limit,
`LEAN_NUM_THREADS=1`, one Lake thread and a two-hour pair wall cap. The observed
6.2–8.0 GiB process RSS is not an aggregate-memory bound. A container hard limit
and node reservation are both required. On a node with 123 GiB actual usable
memory and 16 vCPUs, reserve 12 GiB for the OS/shared tooling and cap at six
active slots. Use actual MemTotal, not advertised capacity. A smaller node
must pass the same fit calculation. Reserve before claiming; no in-job memory
escalation or automatic retry.

Each slot uses a separate checkout/build volume and unique attempt directory.
Share only immutable packages and audited cache freight; copy/reflink into a
slot-local writable cache. Never let two workers write the same generated
Proofs directory or Lean build cache. Capture Git/source provenance on the
host before Docker, because a worktree's external Git directory may not be
mounted in the container. Seed all audited prerequisite objects and verify
source/object/toolchain hashes before trusting the cache.

The execution controller should follow this protocol:

1. Freeze manifest, source/image/toolchain/cache pins and approved resource,
   region, node-count, lifetime and total-cost limits. Validate solver-free
   bootstrap, single-worker canary and limited concurrent canary first.
2. Use conditional immutable claims on `(manifest hash, case ID)` with a unique
   attempt ID. Record owner/slot, limits and heartbeat. Lease expiry alone
   never authorizes reclaim; verify node/container/job termination first.
3. Reserve a full bounded attempt against the remaining approved budget before
   launch. Release unused reservation after authoritative terminal metrics.
   Budget units must distinguish node-hours, slot-hours and consumed CPU-hours.
4. Check STOP before every new claim and between build stages. A running native
   stage drains only until its existing cap; an operator kill remains a partial
   attempt. On interruption, retain any completed certificate object and its
   evidence; later continuation revalidates it and runs only missing stages.
5. Upload attempt-unique artifacts atomically and preserve partial diagnostics.
   Independent collector acceptance, not worker exit alone, marks completion.
   Release claims only after terminal evidence; unresolved observations remain
   UNKNOWN. Never overwrite a successful attempt with a retry.
6. Keep TIMEOUT/OOM/ERROR/UNKNOWN residuals explicit. No larger heap, longer cap,
   first-column split or extra node is implied by the initial pass. A reviewed
   residual plan controls any second pass.

Before a real launch, implement and cloud-test these state transitions with
wrong source/image pins, must-fail proof, killed worker, duplicate claim,
partial upload, consumer-only continuation, budget exhaustion and STOP tests.
This plan intentionally creates no IAM role, bucket object or instance.

The implemented planner checks manifest hashes/counts, excludes caller-specified
live IDs, enforces the capacity fit, and emits a deterministic pending queue:

```sh
python3 -B controller.py --manifest MANIFEST.json \
  --manifest-sha256 11ded9568ddc0497b8fd58d9107bc35f50caca0fd9064e9f85db18f98f614445 \
  --memory-gib 123 --vcpus 16 --nodes 1 --in-flight full-u054-r20
```

## Budget scenarios, not a forecast

Four deliberately varied completed cases cannot establish a bimodal population
or a statistically supported mean. The 1,000–2,500 CPU-hour planning range is
an assumption to discuss, not a measured forecast or completion guarantee.
`controller-plan.json` gives illustrative 4-minute/90-minute mixtures for the
1,810 currently unclaimed computations:

| Assumed fraction at 90 minutes | Ideal slot-hours | Ideal node-hours, six slots | Ideal billed vCPU-hours, 16 vCPUs |
| --- | ---: | ---: | ---: |
| 0% | 120.67 | 20.11 | 321.78 |
| 25% | 769.25 | 128.21 | 2,051.33 |
| 50% | 1,417.83 | 236.31 | 3,780.89 |
| 75% | 2,066.42 | 344.40 | 5,510.44 |
| 100% | 2,715.00 | 452.50 | 7,240.00 |

These assume perfect packing and no startup, dependency, audit, transfer,
interruption or retry overhead. Slot-hours are occupied compiler wall time,
not automatically consumed CPU-hours. Multiple nodes shorten ideal wall time,
not this total resource use. Memory limits concurrency, so billing every node
vCPU can substantially exceed the sum of compiler CPU times.

At the initial two-hour cap, the 1,810 unclaimed attempts reserve at most 3,620
slot-hours of execution, still without promising any rejection success. With
six slots per node, last-wave rounding gives 604 ideal node-hours on one node;
bootstrapping, artifacts and node idle time require their own lifetime/budget
limits. Use a current region-specific spot quote and explicit dollar/node-hour
ceiling in Robb's combined request; this package provides no price quote or
spending authorization. H7's separately measured/estimated resource budget must
be added, not hidden inside this H3 estimate.

## Final proof and readiness gates

Receipt collection must cover the exact full and deficient ID sets with no
missing/duplicate-substituted cases. Generate per-U aggregation shards binding
each accepted certificate to the pinned representative, compile those shards,
and compile the final full/deficient rejection hypotheses against the existing
actual-graph witness theorems. Audit the resulting exact union of native axioms.
A native_decide receipt remains native-backed; do not describe it as a
standard-axiom-only or external CakeML certificate. H3 pair profile t=0 is a
separate lane and is not covered by this triple-profile campaign.

Outstanding: final diagnostic audit and manifest re-freeze; campaign source
canary; executable worker/collector/fleet controller with tested recovery;
budget approval; execution; independent receipts; final Lean aggregation.

## Source bridge canary

`canary.py` prepares a bounded cloud check for Full U3/R3 and deficient U26/R2.
It compiles the exact generated Inputs, Membership and Consumer source bytes.
For Certificate only, it substitutes an explicit proof from the corresponding
old, independently audited certificate. The production native_decide source
hash and the substituted source hash are both recorded. This avoids repeating
an already verified native search while testing the new representative bridge.

All resulting objects go into a private complete copy of the Lean library,
with branch-specific census import paths. The original cache cannot acquire
substituted campaign certificate objects. Only the three generic dependency
modules are Lake targets; prior native certificates are imported as hash-checked
objects. A successful status is `BRIDGE_CANARY_PASS`, never a production PASS.
It cannot count as a new campaign rejection or test the production native
search/controller/collector lifecycle. An independent artifact audit follows.

The canary remains uncompiled until its separately recorded cloud job passes.
Local Python syntax/import and host-execution-refusal checks pass.

The first bridge canary exited 1 at 07:06:40 UTC. Its complete source/log/run
failure evidence is retained in `canary-first-failure/`, at execution commit
`c47efaa6ffb003b4dc665bfbd3a887d93c51730f`. The full branch passed all four
stages; deficient Membership lacked the import defining
`DeficientUNormalizedAssembly.representative`, so the compiler reported an
unknown identifier and sorryAx. Those failed exports are not accepted evidence.
The generator now imports the already verified `Deficient1554` module, which
imports both Assembly and Pruning. This changes deficient membership source
hashes and the frozen manifest hash; the old manifest remains in the original
Git commit and its hash is recorded with the failed run. A fresh canary must
verify this correction before source readiness is claimed.
