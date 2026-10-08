# H3 triple-profile campaign plan

Status: **plan and deterministic metadata tooling prepared; no fleet launched**.
The single-attempt worker has passed full and deficient non-native preflights,
but has not run a production case.
The complete artifact collector, fleet lifecycle and final Lean aggregation
remain implementation/readiness gates. The read-only artifact
validation component and preflight host execution/provenance audit are implemented
and exercised; production acceptance remains pending. `controller.py` is a read-only
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

The final diagnostic Full U54/R20 reached its two-hour job cap and exited 124.
Its independently audited timeout evidence is in
`../h3_varied_pilot_20261008/FullU54R20-timeout-evidence/`. No Certificate or
Consumer object was produced. It stays unresolved and excluded by the current
preflight launcher; this timeout does not authorize a retry or grant credit.

The original verified reduced census is 261 full + 1,554 deficient = 1,815
pairs. `manifest.py` reconstructs the literal set formulas and representative
vectors from pinned source, checks the cardinalities, and emits `MANIFEST.json`
with a unique case ID, compact parameters, exact module names and source hashes
for every pair. The four audited computations are credited explicitly, leaving
1,811 pending computations, including the timed-out diagnostic. No triple
diagnostic remains in flight. The current formal connections Full259 +
Deficient1552 expose 1,811 hypotheses. The U3/R3 computation is now consumed
by the compiled and independently audited Full259 reduction (evidence in
`../h3_full_diagnostic_reduction_20261008/full259-evidence/`, RUN
`a0816150ca3127f6500f2caa6132bc6740f97946a42416d48513cef04c65409f`).
This composition creates no new computation credit; Full258 remains blocked
on the unresolved U54/R20 certificate.

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
verified diagnostic pipeline. The newly emitted campaign namespace and added consumer bridge passed a
two-case cloud canary after a deficient import correction. That canary reused
old native certificates explicitly; it validates the new source bridge for
those two cases, not the production native worker or all 1,815 generated cases.

Generate a source bundle for review, without Lean:

```sh
python3 -B manifest.py --emit-case full-u003-r03 --output /tmp/h3-case-review
```

The output must be fresh. A worker must regenerate and compare every byte's
hash to the frozen manifest before building. Prior credits keep their original
names and receipts; do not rerun or relabel them to fit campaign namespaces.
See `RECEIPT.md` for the required artifacts, trust sets, failure states and
independent acceptance rules.

`validate_artifacts.py` checks retained production source/object/log bundles
against an externally pinned manifest and exact commands, independently parses
the raw axiom reports, and rejects incomplete inventories and substituted bridge
proofs. Its certificate-only mode preserves a verified artifact prefix after
Consumer fails. Neither mode grants campaign credit or permits a retry; a host
collector must establish execution, immutable dependencies, limits and terminal
state. Seventeen synthetic metadata tests in `test_artifacts.py` exercise rejection
and recovery cases without Lean, Docker, native search or cloud calls. Their
opaque test objects are explicitly synthetic, not compilation evidence.

`worker.py` consumes an externally pinned launch record and complete cache
inventory, enforces the actual Docker cgroup memory/CPU limits, and runs four
direct Lean compiler processes in production mode. Its separate preflight mode
stops after Inputs and Membership and emits a distinct non-native receipt that
cannot pass rejection validation. It creates a fresh attempt directory,
copies the complete library into private storage, verifies the copy, and refuses
pre-existing campaign objects. Native certificates are copied into the retained
case bundle immediately after compilation. STOP is checked before starting an
attempt and between stages; the attempt deadline kills and reaps the active
compiler process group. A non-timeout certificate failure is an `ALARM` pending
raw diagnostic review. There is no automatic retry, resizing, claim release,
fleet launch, or acceptance as `AUDITED_PASS`.

The launch schema and cache contract are in `RECEIPT.md`. Forty-nine metadata tests
pass across worker, artifact, inventory and container-audit suites, including
preflight/production separation. `test_worker_runtime.py` is a separate
cloud-host-only check of subprocess completion, nonzero exit, timeout cleanup
and refusal to overwrite retained logs. Cache staging, Docker mount/image
verification and host collection have passed for the two preflights below.
Production native compilation, production host acceptance, consumer-only
continuation and fleet recovery remain untested or unimplemented gates. Do not
use the worker for a campaign until those gates and the limited production
canary are complete.

The four cloud process tests passed in 1.211 seconds in job
`20261008T072956-erdos85__h3-triple-formal-20261007-298258`, at execution commit
`9e80ddc38aaa2eef9a13fc834e96b3c4bbb432ee`. Independent host inspection confirmed
exit zero and source equality to that commit. `worker-runtime-evidence/` retains
the exact tested scripts, raw job log, spec, exit and audit hashes. This tests
the subprocess runner, including descendant cleanup, not production Lean.
The later import-path correction keeps full final census objects before the
base objects, matching the bridge canary; a metadata regression checks both
branches. The tested subprocess function is unchanged, checked by AST equality.

## Container environment probe

`probe_container.py` was run once on the existing builder, using the immutable
image `sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`.
Job `20261008T074307-erdos85__h3-triple-formal-20261007-307377` ran at
`653a7d59de8e73fab45a21dda04912b9b5428a22` and exited zero. Lake environment
setup and `lean --version` succeeded with the repository, existing build volume,
package volume and image root mounted read-only. The probe used a hard 2 GiB
memory limit, zero swap, two CPUs, no network, and a 45-second container cap.
It performed no proof build or native search.

`audit_probe.py` independently checked the raw pre-start and terminal Docker
inspections, image/command/environment identity, exact resource settings,
read-only mounts, in-container cgroup observations, toolchain/config hashes,
terminal exit zero, no OOM, no restart and removal of the probe container. Its
read-only cloud audit passed. `container-probe-evidence/` retains the raw records
and hashes. Eight mutation tests cover wrong identity/image/command/environment,
changed limits or mounts, nonterminal/nonzero/OOM states and restart/wall overruns.

Two auditor compatibility corrections were needed, without rerunning the probe:
this daemon serializes the default `OomKillDisable` value as false before start
and null after exit (true remains rejected); its nanosecond timestamps need
sub-microsecond truncation for the builder's Python parser. The actual Lake
search path includes the pinned toolchain's standard library after project
objects, and that exact suffix is checked.

This establishes the container environment setup. It does not approve arbitrary
cache contents or validate a production worker attempt. Cache preparation and
bounded worker preflights are separately audited below. The limited production
canary remains open. The host launcher gives only the fresh attempt output a
writable mount while keeping the verified inputs read-only.

`prepare_cache.py` rechecks both audited census bundles and the frozen source
manifest, builds only the three generic dependency targets, and copies the
complete library into a fresh private snapshot. It compares the source cache
before/after copying, verifies every copied file, and writes separate full and
deficient cache inventories. Its result is `CACHE_PREPARED`; independent host
audit is required before the worker uses either inventory.

The first preparation and independent artifact audit passed. Job
`20261008T075504-erdos85__h3-triple-formal-20261007-314442` ran at
`3080636e2d0897e29a2f24eb723ed762db018e2a`, with 16 GiB, one Lake thread and a
15-minute outer cap. The preparation wrapper's CPU limit was 16; this was not
the two-CPU production worker. Its only build targets were the three generic
dependency modules, completed in 6.42 seconds. Snapshotting used a separate
complete library directory and no native certificate search was requested.

`audit_cache.py` verified the terminal exit, execution source hashes, commands,
logs, previous census evidence and actual retained file inventories independently
of the worker's inventory walk. It checked 2,471 library files, 430 full-base
files, 1,370 final-full files and 610 deficient-base files. Evidence is in
`cache-preparation-evidence/`; the cache objects remain on the cloud. Full
inventory SHA-256 is
`0bdeec182744aa0737982d109290613eece8ac2f3c0115fa1307ddb76dd1d735`, and deficient
inventory SHA-256 is
`3397a58699851e910c33ad8d3e5ca099de3e2665dc151cc000de934450a29c9a`.
This uses the established builder/toolchain cache and audited census objects;
it is not a clean rebuild of Mathlib or new rejection credit.

## Bounded worker preflights

`launch_preflight.py` runs one preflight on the existing builder with a hard
16 GiB memory limit, no swap, a hard two-CPU quota, no network, one Lean thread,
a 600-second worker deadline and a 660-second container deadline. The repository,
build/packages volumes and image root are read-only; only the fresh output is
writable. It retains pre-start and terminal Docker inspections and logs before
removing its uniquely named container. It has no production or fleet mode.

Both first attempts passed, with no retries:

| Case | Producer job suffix | Execution commit | Container seconds | Inputs / Membership seconds | Peak compiler RSS KiB |
|---|---|---|---:|---:|---:|
| `full-u001-r16` | `20261008T081422-…-328527` | `f8f011a45170d289dca8cbb17f6946420cbbae00` | 16.720 | 3.905 / 5.608 | 6,897,840 |
| `deficient-u000-r02` | `20261008T081938-…-334858` | `1895b057bec3b5a7d4b8e5594795de821df5e885` | 33.688 | 3.805 / 22.930 | 8,079,692 |

`audit_preflight.py` independently checked the actual retained sources, objects,
logs, receipts and complete cache inventories, the execution commit's source
closure, the approved image and launch command, exact mounts and cgroups,
terminal exit zero, no OOM/restart, wall limits and container removal. Audit jobs
`20261008T081830-…-332954` and `20261008T082035-…-335743` both exited zero at
`1895b057bec3b5a7d4b8e5594795de821df5e885`. Each Membership module exported
`member` and `input_identity` with exactly `propext`, `Classical.choice` and
`Quot.sound`. Inputs modules are data-only and emitted no axiom reports.

`worker-preflight-full-evidence/` and `worker-preflight-deficient-evidence/`
retain raw job/audit logs, Docker records, launch/cache inventories, generated
sources and per-stage receipts. Lean objects and private libraries stay on the
cloud at the corresponding `_build/worker-preflight-<branch>-first` paths.
The RUN hashes are respectively
`527d1492ac71e7a136a1fbac784e12eab976352c7b1bbd715634e0839583d0cd` and
`ca7c920dcc97745e7929b75e09c9120ecdf221a6a65313f609c0fe9c81b7d56c`.
Six mutation tests use retained real Docker observations, and three launcher
tests check scope, mounts and refusal to run locally.

These runs compile only Inputs and Membership. Generated Certificate and
Consumer sources were retained but not compiled. No native certificate search,
new exclusion, campaign credit, concurrent campaign or clean Mathlib rebuild
is established by these preflights.

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
live IDs, enforces the capacity fit, and emits a deterministic pending queue.
The following is the historical snapshot while Full U54/R20 was live; that
diagnostic has since timed out. Planner output never grants retry permission:

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

Outstanding: a reviewed disposition for the timed-out diagnostic; production native
worker canary; production collector/fleet controller with tested recovery;
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

The corrected canary now passes its separately recorded cloud job and
independent audit. Local Python syntax/import and host-execution-refusal
checks also pass.

The first bridge canary exited 1 at 07:06:40 UTC. Its complete source/log/run
failure evidence is retained in `canary-first-failure/`, at execution commit
`c47efaa6ffb003b4dc665bfbd3a887d93c51730f`. The full branch passed all four
stages; deficient Membership lacked the import defining
`DeficientUNormalizedAssembly.representative`, so the compiler reported an
unknown identifier and sorryAx. Those failed exports are not accepted evidence.
The generator now imports the already verified `Deficient1554` module, which
imports both Assembly and Pruning. This changes deficient membership source
hashes and the frozen manifest hash; the old manifest remains in the original
Git commit and its hash is recorded with the failed run. The fresh second canary verified this correction.

The corrected job `20261008T071036-erdos85__h3-triple-formal-20261007-286861`
exited zero at 07:11:47 UTC, at source
`bd40e23c8a2dbc0231a0b3cc7af29c89a56905d4`. All eight modules and ten exact
axiom reports passed independent cloud-host audit with `audit_canary.py`.
The Membership reports use standard axioms only; the two substituted
Certificates and their Consumers use exactly the corresponding old pilot
native axiom plus standard axioms. The audit also confirmed no campaign
Input/Certificate objects existed in the shared library cache. The artifacts
and audit are retained in `canary-evidence/`; objects stay on the cloud.
RUN SHA-256: `420fe58eddf04363b5f57745376f3e2544afecbb4a64bea900aafeda41e7b874`.
This is source-bridge readiness for the two tested cases, not a production
campaign receipt, a new native rejection, or a full-campaign execution test.
