# H3 triple-cell completion engine

The conditional engine, bridge and split theorem compile with only
`propext`, `Classical.choice` and `Quot.sound`. This does not yet exclude the
triple cell: successful search results remain explicit premises.

Source commit: `8484794c2a96f41f6aee799c193a56c47bf8e292`.
Cloud build: `20261008T101350-erdos85__h3-triple-formal-20261007-402758`, exit 0.
Engine, Bridge and Split were freshly built in 9.7, 5.1 and 3.9 seconds.
`conditional-build/AUDIT.json` binds their exact sources, objects and four
axiom reports to the successful job. The read-only auditor checked the
objects twice, including modification times within the job interval.
Raw log/spec/exit and exact source snapshots are retained alongside it.

## Adaptation

The source is adapted from the completed pair engine at
`dc7f78d47d7017dcb8da5cc4aa200f1432a0f5df`. Namespace and module names are
separate. The support layout changes to the actual canonical representative
`threeHighRepresentativeMasks 1`: vertex 3 has mask 7; singleton supports
are 4–10, 11–17 and 18–24; empty supports are 25–48. Each colour fibre still
has eight vertices. All range guards and their supporting lemmas use the
new boundary 25. The rest of the search and soundness argument is unchanged.

The bridge proves the mask/colour equality directly with `decide +kernel`,
then derives an engine model and compatibility from the existing relation
constraints. `threeHighCanonicalGraphCover_one` transports representative
exclusion to `OrderFortyNineTripleCellExcluded 3 1`.

The unsplit interface is `tripleSearch = true`; the split interface requires
`0 < m` and every `triplePart m r = true` for `r < m`. Fuels are 70/30/40.
Fuel exhaustion and a completed candidate return false, so false alone is
not a satisfiability certificate. Neither hash injectivity nor balanced
parts is required by the composition theorem.

## Bounded diagnostic

`Probe384R0.lean` requests just `triplePart 384 0 = true` via `native_decide`.
It is outside the library's automatic module glob. `run_probe.py` stages it
under the Lean project root, checks the three prerequisite source/object
hashes, and limits its Lean process group to 300 seconds. Only the existing
cloud builder was used.

The diagnostic **timed out without a certificate**. Job
`20261008T101712-erdos85__h3-triple-formal-20261007-405471` ran at
`0be06607d7d5e176fa0c8f3abf040d191d4447ee`; its Lean child was killed and
reaped at 300.221 elapsed seconds, with 298.868 user seconds, 1.340 system
seconds and maximum RSS 6,451,688 KiB. Its compiler log is empty and no
`Probe384R0.olean` exists. The result remains unresolved.

The runner exits 124 after its five-minute timeout. The existing Docker
wrapper maps that to job exit 1 and prints its outer limit, “6m”, in the
timeout banner. That banner is not a six-minute runtime measurement.
`probe-evidence/` retains both layers' raw evidence and the read-only audit.
The audit verifies execution/source identity, absent certificate, removal of
the staged source, and unchanged prerequisite objects. The container and Lean
process were also observed absent after termination.

`probe-container-live.json` records the actual pinned image
`sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`,
16 GiB hard memory limit, and two-CPU cgroup quota. The launch applied CPU
affinity `0,1` to `e85-host`, so its `nproc`-derived Docker quota was two.

This one censored sample does not estimate the whole route's cost or establish
that it improves on the census. No full campaign is authorized or launched by
this experiment, and the prior census route is unchanged.

## Phase-one-only follow-up

`PhaseOneOnly.lean` establishes `dfs1 (fun _ => true) 70 s0 = true` by
`native_decide`: every phase-one leaf is accepted without running phase two or
three. This is a traversal diagnostic and cannot imply graph exclusion.

Job `20261008T102436-erdos85__h3-triple-formal-20261007-410562`, execution
`94aab7d1b8baacb6e5b3c65c6ea319b65ebe89f6`, exited zero under a 60-second
inner cap. The compiler process finished in 4.970 seconds, including imports
and Lean startup, with 3.648 user seconds and 1.299 system seconds. Maximum RSS
was 6,485,932 KiB. The object hash is
`5f43898b6c353e3ed38c2c6c5d3006e85e212739b7d302c3a2672ba732076150`.
The theorem uses `propext`, `Quot.sound`, and its own
`phaseOneTraversal._native.native_decide.ax_1_1`; it is not standard-axiom-only.

`phase-one-evidence/` retains the exact source, runner, raw job records, inner
receipt, compiler log and read-only audit. The audit checks execution/source
identity, actual object hash, exact axiom set, unchanged prerequisite objects
and removal of the staged source. The job spec requests 16 GiB/two CPUs; no
live Docker inspection was captured for this short job. No isolation from
other workloads on this shared builder was enforced.

The result shows that the basic phase-one traversal can finish well within the
earlier cap. It suggests the expensive work is elsewhere, but the constant
callback also omits per-leaf hashing: this measurement alone does not isolate
hashing from phase-two/three search or measure bucket balance.

## Phase-two-only follow-up

`PhaseTwoOnly.lean` keeps the original phase-one hash selection for bucket
384/0 and runs phase two with a constant-true leaf in place of phase three.
It requests a traversal result, not a graph exclusion.

Job `20261008T102949-erdos85__h3-triple-formal-20261007-414392` at
`a56fefc7a97fa279ae49f13b31bed1e9a0a25a1f` timed out at 60.207 seconds
(58.973 user, 1.230 system), maximum RSS 6,452,552 KiB. No object was produced;
the compiler log is empty. The inner runner killed and reaped Lean, exited
124, and the outer Docker wrapper recorded exit 1 with its two-minute-limit
banner. Exact source, raw records and the read-only audit are retained in
`phase-two-evidence/`. The audit checks that the prerequisite objects did
not change. The job spec requests 16 GiB/two CPUs; no live container snapshot
was captured for this job.

This rules out attributing all expensive work to phase three. It does not yet
distinguish callback hashing from phase-two branching. No pruning change or
new exclusion attempt was made on this measurement alone.

## Phase-one counts and hashing

The instrumented traversal `PhaseOneProfile.lean` follows the same clause
choice, low-vertex/open-clause guards, twin skipping and edge-insertion
branches as `dfs1`. At each leaf it computes the existing `stKey` and increments
one of 384 counters. It records fuel exhaustion and invalid guards separately.
This is profiling code, not a proved counting theorem or an exclusion result.

The first helper failed to parse a multiline record update, before evaluation.
`profile-evidence/` preserves that failed compilation at `4ac20ada301` in job
`20261008T103524-erdos85__h3-triple-formal-20261007-417821`; no counts or
certificate are accepted from it. The compiler's subsequent `#eval` refusal
mentions `sorry` because elaboration had failed, not because an accepted
search result was obtained.

After the syntax fix, job
`20261008T103658-erdos85__h3-triple-formal-20261007-419075` at
`16bc832cef47affb671b7fc225d88f0ff521fc59` exited zero in 4.870 seconds
(3.647 user, 1.189 system), including Lean startup. Maximum RSS was
6,497,672 KiB. The one-minute cap did not fire. The output reports:

- 8,167 phase-one nodes and 1,088 leaves;
- zero fuel-exhausted or invalid-guard states;
- four leaves in bucket 0 of 384;
- bucket sizes ranging from zero to eleven, summing to 1,088.

`profile-fixed-evidence/` retains the exact helper and runner, raw records,
receipt and audit. The read-only audit checks source/commit identity, the
nonempty compiler object, unchanged prerequisite objects, complete counter
output, 384 nonnegative integer buckets, their sum and zero failure counters.
The spec requests 16 GiB/two CPUs; no live container snapshot was captured.

This measurement includes hashing and points to phase-two branching as the
dominant unresolved cost in the earlier diagnostic. The helper's timing is
not a formal lower/upper bound on the uninstrumented search. Four leaves in
bucket 0 do not imply that other buckets have equal runtime; no campaign cost
is extrapolated. These partial-graph leaves also are not the old census's
1,811 outstanding pairs and grant no credit to that census.

## Early degree-capacity gate: prototype result

The C sizing prototype from H5 commit
`6e85c306db71d4080850edfc4ef5436544cc2997` was adapted to the canonical H3/T1
layout in `h3_phase2_profile.c`. Phase three is omitted. The proposed gate
checks during phase two whether an empty vertex can still attain degree seven
using its current neighbours and all presently admissible candidate edges.
Its mathematical justification would be the existing `count_gate` argument.

Before comparison, the control reproduced the Lean profile's 8,167 phase-one
nodes, 1,088 leaves and every one of the 384 bucket counts, with the exact
canonical masks. This is an implementation cross-check, not a formal proof
that the C and Lean programs are equivalent. The prototype pre-generates only
colour-consistent patterns and stores their distinct vertices as sets; it has
344 patterns, whereas Lean starts with all 512 triples and filters at runtime.

Job `20261008T104402-erdos85__h3-triple-formal-20261007-423339` at
`e7a5c8ae2dcf2eb0726ab84f1f3937fbc5ee732a` exited zero after recording the
control and both capped comparisons. Each comparison selected bucket 0 with
first-open-clause ordering and no phase-one forward checking. Child programs
had a two-million-node cap, a 20-second internal wall check, 30-second outer
wall/CPU limits, two-GiB address-space limits and affinity to CPUs 0–1.
The runs used the existing shared cloud host, not Docker.

| Variant | Wrapper wall seconds | Phase-two nodes | Gate hits | Result |
| --- | ---: | ---: | ---: | --- |
| Baseline | 0.566 | 1,992,343 | 0 | Node cap |
| Early gate | 4.771 | 1,992,343 | 2,407 | Node cap |

Both reached 7,657 phase-one nodes, making the total two million. Their fourth
selected leaf was interrupted, so neither completes the bucket. The prototype
returns 124 with `stopped=1`; its `traversal_return=1` is not a successful
complete traversal or an exclusion claim.

For the two completed nontrivial leaves, phase-two nodes fell only from
291,381 to 291,262 and from 1,574,657 to 1,574,586; their combined C time
grew roughly ninefold. That is insufficient benefit on this sample to justify
formalizing the gate. No Lean engine change was made.

`prototype-evidence/` retains the source, runner, compiler/control/comparison
logs, job records, receipt and read-only audit. The audit checks the source
against the execution commit, actual binary hash, raw counters and caps, and
the full control bucket vector against the retained Lean profile. This records
prototype performance only, with no graph-exclusion credit or campaign estimate.

## Deficit-aware vertex ordering: fixed-prefix comparison

Job `20261008T105313-erdos85__h3-triple-formal-20261007-428217` at
`51e224ef95c0122e87993ff0a56617795db6cd3a` compared four phase-two orderings
in `h3_phase2_heuristics.c`. It changes only the next deficient core vertex:
minimum candidate count (baseline), minimum count minus deficit, minimum
count/deficit ratio (integer cross multiplication), or minimum binomial
choice count. All ties retain the earliest vertex. The phase-one control
again matched all 384 Lean bucket counts.

Each comparison completed the first three selected states in bucket zero,
with keys 975744, 986112 and 41088 at phase-one positions 1393, 6289 and 6321.
Each then stopped before processing the fourth state, with explicit
`stop_reason=leaf-prefix`, `leafrun=3`, exit 124 and no outer timeout.
The node/time/address-space/CPU limits match the preceding experiment.

| Ordering | Phase-two nodes | Phase-two leaves | Wrapper wall seconds |
| --- | ---: | ---: | ---: |
| Candidate count | 1,866,055 | 17,312 | 0.515 |
| Count minus deficit | 836,990 | 17,312 | 0.265 |
| Count/deficit ratio | 395,699 | 17,312 | 0.165 |
| Binomial count | 1,662,297 | 17,312 | 0.616 |

The ratio ordering reduced nodes by about 79% on this sample. These are
single short runs on a shared builder, not a stable timing benchmark or an
estimate for all buckets. Matching terminal-state counts do not establish
formal equivalence. Phase three remains omitted; no graph exclusion follows.
The result justifies trying the ratio ordering in the sound Lean engine.

`heuristic-evidence/` preserves the source, runner and imported helper, raw
logs and receipts, plus a read-only audit of the execution pin, file and
binary hashes, counters, state sequence, stop reasons and control vector.

The Lean ratio ordering was implemented at
`e899840b71d004c63daaf9f83bec9bffa255a4a0`. Job
`20261008T105436-erdos85__h3-triple-formal-20261007-429055` rebuilt Engine,
Bridge and Split successfully (11s, 4.0s and 3.8s respectively). The existing
soundness proof required no change: phase-two vertex guards validate the
chosen vertex, independent of the ordering. All four audited exports retain
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`.
`ratio-build/` and its capture/audit scripts retain fresh-object provenance
and the exact source/log records. Earlier evidence remains pinned to its
original engine and is not evidence of this version's runtime.

`run_phase_two_ratio.py` repeats the existing one-minute phase-two-only
bucket-zero diagnostic with the newly audited prerequisite hashes. It still
accepts all phase-two leaves and therefore cannot establish graph exclusion.

The ratio diagnostic ran at `bab58460183e3512014f7413d850678e4fbb33e1`
in job `20261008T105548-erdos85__h3-triple-formal-20261007-430342` and
still timed out: 60.211 seconds elapsed, 58.946 user, 1.260 system, maximum
RSS 6,452,544 KiB. The inner runner killed and reaped Lean, retained an empty
compiler log and produced no object. The wrapper maps this to exit 1 and
prints its outer two-minute limit; that banner is not the measured duration.
`phase-two-ratio-evidence/` retains the read-only audit, source, runner,
receipt and raw job/compiler logs. All prerequisite object hashes remained
unchanged. This result does not measure a complete-bucket speedup in Lean;
more targeted instrumentation is needed before increasing search scope.

## Bounded phase-two Lean profile

`PhaseTwoProfile.lean` collects the four bucket-zero phase-one states and
mirrors phase two with a 10,000-node limit for each state. It uses the engine's
state check, candidate filter, ratio picker, fresh-vertex selection, insertion
and pattern-ban order. It records invalid states and fuel exhaustion; it is
instrumentation, without a proved equivalence or exclusion theorem.

The first compilation at `6bc0161345d6c92c5b9378a8f69a650368ddfb24`, job
`20261008T105909-erdos85__h3-triple-formal-20261007-432793`, failed because
the timing block inferred `BaseIO` while printing requires `IO`. It produced
no accepted profile. `phase-two-profile-evidence/` preserves that failure.

After adding the explicit `IO Unit` type, job
`20261008T110003-erdos85__h3-triple-formal-20261007-433844` at
`47ccc586fd33cf86c51304eb1cda39e1e67fd95e` compiled and ran successfully.
Phase-one collection took 674 ms. The complete helper took 11.378 seconds,
including startup (10.144 user, 1.230 system; maximum RSS 6,501,468 KiB).

| State key | Visited nodes | Phase-two leaves | Node cap reached | Measured phase-two ms |
| --- | ---: | ---: | --- | ---: |
| 975744 | 17 | 0 | No | 9 |
| 986112 | 10,000 | 427 | Yes | 2,187 |
| 41088 | 10,000 | 478 | Yes | 2,068 |
| 776448 | 10,000 | 451 | Yes | 2,142 |

All fuel-exhaustion, invalid-state, missing-fresh-vertex and rejected-insertion
counters were zero. The first state's 17 nodes match the C prototype. The
other states' counts are incomplete prefixes. These measurements expose
substantial cost per visited node in the instrumented evaluator; they do not
isolate the time spent in each engine function, prove equivalence to C, or
bound the uninstrumented native diagnostic. In particular they do not show
that the fourth state alone explains the earlier timeout.

`phase-two-profile-fixed-evidence/` retains the helper, runner, raw logs,
receipt and audit, with a nonempty object checked on the builder and unchanged
prerequisite object hashes. Next useful work is to measure the costs of state
validation, candidate filtering, vertex selection and insertion on this same
bounded sample before choosing further engine changes.

## Component replay and equivalent state validation

`PhaseTwoComponents.lean` collects up to 1,000 nodes from each of the same four
states, then replays individual engine operations over those inputs. The first
run (job `436420`, execution `521505a9874ce443503fb280024947a6ead2e8d9`)
reported zero milliseconds for every component. Those timings are not accepted:
the pure checksum was not forced before the ending clock read. Its counters,
logs and source remain in `phase-two-components-evidence/`.

The corrected timer writes the computed checksum to an `IO.Ref` before reading
the ending clock. Job `20261008T110539-erdos85__h3-triple-formal-20261007-437976`
at `280ed4603d3a28e435c8d7480f681b1c133095ec` compiled and completed in
7.073 seconds including startup, with the same sample counts and checksums.
`phase-two-components-forced-evidence/` retains its audit and exact records.

| Component | State 986112 ms | State 41088 ms | State 776448 ms |
| --- | ---: | ---: | ---: |
| State validation | 97 | 100 | 100 |
| Candidate filtering | 52 | 43 | 44 |
| Vertex selection | 42 | 36 | 38 |
| Fresh-vertex selection | 5 | 4 | 4 |
| Pattern partitioning | 15 | 14 | 14 |
| Candidate-list assembly | 16 | 13 | 14 |
| Triple insertion | 22 | 20 | 21 |

Each column uses 1,000 sampled nodes. These are separate replay timings,
including iteration overhead. Assembly and insertion also perform partitioning;
insertion replays every candidate, including candidates beyond the collection
cutoff. The figures therefore must not be added into a production runtime
estimate. They identify state validation as the largest measured component.

`PhaseTwoComponentsFast.lean` adds an equivalent state check: cache each row,
and remove its repeated intersection with `M49` after masking by a fibre mask
whose bits already lie below 49. The Lean theorem `stateOKFast_eq` proves
pointwise equality for every state, without a well-formedness precondition.
Job `20261008T110838-erdos85__h3-triple-formal-20261007-440039`, execution
`88c9c3dc8149803ed9e83cc54cefb7c1b45415b9`, compiled that proof with only
`propext` and `Quot.sound`, and completed its helper in 7.273 seconds.

On the three 1,000-node samples, original validation took 97/101/100 ms;
the equivalent check took 30/30/30 ms. Checksums matched. The 17-node first
state is too small for meaningful millisecond timing. This supports integrating
the helper, but is not an end-to-end search speedup measurement.
`phase-two-components-fast-evidence/` retains source, receipts, raw logs and
the proof/timing audit. The engine's `dfs2` now calls `stateOKFast`, and its
soundness proof rewrites through `stateOKFast_eq`.

The integrated source at `cacbdb7b8b35d93e985fed136d4127436eb6ed1b` was
verified in job `20261008T111037-erdos85__h3-triple-formal-20261007-441642`:
Engine, Bridge and Split rebuilt in 11s, 4.8s and 3.6s, with exit zero.
The four exported theorems still have exactly `propext`, `Classical.choice`
and `Quot.sound`, with no `sorry`. `fast-state-build/` retains the successful
fresh-object/source/log audit. The component optimization is integrated and
sound; complete-bucket runtime and graph exclusion remain unverified.

## Bucket-zero sizing and integrated traversal comparison

The ratio-ordered C prototype completed all four bucket-zero states under the
unchanged two-million-node and 20-second internal caps in job
`20261008T111356-erdos85__h3-triple-formal-20261007-443889`, execution
`d02fb5b5430ff42a1113172df00ef16cefc3adaf`. It reported exit zero,
`stopped=0`, `stop_reason=none`, 8,167 phase-one nodes, 458,244 phase-two nodes
and 19,920 phase-two leaves. Wrapper wall time was 0.165 seconds. The fourth
state contributes 62,545 nodes, so it is not the dominant subtree in this
prototype. The control again matched every one of the 384 Lean bucket counts.
`bucket-zero-evidence/` retains the read-only source/binary/log/counter audit.
Phase three is omitted; completion here is sizing evidence, not exclusion.

`PhaseTwoPaired.lean` runs the original and optimized validation in one
10,000-node-per-state Lean profiling job. It forces the completed profile into
an `IO.Ref` before stopping each clock. Job
`20261008T111445-erdos85__h3-triple-formal-20261007-445375` at the same
execution commit compiled and completed in 15.783 seconds including startup.

| State key | Original ms | Optimized ms | Nodes in each run |
| --- | ---: | ---: | ---: |
| 975744 | 9 | 8 | 17, complete |
| 986112 | 2,175 | 1,469 | 10,000, capped |
| 41088 | 2,061 | 1,334 | 10,000, capped |
| 776448 | 2,137 | 1,420 | 10,000, capped |

All non-timing counters matched between variants and the previous profile,
including zero invalid/fuel-exhausted states. The nontrivial prefixes improve
by 32–35% in this instrumented run. This is not a complete-bucket or campaign
runtime bound. `phase-two-paired-evidence/` retains exact source, object hash,
logs, receipts and the cross-profile counter audit.

The measured prefix costs and complete C bucket size support a new bounded
90-second phase-two-only diagnostic (`run_phase_two_fast.py`) against the
optimized engine. It still accepts phase-two leaves and cannot prove graph
exclusion. The earlier timed-out runs retain their original limits and pins.

The optimized phase-two-only native diagnostic completed successfully in job
`20261008T111628-erdos85__h3-triple-formal-20261007-446936`, execution
`85d3b19ad0c9dd26bfc42e8f05e564facad6b304`. It took 67.292 seconds elapsed
(66.107 user, 1.180 system), with maximum RSS 6,485,576 KiB; the 90-second
inner cap did not fire. The runner and wrapper both exited zero. Its nonempty
10,624-byte object has SHA-256
`ba5b387836b542ba2036343adbdd513d7f959179da080b6b700586f8ad9bd4f2`.

The theorem `phaseTwoTraversal` reports exactly `propext`, `Quot.sound` and
its own `._native.native_decide.ax_1_1`, without `sorry` or compiler errors.
`phase-two-fast-evidence/` retains the source, runner, logs, receipt and audit;
all audited prerequisite object hashes remained unchanged. This is a completed
bucket-zero traversal with a constant-true callback at phase-two leaves.
It does not prove those leaves impossible: phase-three completion remains the
next computational step. No new exclusion or old-census credit is claimed.
