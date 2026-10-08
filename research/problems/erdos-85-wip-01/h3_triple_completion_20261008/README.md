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
