# Four-case H3 timing sample

Status: **both membership gates PASS; both deficient cases and Full U3/R3 PASS;
Full U54/R20 timed out at its two-hour job cap and remains unresolved**.

Claude requested 3–5 additional pairs after the U1/R15 pipeline fix, to measure
cost variation before a larger campaign. The four selected cases are:

| Branch | U index | R index | Compact U code | R edge (6,7) |
| --- | ---: | ---: | --- | --- |
| Full | 3 | 3 | (6,9,5) | true |
| Full | 54 | 20 | (9,12,90) | true |
| Deficient | 26 | 2 | (6,9,11,1) | false |
| Deficient | 369 | 11 | (9,12,92,2) | true |

These choices vary the census branch, compact first-code class, secondary
representative, and special R edge. They are diagnostic diversity choices,
not a random or statistically representative sample. Their timings cannot
by themselves justify a precise average over all 1,815 pairs.

`prepare.py` reconstructs the literal set operations in the current Lean
census sources, checks their formulas, checks the full counts 565 → 276 → 261
and deficient count 1,554, and verifies each selected pair is retained. It
reads compact parameters directly from the representative vectors and records
all input hashes in `PLAN.json`. This Python check is not a Lean proof.

Each pair has separate `Inputs`, `Certificate`, and `Consumer` modules. The
certificate uses the same `threeHighNativePairSearch` as U1/R15; a later
consumer failure therefore need not discard its compiled object. The consumer
uses the cloud-verified local-irreducibility fix for `threeHighCrossDomain`.
All files remain outside the library's default build glob.

Before an expensive search for a case, compile its corresponding
`FullMembership.lean` or `DeficientMembership.lean`, including its input
module. Each checks the
selected pair's census membership and its exact representative/input identity.
They require separate import paths: the full build uses the checked
`CapacityReduction` plus full census output, while the deficient build uses
the checked deficient census output. Both censuses contain a module named
`Pruning`; do not combine those search paths into a single environment.

The split U1/R15 rerun must first validate the revised pipeline. Then the
bounded timing sample should retain each module's wall/CPU time, peak memory,
source/object/log hashes, exit status, and exact axiom reports. A timeout or
failed module remains unresolved. No new instance or full campaign is
authorized by this preparation artifact.

Run `python3 prepare.py` to recheck generated sources and provenance without
Lean or search. `python3 prepare.py --write` regenerates them. All eventual
Lean builds and finite searches run on the cloud builder.

The U1/R15 split pipeline has now passed and its evidence is independently
audited. `check_preflight.py` validates an exact copied snapshot of the
previously verified deficient census (203 modules, receipt SHA
`190d7e37c814bd8a7eea54e6ad1bbcba73e092e6e0d77deddc717bab098bfecc`),
builds all four input modules, then checks deficient membership and representative
identity with standard axioms only. It does not run any certificate search.
The full membership preflight subsequently passed in cloud job
`20261008T062957-erdos85__h3-triple-formal-20261007-260985`, with
independent audit retained in `../h3_u1r15_census_reduction_20261008/evidence/`.
All four full membership/input reports use standard axioms only; receipt
SHA-256 is `36fe58d9bae19306311cc9655d0300a3ecf60e669141c4fe834e89be670de820`.

The preflight passed in cloud job
`20261008T042839-erdos85__h3-first-column-20261008-180990`, using source
`16d3a56a9ab`, 16 GiB, one compiler thread, and a 20-minute cap.
The copied base contains 610 files; all copied source/log/object hashes match
the original audited receipt. `preflight-launch.json` now links its passing receipt. `preflight-evidence/`
retains all five sources, complete logs, the executed `PLAN.json`, run record,
and independent audit. All five object hashes were read independently from
the cloud and matched. The four deficient membership/identity reports use
exactly the standard three axioms. Dependencies took 585.40 seconds and the
membership module took 319.96 seconds, with exit 0 at 04:44:26 UTC.

The current generator simplifies membership formulas before decision checking;
the current full membership script has passed, while the later deficient
script remains uncompiled. The retained deficient proof and its original
plan remain that branch's preflight evidence. The timing runner binds
to that immutable plan and requires each selected input, certificate, and
consumer source to match both the current plan and the verified plan exactly.
A change in any selected case or source therefore still blocks its search.

`check_case.py` runs one selected pair only after an independent audit of its
matching preflight. It rechecks the prepared source hashes, membership and
input-identity reports, and the preflight receipt/logs. The two census branches
have separate prerequisites: a verified deficient preflight suffices for a
deficient timing case; a full case must wait for its full membership proof.
Each case is a separate bounded cloud job, initially capped at two hours,
16 GiB, and one compiler thread on the existing instance. A timeout remains
unresolved and is a censored timing observation, not a rejection result.

The runner builds Inputs, Certificate, and Consumer separately, preserving
source copies, raw logs, object hashes, exact native-backed axiom sets, and
wall/CPU/peak-RSS measurements. Linux `wait4` RSS is per Lake process and its
waited children, not total container memory. There is no retry or batch launch.
No case is queued merely by preparing this runner. Example after a passing,
independently audited deficient preflight:

```sh
lake env python3 ../research/problems/erdos-85-wip-01/h3_varied_pilot_20261008/check_case.py \
  --case DeficientU26R2 \
  --membership-evidence ../research/problems/erdos-85-wip-01/h3_varied_pilot_20261008/preflight-evidence \
  --output ../research/problems/erdos-85-wip-01/h3_varied_pilot_20261008/_build/DeficientU26R2-first
```

Deficient U26/R2 passed as
`20261008T044647-erdos85__h3-first-column-20261008-194983`, at source
`1d388af91cd`, under the above two-hour/16-GiB/one-thread limits.
`DeficientU26R2-evidence/` retains exact sources, raw per-module logs, run
records, and an independent audit. All three object hashes match a separate
cloud read; both certificate and consumer targets were freshly built.
The certificate took 192.404 seconds wall / 190.908 seconds user CPU,
with wait4 peak RSS 6,549,052 KiB; its consumer took 9.702 seconds.
Both reports contain exactly the standard three axioms plus this pair's
native-decision axiom. The consumer retains its cross-domain and external
capacity premises. This closes one pair, not the deficient census or H3.
The second deficient sample U369/R11 passed as
`20261008T050258-erdos85__h3-first-column-20261008-206594`, with the same
source ref, audited preflight, and two-hour/16-GiB/one-thread limits, exiting
zero at 06:17:21 UTC. Its certificate took 4,442.672 seconds wall (74.04
minutes), 4,438.415 seconds user CPU, and 8,332,452 KiB peak RSS. Its consumer
took 10.345 seconds. `DeficientU369R11-evidence/` retains all three exact
sources, logs, individual receipts, the job log, and an independent audit.
Source/object hashes were separately checked on the cloud; certificate and
consumer were freshly built. Both reports have exactly the standard three
axioms and `Erdos85.VariedPilot.DeficientU369R11.rejected._native.native_decide.ax_1_1`.

The two deficient certificate times differ by more than a factor of 23.
Together with the 97.4-minute U1/R15 pilot, this shows substantial variation
among these selected cases; it does not determine a census-wide average.
The full membership gate subsequently passed, enabling the two full diagnostics below.

Full U3/R3 passed as cloud job
`20261008T063412-erdos85__h3-first-column-20261008-264145` at commit
`9a1555a52461ab6d53bb145378f92de81c88cdc6`, with 16 GiB, one Lake
thread, and a two-hour cap. It uses the independently audited full membership
evidence above. `FullU3R3-launch.json` records the exact source hashes.
It completed with exit zero at 06:38:33 UTC. The certificate took
238.976 seconds wall time (237.365 seconds user CPU, 6,562,176 KiB RSS);
the consumer took 10.336 seconds. Both were freshly built and use standard
axioms plus exactly the matching FullU3R3 native rejection axiom.
`FullU3R3-evidence/` retains the independently audited source/log/receipt
sets; all cloud object hashes matched. Full U54/R20 used the same bounded limits.

Full U54/R20 ran as
`20261008T064336-erdos85__h3-first-column-20261008-270638`, using the
same pinned source commit `9a1555a52461ab6d53bb145378f92de81c88cdc6`,
16-GiB limit, one Lake thread, and two-hour cap. It is the last of the four
agreed diagnostic cases. It reached the 7,200-second job cap and exited 124.
`FullU54R20-timeout-evidence/` retains the original job records, partial receipt,
input/certificate logs and source snapshots. `audit_full54_timeout.py` checked
the terminal exit, explicit timeout event, exact execution sources, absence of
the old runner/compiler and container, and actual object inventory. Inputs has
the expected object; Certificate and Consumer have neither completed objects
nor per-stage receipts. The consumer source was never executed.

The original `RUN.json` still says `RUNNING`, with Certificate active: the
outer container timeout killed the runner before it could finalize that file.
It is retained unchanged; `AUDIT.json` records the authoritative TIMEOUT.
This is a censored timing observation, not a rejection, counterexample or OOM.
No completed certificate duration or final peak RSS is available. No retry is
authorized by this record and no automatic restart was performed.

Audited certificate timings so far (consumer time excluded):

| Diagnostic case | Certificate wall minutes | Maximum RSS KiB |
| --- | ---: | ---: |
| Deficient U26/R2 | 3.207 | 6,549,052 |
| Deficient U369/R11 | 74.045 | 8,332,452 |
| Full U3/R3 | 3.983 | 6,562,176 |
| Full U54/R20 | TIMEOUT (two-hour job cap) | unavailable |

The earlier U1/R15 pilot took 97.400 minutes. This selected diagnostic
set shows large cost variation; it is not a basis for an unbiased campaign
average. The timed-out case must remain censored in any cost analysis.
