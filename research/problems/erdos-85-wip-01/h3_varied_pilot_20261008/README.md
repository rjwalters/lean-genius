# Four-case H3 timing sample

Status: **input/deficient-membership preflight PASS; Deficient U26/R2 certificate and consumer PASS**.

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
The full membership preflight awaits the still-building `CapacityReduction`.

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
those later proof-script changes have not been compiled. The retained proof
and its original plan remain the preflight evidence. The timing runner binds
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
The second deficient sample U369/R11 was subsequently submitted as
`20261008T050258-erdos85__h3-first-column-20261008-206594`, with the same
source ref, audited preflight, and two-hour/16-GiB/one-thread limits.
`DeficientU369R11-launch.json` is a submission record, not a passing result.
Both full sample cases remain unqueued pending their membership proof.
