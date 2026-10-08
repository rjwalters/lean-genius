# Four-case H3 timing sample

Status: **input/deficient-membership preflight running; no search queued**.

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

Before any expensive search, compile `FullMembership.lean` and
`DeficientMembership.lean`, including their input modules. Each checks the
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

The preflight is cloud job
`20261008T042839-erdos85__h3-first-column-20261008-180990`, using source
`16d3a56a9ab`, 16 GiB, one compiler thread, and a 20-minute cap.
The copied base contains 610 files; all copied source/log/object hashes match
the original audited receipt. `preflight-launch.json` records this launch,
not a successful proof receipt.
