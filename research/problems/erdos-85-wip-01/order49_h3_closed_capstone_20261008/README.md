# H3-discharged order-49 capstone

Status: source and acceptance procedure prepared; compilation pending.

`Proofs.Erdos85OrderFortyNineCapstoneH3` imports the unchanged accepted
conditional capstone and the independently accepted H3 stratum. Its three
corollaries leave only the one-high checked capacity inventory and seven-high
structural HSB evidence as hypotheses (with a depth parameter):

* `not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence`;
* `minDegreeForC4_fortyEight_fortyNine_exact_of_h1_h7Evidence`;
* `minDegreeForC4_fortyNine_lt_fortyEight_of_h1_h7Evidence`.

All names are in namespace `Erdos85`. Expected exact axiom sets are the
unions of previously accepted exports: 601, 607 and 604 respectively.
These are conditional Lean conclusions, not an unconditional finite-drop
proof, a resolution of the full Erdős problem, or paper publication approval.

## Accepted inputs and complete import closure

The original capstone audit binds 500 source/object pairs at
`c955257fbd9a4b4aab5e96c90e26cdedb0f74a5c`. The H3 stratum audit binds
its object and 417 explicit prerequisite objects at
`bb71918f37667a3bd2cdc0c2ba21be33b593d9a7`. Their 28 shared pair modules
have identical source and object hashes. Only 61 missing accepted sources
were materialized; existing sources were unchanged.

Full import traversal found one additional transitive dependency,
`Erdos85OrderFortyNineThreeHighOneFiber`, an unchanged proof-only baseline
module. Its current cloud object is recorded in `supplementary.json` as
observed, not newly accepted. Before compiling the wrapper, `run.py` rebuilds
that source into a separate output and requires byte identity with the
observed object. It never overwrites the existing cache object. The complete
closure is 891 imported repository modules and the new wrapper.

`PLAN.json` binds every source hash, imported object hash/size, producer
receipt and expected axiom set. `prepare.py` checks retained producer files,
compares pinned source bytes, refuses conflicts, and traverses all imports.
Its initial traversal discovered the baseline dependency after the missing
sources had been copied; its final successful run copied zero more files.
Preparation executes no Lean or native search.

`transfer.py` uses the already tested exclusive-copy helper from H3 stratum
integration. It inspects the entire 500-object capstone batch, refuses any
differing existing destination, copies only absent objects, and verifies all
other H3 objects. `capture_transfer.py` repeats read-only inspection and
retains the pinned terminal job, receipt and metadata. Transfer grants no
new theorem.

## Bounded compilation and independent acceptance

All compilation uses the existing cloud builder, with one worker, two CPUs,
16 GiB, 90 seconds per module and a four-minute outer job limit. Direct Lean
reuses the accepted objects; no native searches are scheduled. The full
891-object ledger is checked before and after compilation.

After committing and pushing preparation, run the host transfer, bank its
receipt, then commit and push again before launching `run.py`. Do not move
the cloud branch while either job is active. The compile job runs:

```
taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 4m --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/order49_h3_closed_capstone_20261008/run.py
```

`capture.py --job JOB --commit FULL_COMMIT` independently checks the pinned
source tree, terminal job, full object ledger twice, fresh object creation,
baseline byte-identical rebuild, and all three exact printed axiom sets.
Only `H1_H7_CONDITIONAL_CAPSTONE_ARTIFACT_AUDIT_PASS` grants acceptance.
Keep raw evidence immutable and force-add ignored logs when banking.

## Accepted object transfer

Host job `20261008T151157-erdos85__h3-triple-formal-20261007-602337`
at `ef7d2bda68008a8380d17acfffc58141dd84094b` exited zero. Independent
read-only inspection accepted all 500 capstone objects; 216 absent objects
were copied, with no overwrites. All other H3 inputs also matched.
`transfer-evidence1/AUDIT.json` reports
`CAPSTONE_TRANSFER_ARTIFACT_AUDIT_PASS`. Compilation remains pending.
