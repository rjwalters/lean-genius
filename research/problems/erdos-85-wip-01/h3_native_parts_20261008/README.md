# H3 native completion parts: prepared inventory and sizing plan

Status: the bounded five-part sample passed its independent artifact audit.
Five of 384 unique residues are verified; 379 remain. The full campaign is
not launch-ready or authorized here.

The current engine is pinned at
`a64f02c30eafde63acece8f251fd98666b757ea7`. Its Runtime, Engine, Bridge and
Split have an audited fresh build. Bucket `triplePart 384 0 = true` has
been verified with the production runtime plugin in 15.132 seconds. The
subsequent sample also verified residues 3, 4, 5 and 162, as recorded in
`ACCEPTANCE.json`. The immutable preparation manifest retains its original
pre-run statuses; acceptance is recorded separately.

## Exact deliverable

`MANIFEST.json` lists every residue from 0 through 383 exactly once, with
its module name, source hash, theorem name and expected native axiom.
`prepare.py` deterministically emits each part and the full cell composition.
The generated composition imports all 384 modules, covers every bounded
index, and applies the existing soundness bridge to obtain both the
canonical representative exclusion and `OrderFortyNineTripleCellExcluded 3 1`.

The review bundle is under `source-review/Proofs`, outside the production
library glob. Its five part sources have now been compiled at their production module
paths and independently audited. The full composition remains uncompiled.
Preparing `native_decide` source alone is not computation credit.

The earlier bucket-zero object belongs to a temporary diagnostic module.
It proves the needed proposition but is not a compiled production
`Erdos85H3TripleCompletionPart000` module. This plan preserves its original
identity and receipt. Compiling the production Part000 source is a deliberate
packaging check, not another mathematical bucket credit.

This new decomposition is an alternative route to the same `(3,1)` cell.
It does not reduce or replace the old census ledger's 1,811 outstanding
obligations. A later whole-H3 integration also needs the separately audited
pair-cell `(3,0)` result and the existing three-high stratum capstone. Closing
this cell alone would not prove the complete order-49 exclusion or finish
the paper's human review/publication work.

## Completed bounded sizing run

The sample used the existing cloud builder, pinned Lean image and current
H3 cache, with one worker, a two-CPU quota and 16 GiB. These production module
sources ran sequentially with the audited Runtime plugin:

| Residue | Historical phase-one leaves | Purpose |
|---:|---:|---|
| 0 | 4 | Validate the production module packaging against the known result |
| 3 | 0 | Check an empty hash bucket |
| 5 | 1 | Check a one-leaf bucket |
| 4 | 3 | Check a median-count bucket |
| 162 | 11 | Check the largest observed leaf-count bucket |

The historical profile is retained, audited instrumentation with 8,167
phase-one nodes and 1,088 leaves. It is not a proof of bucket completeness,
a phase-two workload estimate, or a random statistical sample. In particular,
one phase-one leaf can have a much larger completion subtree than another.

Caps: 60 seconds for compiling the shared library, 90 seconds per part,
and ten minutes for the entire job. That allows at most 510 seconds for the
five capped Lean runs plus library compilation, with outer overhead bounded
by the job cap. Reuse the same checked library across the five parts.
Do not start another part after a timeout, compiler failure or explicit STOP.
Keep successful objects and raw evidence even if a later part fails. No
automatic retries, resizing, new machines or full-part loop are included.

`run_sample.py` implements this fixed five-part sequence. It refuses existing
sources/objects, verifies the actual cgroup memory and CPU limits, checks
the audited dependency hashes before each part, and retains completed objects
immediately. Sources are staged at their real `Proofs.*` module paths and
removed after each invocation. Objects are retained both in the H3 cache and
under the immutable attempt directory. The source inventory alone runs none
of this work.

`capture_sample.py --job JOB --commit FULL_COMMIT` independently checks an
explicitly selected terminal job, exact source/command hashes, raw axiom
reports, actual object hashes/sizes/modification times, library hash and
prerequisites. While the job is live it reports the exact PID and writes no
acceptance record. Successful prefixes can be retained after a later timeout;
only explicitly accepted parts receive credit. Neither script launches the
full set or retries a failed part.

## Audited sample result

Job `20261008T121835-erdos85__h3-triple-formal-20261007-487248`, execution
commit `afcd487aecce0b9950355c0d06e2f81ffef63093`, exited zero.
`sample-evidence/AUDIT.json` records `SAMPLE_ARTIFACT_AUDIT_PASS` after
checking each retained source, raw axiom report, source/object dependency,
plugin, actual cache object hash and its creation time within the job.
All five reports contain exactly `propext`, `Quot.sound` and the part's
own named native-decide axiom, with no `sorryAx`.

| Residue | Elapsed seconds |
|---:|---:|
| 0 | 15.183 |
| 3 | 3.968 |
| 5 | 3.918 |
| 4 | 5.971 |
| 162 | 34.457 |

Shared-library compilation took 1.115 seconds. Every part finished within
its 90-second cap. Sources and raw logs are retained here; compiled objects
remain in both the cloud attempt directory and the H3 cache, with hashes
and sizes in the audit. Residue zero validates production packaging for an
already verified proposition; the sample adds four new mathematical
residues. There are five unique accepted residues and 379 unresolved ones.
These deliberately chosen timings provide no statistical whole-run bound.
The whole-cell theorem and its 384-part composition remain unverified.

## Acceptance and subsequent decision

For each part, retain the exact execution commit, generated source bytes,
command, terminal return code, time/resource receipt, object hash, plugin
hash, raw log and printed axiom set. Check the generated source against the
manifest and all four dependency sources/objects against the fresh audit.
The expected part trust set is `propext`, `Quot.sound` and its own named
native-decide axiom; reject unreviewed extras and `sorryAx`.

A timeout or memory/compile failure leaves the part unresolved. An explicit
false Boolean result needs investigation; it must not be silently converted
to exclusion or retried with different semantics. Completed parts require
independent artifact acceptance before any ledger update.

After the sample, review actual elapsed times, memory use and any failures.
This deliberately selected sample cannot justify a statistical full-run
estimate. A proposed full campaign must name a fixed worker count, global
wall/CPU budget, per-part limits, stop conditions, immutable artifact
collection and source pin. It also needs a complete aggregation/build check
and explicit launch authorization; none is inferred from these prepared
files. Until then, the whole-cell composition remains uncompiled.

## Reproduce the source preparation

```sh
python3 -B prepare.py
python3 -B prepare.py --emit-part 162 --output /tmp/Part162.lean
```

These commands perform source and metadata checks only. They neither run
Lean nor start cloud work, and refuse to overwrite differing output bytes.
