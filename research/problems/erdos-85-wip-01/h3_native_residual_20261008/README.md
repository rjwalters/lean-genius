# H3 residual native parts

Completed and independently accepted. `PLAN.json`
binds the accepted complete sweep: 378 reusable parts and exactly six
residuals, **89, 134, 142, 186, 279, 298**. A fresh authoritative H5
observation selects four workers, eight CPUs and 64 GiB. This
plan alone grants no mathematical credit. All Lean execution and native search
must stay on the existing cloud builder.

Room message 53044 from `claude-h5` authorizes a subsequent pass over only
timed-out residues: 30 minutes per part, at most two workers while H5 job
`20261008T112746-erdos85__h5-formal-20261008-455708` is live, or four after it
finishes, and a six-hour outer cap. Any further timeout stops the whole pass;
there is no automatic retry or cap increase. A stopped part remains unresolved.

`prepare.py` requires a complete independent sweep audit and checks the exact
384-way coverage against the previously accepted 90 parts. It combines those
objects with newly accepted sweep objects and selects only the remaining
timeouts, including the known residue 89. It pins all source-generation and
prior-audit inputs. An incomplete sweep cannot produce a residual plan.

`observe_h5.py --output FILE.json` reads the exact H5 job on the existing
builder without changing it. `prepare.py --h5-observation FILE.json` requires
that observation to be at most five minutes old. Reobserve H5 immediately
before launching; do not infer that a job finished from a room lease or an
observation timeout. The worker count is fixed for the entire pass. Two workers
use 4 CPUs/32 GiB; four use 8 CPUs/64 GiB. Check the builder's other active
containers and watchdog budget before launch. Do not advance the H3 cloud
branch while the current sweep is live.

`run.py` defaults to a read-only preflight: it validates the frozen plan,
actual cgroup limits, four prerequisite source/object pairs, generated runtime
C, all reused objects, and absence of unaccepted residual sources/objects.
It rejects host execution. Compilation requires
`--execute-approved-plan PLAN_SHA256`. The shared runtime library has a
60-second cap; each native part gets at most 1,800 seconds; the worker stops
at 21,300 seconds inside the six-hour outer deadline. Lean uses `-j1` per part.

`scheduler.py` limits concurrency and dispatches each residue at most once.
`process.py` polls the shared stop event and the directory's `STOP` file.
A timeout, compiler failure, or explicit stop signals other workers and kills
the child's process group, including descendants. A deadline-shortened timeout
is `BUDGET_STOP`, not evidence that the full 30-minute allowance was exhausted.
The coordinator serializes receipts. Failed output objects are preserved
separately before removal from the reusable cache. Successful objects remain
provisional until independent acceptance. Elapsed time is measured per child;
process-global CPU counters are deliberately omitted because overlapping
children would contaminate those measurements.

`capture.py --job JOB --commit COMMIT --output DIRECTORY` reads a specific
terminal job; `--preflight` selects the read-only preflight audit. Pending jobs
return their exact PID and presence without creating acceptance files. The
collector verifies the execution commit, job resource specification, committed
worker sources and inputs, actual cgroups, all prerequisite and reused objects,
generated sources, raw logs, exact three-axiom sets, and fresh output object
hashes and times. It reads prerequisite/reused/accepted objects twice to catch
changes during collection. Raw evidence is immutable; use a new output
directory for any later collection and force-add ignored `*.log` files when
banking it.

Full success means `H3_RESIDUAL_ARTIFACT_AUDIT_PASS`. A stopped pass can retain
only its independently checked successes as `PARTIAL_RESIDUAL_ARTIFACT_AUDIT`.
Neither result establishes the assembled H3 cell or stratum. Once all 384
parts have independent acceptance, the full cell still needs compilation and
its exact axiom audit, followed by integration with the audited pair cell and
the H3 stratum audit.

Validation uses metadata fixtures, small temporary files, threads and dummy
Python children only. It checks frozen-input drift, residual coverage,
resource caps, stop propagation, descendant termination, immutable logs,
failed compilation, source/object/axiom drift, missing or duplicate parts,
excess concurrency and partial acceptance. Run with:

```sh
python3 -B -m unittest discover -p 'test_*.py'
```

## Independently accepted preflight

Read-only job `20261008T144142-erdos85__h3-triple-formal-20261007-578119`,
execution pin `a464ccde01560afabfd2f5250b30ebc6a0356a39`, exited zero.
`preflight-evidence1/AUDIT.json` is `RESIDUAL_PREFLIGHT_AUDIT_PASS`, with
22 retained hash-verified files. It checked all 378 reused objects, runtime
prerequisites and source/input pins, with actual cgroups of eight CPUs and
64 GiB, four workers, and no residual attempt directory. It granted no new
mathematical credit.

The frozen plan SHA256 is
`f6443ae8f4debda5515f031a8be7b0e997b4c4a2062f8ca4e8c5de7312874f00`.
All execution code and this plan remain byte-identical to the preflight pin.
The independent auditor was subsequently corrected for the timeout/normal
exit race observed in sweep part 279: an explicit full-cap timeout remains
unresolved even if the child exits zero, and any output object must be absent
from the reusable cache. Quarantined bytes are retained. All 66 preparation,
process, scheduler and artifact tests pass, including two regressions for
this case. The preflight's original auditor snapshots remain unchanged.

## Terminal residual acceptance

Job `20261008T144421-erdos85__h3-triple-formal-20261007-582400`, execution
pin `ed45ae396a63ae340c5e55f8a940d31746c97f23`, exited zero.
`residual-evidence1/AUDIT.json` is `H3_RESIDUAL_ARTIFACT_AUDIT_PASS`:
all six residues accepted, no unresolved parts. All 36 retained evidence
files are hash-verified. The run took 252.127 seconds overall; part times
were 120.157 (89), 104.143 (134), 109.480 (142), 98.935 (186), 90.331
(279), and 146.775 seconds (298). No timeout, retry or cap change occurred.
`h5-observation-before-launch.json` preserves the second, fresh observation
made after banking preflight and immediately before launch.

Together with the original 90-part baseline and 288-part sweep, all 384
parts now have independent artifact acceptance. The cell and stratum
compositions still need their own bounded compilation and acceptance;
`whole_cell_verified` remains false in this residual audit.
