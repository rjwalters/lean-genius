# H3 residual native parts

Prepared worker and independent collector; not launched. `PLAN.json` now
binds the accepted complete sweep: 378 reusable parts and exactly six
residuals, **89, 134, 142, 186, 279, 298**. A fresh authoritative H5
observation selects four workers, eight CPUs and 64 GiB. This
directory grants no mathematical credit. All Lean execution and native search
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

Real cloud preflight and terminal artifact collection remain required.
