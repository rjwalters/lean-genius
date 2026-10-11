# H3 skip-on-timeout sweep

Prepared continuation after the first campaign stopped at residue 89.
The independently accepted baseline is residues 0 through 88 plus 162
(90/384). Residue 89 is carried as a known timeout and is not rerun here.
This pass visits the remaining 293 never-attempted residues once, in
ascending order, using exactly the same mathematical sources and plugin.

Squad message 53044 from `claude-h5` authorized this stage on the existing
builder: keep the 90-second cap, record and skip timeouts, and do not retry
inside the pass. The subsequent residual stage is separately bounded at
30 minutes per timed-out part and six hours overall, up to two workers while
H5 is live or four after it finishes. That residual stage is not launched
by this package.

This sweep uses one worker, two CPUs, 16 GiB, a 6,900-second worker deadline
and a two-hour outer cap. Shared-library compilation remains capped at
60 seconds. A full 90-second part timeout is retained and skipped. A child
whose time was shortened by the global budget is a budget stop, not a
classified 90-second timeout. Compiler errors, explicit STOP, changed
sources/objects/axioms and global budget exhaustion halt the pass. No retry
or new machine is included.

The worker rechecks all 90 previously accepted objects and the four runtime
prerequisites. A failed part never receives acceptance. If a timed-out child
left an object, its bytes are retained under `unaccepted-objects` before
removing that unaccepted cache file. It cannot be silently reused as proof.
Every accepted part needs the same independent source, raw axiom, cache
object, timestamp and resource checks as the first campaign.

The worker defaults to read-only preflight. Execution requires the exact
PLAN hash supplied with `--execute-approved-plan`; authorization is recorded
in the plan, not inferred from that argument. Existing attempt directories,
source/object conflicts and STOP files are refused.

```sh
python3 -B prepare.py
python3 -B test_controls.py
```

Preflight after committing and pushing:

```sh
e85-remote ssh 'taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 3m --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/h3_native_sweep_20261008/run.py'
```

Authorized sweep, after the preflight is independently accepted:

```sh
e85-remote ssh 'taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 2h --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/h3_native_sweep_20261008/run.py --execute-approved-plan 5729541d79436ea26cc10f881ae03d20f57960084d14473687a07238bff6f30d'
```

```sh
python3 -B capture.py --job JOB --commit FULL_COMMIT --preflight --output preflight-evidence
python3 -B capture.py --job JOB --commit FULL_COMMIT --output sweep-evidence1
```

The collector checks both successful parts and timeout classification. It
accepts only completed, independently checked objects. Neither a completed
sweep nor a partial sweep proves the whole cell; no cell composition is run
here because residue 89 is already unresolved. Preserve all receipts and
force-add ignored raw logs before banking results.

Validation: 34 metadata/dummy-process tests pass, including full-cap versus
global-budget timeout classification, non-timeout failures and a child exit
racing the full-cap timer.

## Audited preflight

Read-only job `20261008T131421-erdos85__h3-triple-formal-20261007-520534`,
execution pin `e2578cb884187bbd93359201cd48b46497bb5235`, exited zero and
passed independent collection as `SWEEP_PREFLIGHT_AUDIT_PASS`. It checked
all 90 reusable objects, the source/input/runtime pins and actual resource
limits. It ran no native part and granted no new mathematical credit.

## Terminal sweep acceptance

Job `20261008T131600-erdos85__h3-triple-formal-20261007-522397`, execution
pin `61e4c3ec17cac2fefea52542abc3580ee2d5a222`, exited zero after all 293
attempts. `sweep-evidence1/AUDIT.json` is `H3_SWEEP_ARTIFACT_AUDIT_PASS`:
288 new parts accepted, plus the original 90, for 378/384. The unresolved
residues are exactly **89, 134, 142, 186, 279, 298**. The new five each
received the full 90-second allowance. No whole-cell credit is granted.

The initial collector stopped at its requirement that every timed-out child
have a nonzero exit code (`collection-attempt1.stderr`). Part 279 raced the
timer: elapsed 90.139596547 seconds, explicit `TIMEOUT`, child exit 0.
The worker correctly classified it as unresolved, preserved its 6,712-byte
object under `unaccepted-objects`, and removed it from the reusable cache.
The corrected auditor checks the explicit timeout, exact full cap, elapsed
time and terminal child result; it does not turn that object into a success.
Eight regressions exercise this case and reject short-deadline, early,
missing-result and non-timeout records. No computation was rerun.

The accepted collection retains 606 hash-verified files, including all raw
logs and the quarantined object. Producer records and the execution pin
remain unchanged. The next stage may use only the six unresolved residues,
under the separately authorized residual limits.
