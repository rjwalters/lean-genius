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

Validation: 26 metadata/dummy-process tests pass, including full-cap versus
global-budget timeout classification and non-timeout failures. The actual
sweep has not yet launched; preflight and launch receipts will record it.
