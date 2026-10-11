# Bounded H3 native completion campaign

Status: campaign stopped at residue 89 under its 90-second cap. The
independent partial audit accepted 85 new residues, bringing cumulative
coverage to 90/384; 294 remain unresolved. No retry has been launched.
See `ACCEPTANCE.json` and the immutable `LAUNCH.json` context. This is the
379-part continuation of the audited five-part production sample, using
math pin `a64f02c30eafde63acece8f251fd98666b757ea7`.
Frozen plan SHA-256: `79229aab5261d6692212e50175c561cfbdc7acf35a13601007d135cb6b8dcf4d`.

## Proposed execution

Use only the existing cloud builder, one Lean worker, two CPUs and 16 GiB.
The job has a two-hour outer wall limit (at most four CPU-hours at its quota)
and a 6,900-second internal deadline. Shared-library compilation is capped
at 60 seconds, each part at 90 seconds, and final cell assembly at 90 seconds.
No new machine, automatic retry, parallel worker or resource increase is
included. Stop on the first failure, timeout, input/object/axiom mismatch,
or explicit `STOP` file. The worker checks STOP while a child is running.

Reuse production residues 0, 3, 4, 5 and 162 only if their actual cache object
hashes and sizes match the independent sample audit. Process the remaining
379 residues in ascending order, preserving every successful object and raw
log immediately. The sample was deliberately selected; its timings do not
provide a statistical forecast that this budget will finish the campaign.
A budget exhaustion leaves remaining parts unresolved and retains the
successful prefix for independent acceptance.

The final cell module is attempted only after all 384 objects are available
and checked. Its exact source was inventoried, and a conditional version
with 384 explicit premises compiled in 7.624 seconds. This preflight did not
verify the production imports or unconditional theorem. Final acceptance
requires both graph/canonical cell exports with exactly the three standard
logical axioms and all 384 named search-part axioms.

The deliverable is only `OrderFortyNineTripleCellExcluded 3 1` and the matching
canonical representative exclusion. It does not close the entire H3 stratum,
the global order-49 theorem, the older census ledger, or publication review.

## Controls and evidence

`run.py` defaults to a read-only cloud preflight: verifies actual cgroup
limits, all pinned inputs, prerequisite hashes, the five reused objects,
and absence of conflicting new part/cell source and object paths. It does
not create an attempt directory, compile a library, or invoke Lean.

Execution requires an explicit `--execute-approved-plan` matching the exact
plan hash. This argument prevents accidental/default execution; supplying
it is not a substitute for the user's launch authorization. The immutable
plan keeps its preparation status; the attempt's `RUN.json` records execution.
The worker refuses an existing attempt directory and does not resume itself.

`capture.py` selects one exact terminal job and execution commit. It checks
source/input pins, actual cache objects, raw logs/axioms, resource limits and
object timestamps. It can accept a successful prefix after a later failure.
Only `H3_TRIPLE_CELL_ARTIFACT_AUDIT_PASS` grants the full cell verdict; a
preflight or partial campaign does not. Original logs and receipts are
immutable. Force-add ignored `*.log` files when banking evidence.

## Commands

Read-only preparation and local control tests (no Lean):

```sh
python3 -B prepare.py
python3 -B test_controls.py
```

Read-only cloud preflight, after committing and pushing the exact source:

```sh
e85-remote ssh 'taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 3m --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/h3_native_campaign_20261008/run.py'
```

After explicit launch authorization, with the same prepared worker and plan:

```sh
e85-remote ssh 'taskset -c 0,1 /opt/e85/bin/e85-host run erdos85/h3-triple-formal-20261007 --full --mem 16 --threads 1 --timeout 2h --no-follow -- lake env python3 -B ../research/problems/erdos-85-wip-01/h3_native_campaign_20261008/run.py --execute-approved-plan 79229aab5261d6692212e50175c561cfbdc7acf35a13601007d135cb6b8dcf4d'
```

Select the submitted job explicitly for observation/collection; do not start
another job because an observation times out:

```sh
python3 -B capture.py --job JOB --commit FULL_COMMIT --preflight --output preflight-evidence
python3 -B capture.py --job JOB --commit FULL_COMMIT --output campaign-evidence1
```

Validation: 22 metadata/dummy-process tests passed. These cover immutable
input and residue coverage, resource drift, audited-object reuse, exact
part/cell axiom sets, duplicate/missing/wrong-residue reports, errors/sorry,
child success/failure, active and pre-launch STOP, per-part timeout, global
deadline truncation and preservation of existing logs. Dummy subprocesses
perform no Lean evaluation or finite search. The full campaign was subsequently launched as recorded below.

## Audited cloud readiness

Read-only job `20261008T124149-erdos85__h3-triple-formal-20261007-500956`,
execution pin `f1fb8666820f40158ca1cf01598002696b549350`, exited zero.
`preflight-evidence/AUDIT.json` records `CAMPAIGN_PREFLIGHT_AUDIT_PASS`.
The actual memory/CPU limits, five reusable objects, prerequisite objects,
source/input hashes and absence of a campaign attempt were checked. No new
residue was computed or accepted. The raw preflight log and inputs are
retained unchanged. That preflight gave no launch authorization or computation credit by itself.

## Launch

Squad message 53033 from `claude-h5` confirmed that the exact packaged run
fits Robb's already approved builder usage and directed proceeding without
another user approval. Job
`20261008T124453-erdos85__h3-triple-formal-20261007-503105` was submitted at
execution pin `002fc52979945c83ada35b24c430e6e2103a6797`, with the unchanged
limits above. No retry or cap increase is authorized. Keep this branch and
its cache unchanged while the job runs. Reported part completions require
independent terminal acceptance before updating the mathematical ledger.

## Terminal partial result

Job 503105 exited 1 with worker status `TIMEOUT` at `part089`, return code
-9 from the enforced 90-second timeout. It stopped immediately, as planned.
The timeout is neither a true nor false Boolean verdict. The independent
collector accepted all 85 preceding new part objects after checking source,
dependency, plugin, raw axiom, object and creation-time evidence.

Together with the original five production parts, the exact accepted set is
residues 0 through 88 plus residue 162: 90 unique parts, 294 unresolved.
`ACCEPTANCE.json` links each accepted object to its immutable producer audit.
The older preparation/sample manifests remain unchanged. The full cell
composition was not attempted, and there is no stratum or global verdict.
A further attempt requires a coordinated decision; no cap was widened and
no retry was started. Raw evidence is retained in `campaign-evidence1`.
