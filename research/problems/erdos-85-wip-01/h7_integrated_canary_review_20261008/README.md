# Integrated H7 canary review, 2026-10-08

**Targeted review PASS** at Claude's commit
`797579e113ab59e1bcbcb93eb0b84540b628ded0`. The atomic batch reservation and
mixed canary selection address the two earlier findings. This review does not
establish AWS-path readiness, execute the 386-item canary, or authorize a fleet.

## Reservation and canary metadata

`check_metadata.py` extracts the reviewed Git blobs into a fresh temporary
directory and runs the in-tree metadata suite there: **16 tests, exit 0**.
Its `slot_loop` AST is identical to the previously tested proposed patch;
the entire worker hash is also identical:
`e159d9fe358488fbaf8c6f3095915b613beb895c7fff3c07e5b72cd5af2792d4`.
Capacity is reserved under the limit lock before the first store call, then
released on completion and all pre-claim exits. The cap continues to count
completed plus active batches; it is not a lifetime cap on failed attempts.

The pinned selection contains two covers and six batches of leaves 0–63 from
six distinct cubes: **386 items**. These are ordinary main-manifest IDs. The
generated user data carries the `--only` selector and 120-second partial interval
while retaining the full manifest identity. Source review confirms bootstrap
passes the interval to the worker. No generated shell script was executed.

The actual `one_pass` function was exercised with a mocked controller backend:

| Manifest / certified rows | Calls controller STOP? |
|---|---|
| Full 5,945-row manifest / eight canary rows | No |
| Full manifest / all 5,945 rows | Yes |
| Hypothetical eight-row manifest / all eight | Yes |

The implemented `--only` selection therefore avoids the automatic STOP caused
by completing a restricted manifest. A remaining runbook clarification is to
say whether the existing watcher stays running in tmux during setup/full launch
or is ended with Ctrl-C. `controller stop` is not a substitute for ending a
watcher: it persists `control/STOP`. An existing alarm or budget STOP still
requires deliberate review; no automatic clearing was proposed or tested.

`metadata/RESULT.json` and the complete unit log retain these checks. Every
source hash used by the local metadata run matches the cloud execution snapshot.

## Actual cloud end-to-end evidence

Producer job `20261008T085923-commit-797579e113ab-359334` has authoritative
**exit 0**. Its wrapper prints `Ran 16 tests`, `OK`, and `E2E_ALL_PASS`.
Because the wrapper pipes the unit output and does not itself propagate that
unit-test exit independently, the separate frozen-source rerun above supplies
an explicit unit exit check.

`audit_cloud.py` ran read-only by SSH on the existing builder and inspected the
actual files. It checked execution/source Git identity, the raw job and E2E
logs, 12 named PASS lines, five CERTIFIED ledgers, and exactly 21 distinct
CERTIFIED item receipts. All five ledgers record the reviewed commit and the
correct input/manifest hashes; certified items carry the approved solver/checker
binary hashes, solver exit 20, checker verified marker, positive proof size,
proof hash, and no early checker closure. The reclaimed F9 batch carries three
prior items. Retained files also support fake-checker ALARM/STOP, refusal to
claim with an unapproved checker or excessive memory reservation, no further
claim after STOP, and an INCOMPLETE solver-timeout batch without STOP.

The producer's uncommitted `receipts/e2e_test_builder.txt` was read only and
matches the raw builder E2E log byte for byte. It was not edited or committed
on Claude's branch by this review.

Raw job-log SHA-256:
`9d6dfe2f0c286431d6454befa9c554d0e7c87af5bb7320165c0318ce98483020`.
Raw E2E-log SHA-256:
`2893bdcd1276c7e220bfa949e43f69d2acab65017a4a2db22985616713d5f498`.
`cloud-evidence/AUDIT.json` binds 65 retained raw artifacts, including sources,
job log/spec/exit, compressed receipts, ledgers and partial-recovery evidence.

This audit did not replay discarded proof streams or freshly reconstruct the
CNFs. The cloud test uses a local directory store and 21 selected items, not
S3 or the proposed 386-item canary. Orphan release, spot-node bootstrap, live
budget stopping, and S3 behavior remain outside this evidence. Partial uploads
are tested by the producer's 20-second E2E setting; whether the selected AWS
canary actually exercises its 120-second upload path must be checked in that
run's receipts. A short batch alone cannot establish that coverage.

## Reproduction

Metadata only, from this checkout:

```sh
python3 -B research/problems/erdos-85-wip-01/h7_integrated_canary_review_20261008/check_metadata.py \
  --repository /path/to/repository-with-reviewed-commit --output /tmp/fresh-h7-metadata-review
```

Read-only cloud audit, with the original producer output still retained:

```sh
python3 -B audit_cloud.py --repository /opt/e85/wt/commit-797579e113ab
```

The latter prints a JSON evidence bundle; save its output to a new location.
Neither command launches a solver, Lean, AWS canary, or fleet.
