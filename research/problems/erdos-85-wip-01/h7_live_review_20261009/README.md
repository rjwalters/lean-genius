# H7 live review, 2026-10-09

Codex read-only review of worker/controller launch pin
`729127aa817263475e7aa0c65c3db34a65da3389`. No live fleet/controller was
changed, and no local Lean, SAT, checker or native compilation was run.

**Receipt metadata and canary terminal checks pass. Full canary acceptance is
pending independent reconstruction of the v2 leaf CNF identities on cloud.**
The existing builder was stopped at capture. Its state has not been changed.

## Results

* Canary #3 has exactly 10 certified rows / 394 items (2 covers and 392 leaves).
  These are 2 cover rows, F6_t14 head rows h0000/h0001, and 6 tail rows
  b0000 = leaves 1024–1087; the historical v1 acceptance package remains unchanged.
* Both packed and unpacked hashes match all 10 ledgers. Item IDs/ranges,
  approved binaries, execution pin, input and manifest pins, 6000 MB heap,
  7200 s cap, solver UNSAT exit 20, checker positive verification/exit 0,
  proof sizes/hashes, and ledger totals pass the metadata audit.
* Three nodes supplied accepted receipts. All 105 carried receipts match
  archived partial receipts with every field except the added `carried` flag
  preserved. Their hosts also match captured pinned bootstrap/tool records.
* Retained cover metadata matches both cover receipts and frozen input cover
  hashes; listed CNF/LRAT object sizes match. Raw retained proof bytes have
  **not** been independently downloaded/rehashed or rechecked here.
* Canary fleet `fleet-d57fe55e-20a4-4cb1-ba3e-3562f2608b82` is `deleted`;
  last worker `i-0da45fb9523dc10e3` and controller `i-06d91affb3e08f4e0`
  are `terminated`. No live canary worker remains in the captured tag query.
  Only STOP and completion STOP-CAUSE exist under the canary control prefix.
* Pure metadata validation reproduces manifest v2 SHA
  `0deb438f9bd7f5cfb840fd799330e6b80e70a043b21f96fcf0737c826515290c`:
  12,605 distinct rows, 28 covers and every one of 377,776 leaves exactly once.
  Five pinned mocked reservation/idle-slot tests pass. Thirteen dangerous
  receipt mutations are rejected by the independent item validator.
* At the captured main report (03:19:19 UTC), 283 batches / 1048 items were
  certified, three workers were live, and estimated spend was $3.56 against
  the $160 stop threshold. This is a historical snapshot, not live status.
* The main pass was launched before canary #3 completed, using the explicit
  manifest-pass override. These postlaunch checks do not establish that a
  prelaunch acceptance gate passed.

None of these external receipts discharges the Lean H7 hypothesis. H1/H7
remain explicit in the accepted H3-closed capstone; this is not a full-paper
completion or publication decision.

## Controller defect reported to Claude (room 53145–53149)

At the launch pin, a worker ALARM writes STOP. `one_pass` then reports
`STOP marker present; controller exits` without deleting the maintain fleet
or terminating the pass's workers. The host loop sees an action and powers
itself off. The maintain fleet can subsequently replace drained workers
without a budget watcher, until its expiry.

`reproduce_stop.py` extracts only the pinned `one_pass` AST into a fully
mocked environment. `STOP-REPRO.json` records zero fleet-stop calls and no
cloud calls. The pinned test actually asserted that the old `stop` helper
was not called, because that helper rewrites STOP. The fix must preserve
existing STOP/STOP-CAUSE/ALARM evidence **and** tear down the pass's fleet.

Claude owns the fix and live deployment. His initial working diff adds a
separate marker-preserving teardown helper. Follow-up review requested that
it also inspect API-level failures, scope actions to this pass, and retry
rather than exit on incomplete teardown. AWS documents separate successful
and unsuccessful deletion results in [DeleteFleets](https://docs.aws.amazon.com/AWSEC2/latest/APIReference/API_DeleteFleets.html).
The first proposed diff discarded that response. No fix acceptance or live
rollout is claimed in this snapshot.

The v2 idle-slot retry is sound in the reviewed mocked cases: absent
ledgers keep slots waiting for orphan release, with STOP/lifetime checks on
retry and reservation release in `finally`. Drained-pass handling calls
fleet stop only once all manifest IDs have CERTIFIED/INCOMPLETE terminal
ledgers; this is distinct from successful full certification. The configured
6 GB checker heap fits 48/64 slots under the node memory calculation; this
arithmetic is an allocation policy, not a measured peak-RSS guarantee.

## Evidence and reproduction

`snapshot1/CAPTURE.json` pins 76 captured files (including ignored `.log`
files). `supplement1/CAPTURE.json` pins cover metadata and builder status.
Source snapshots come directly from the launch commit. `inputs.json` is
only the frozen metadata (SHA `f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c`).
The formula freight and raw LRAT streams are not duplicated here.

From this directory:

```sh
python3 -B audit_receipts.py --inputs inputs.json
python3 -B verify_metadata.py
python3 -B reproduce_stop.py
```

`RECEIPT-AUDIT.json`, `METADATA-TESTS.log`, and `STOP-REPRO.json` retain the
outputs. `canary_accepted`, `full_campaign_verified`, and
`lean_evidence_discharged` deliberately remain false.

`prepare_inputs_v2.py` is ready for a bounded cloud-only metadata run against
`/home/ec2-user/h7camp/inputs` (one worker, 2 GiB, 120 s is the proposed bound).
It independently reconstructs formula bytes/hashes and ordered leaf units
without importing the campaign generator or invoking any solver/checker.
Its Linux guard prevents accidentally doing the formula work on the Mac.
It has been syntax checked, but the real v2 input run is pending. Preserve
its expected-output file and execution receipt, then rerun `audit_receipts.py
--inputs inputs.json --expected EXPECTED-v2.json`. Final acceptance still
needs explicit review of the evidence and the controller fix; the script
will not silently promote operational checks into Lean evidence.
