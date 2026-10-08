# Independent H7 canary acceptance preparation

Status: preparation only. No canary receipt, fleet transition or full-campaign
result is accepted here yet. Claude requested the read-only review in squad
message 53115 after reporting Robb's canary/full-run authorization.

The canary is exactly two covers (`F6_t14`, `F7_t10`) and leaves 0–63 of
`F6_t14`, `F6_t18`, `F7_t10`, `F7_t13`, `F8_t0`, `F9_t0`: eight batches,
386 items. `prepare_inputs.py` independently reconstructs their CNF hashes
and ordered leaf units from the previously pinned input bytes on the existing
cloud builder. It imports no campaign generator and runs no solver or Lean.
Its output is an expected-input ledger, not evidence of completed checks.

`validate.py` checks captured per-batch ledgers against the exact selected
items, execution commit, instance, full manifest and input pins. It requires
matching compressed/uncompressed transport hashes, both binary pins, exact
CNF identity, solver UNSAT evidence and checker verification, and reconciles
ledger counts with the item records. A timeout or exhausted checker heap
produces `CANARY_RESIDUAL_REVIEW_REQUIRED`; it never receives certification
credit from an `INCOMPLETE` label. The caller must independently decompress
the captured results and preserve the original bytes and AWS observations.

The separate transition check requires a terminated canary instance and
quiescent fleet, no live campaign instances, no `control/STOP` or ALARM key,
reconciled canary receipts, observed partial uploads and bootstrap selftests,
and the intended full manifest with the approved $160 controller stop.
These observation fields must come from the actual pinned launch and captured
cloud state. Supplying a synthetic dictionary is only a unit test.
An already fulfilled one-time `request` fleet may remain `active`: AWS states
that this type does not replenish interrupted instances. The check accepts
that case without demanding fleet deletion; an active `maintain` fleet does
not get this exception. See the [AWS fleet request-type documentation](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-fleet-request-type.html).

The existing controller leaves STOP persistent after manual, budget or alarm
stops; a new launch-template version does not remove it. These scripts do not
remove that marker, change cloud state or authorize a launch. An outstanding
marker must be classified and its authorized transition documented separately.

`test_validate.py` uses tiny synthetic receipt/transition fixtures. Passing
tests grant no real canary, full-campaign, or Lean theorem verdict. The actual
collection and review will bind the frozen launch commit and canary instance
and fleet identifiers when they are available.
