# Consume the full diagnostic certificates

Status: **Full259 compiled and independently audited PASS; Full258 remains blocked**.

Full259 build `20261008T085716-erdos85__h3-triple-formal-20261007-357296`
and audit `20261008T085913-erdos85__h3-triple-formal-20261007-359172`
both exited 0 at execution commit `9761aeec04b88e042d570f788a1fc7d7e8270bce`.
The composition took 4.722 s wall, 3.620 s user CPU, 1.458 s system CPU,
and 6,842,052 KiB peak RSS. The six exports have exactly the trust sets below.
No native rejection search was repeated, and no new computation credit was
created: the previously verified U3/R3 result is now formally connected.

Evidence is in `full259-evidence/`. RUN SHA-256:
`a0816150ca3127f6500f2caa6132bc6740f97946a42416d48513cef04c65409f`.
Full259 object SHA-256:
`3240bd42f42caecc7b2dadf7881b7ba0394b20db051f723122062404bde42b68`.
The object remains on the existing builder in `_build/full259-first/`;
the independent audit inspected its actual bytes. Raw build/audit job logs,
source bytes, individual receipt, dependency log and execution scripts are
retained. The first audit launch (job 358295, exit 1) failed before executing
Python because shell redirection into the Docker-owned directory was denied.
Its raw record is retained; the successful read-only audit printed to the
host job log instead. `AUDIT.json` is extracted from that log.

The U54/R20 job exited 124 at its two-hour cap, with no completed certificate.
Its raw timeout evidence is in `../h3_varied_pilot_20261008/FullU54R20-timeout-evidence/`.
Full259 can consume the already verified U3/R3 result using `--through Full259`.
This mode neither requests nor credits U54/R20. Full258 continues to require an independently
verified U54/R20 certificate. No native search should be repeated just to run
the Full259 connection.

`Full259.lean` consumes the independently audited U3/R3 native
certificate after the verified `Full260` reduction. `Full258.lean` proposes
consuming U54/R20 after that. The latter certificate is not yet verified;
its preparation does not authorize another native search. Its
actual-graph witness and exclusion theorem retain 258 rejection hypotheses.
Neither module would close the full H3 branch.

Both modules request six reports. The first three (membership, count,
input identity) must use standard axioms only. The fourth uses only the
matching diagnostic native axiom in addition to standard axioms. The last
two must have exactly the inherited native trust set: U1/R15 plus U3/R3 for
Full259, and those two plus U54/R20 for Full258. Existing rejection searches
must not be repeated.

For the default `--through Full258`, `check.py` requires a complete independently audited U54/R20 receipt hash
as `--full54-receipt-sha256`, matching committed evidence for that exact
case. It also requires the fixed audited Full260 and U3/R3 receipts. Before
any output or Lean build, it re-runs the read-only Full260 artifact audit,
including the entire full base/final census and the reused input objects.
It verifies the selected diagnostic source/log/receipt sets, exact native reports,
and certificate objects. Full259 requires only U3/R3 and rejects a supplied
FullU54 receipt argument. Missing, failed, or unaudited evidence
blocks the build. A timeout is not an acceptable result.

After that gate, the cloud-only checker verifies its dependency command
cannot target any imported input or certificate module, copies the four or five
hash-verified prerequisite objects beside the complete Proofs library,
and compiles Full259, followed by Full258 only when requested. Full and deficient census import
paths are kept separate. The checker preserves source/object/log hashes,
exact exports, and per-module wall/CPU/RSS evidence; it revalidates every
prerequisite before PASS. `audit.py` independently checks the actual compiled
inventory, source/object/log hashes, commands and six exact trust sets per
module; it revalidates prerequisite evidence and requires an explicit final
stage. Full259 must have no Full258 artifacts. Only Full259 has passed this
audit; Full258 has not been compiled or queued.

Arguments are `--prior-build` (the verified Full260 output),
`--prerequisites` (its staged full base/final/extra directory),
`--extra-objects` (the selected diagnostic certificates),
`--through Full259` or `--through Full258` (default),
`--full54-receipt-sha256` (required only for Full258), and
`--output` (a fresh directory). Run with `lake env python3` only inside
cloud Docker from `proofs/`. No automatic retry or submission occurs.

Local Python syntax, import, and six stage-selection/receipt-gate checks pass.
No Lean computation was performed locally.
