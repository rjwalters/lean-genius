# Consume the full diagnostic certificates

Status: **prepared, uncompiled, unqueued; U54/R20 remains a live diagnostic**.

`Full259.lean` proposes consuming the independently audited U3/R3 native
certificate after the verified `Full260` reduction. `Full258.lean` proposes
consuming U54/R20 after that. The latter certificate is not yet verified;
no build of this package is authorized by its preparation alone. Its
actual-graph witness and exclusion theorem retain 258 rejection hypotheses.
Neither module would close the full H3 branch.

Both modules request six reports. The first three (membership, count,
input identity) must use standard axioms only. The fourth uses only the
matching diagnostic native axiom in addition to standard axioms. The last
two must have exactly the inherited native trust set: U1/R15 plus U3/R3 for
Full259, and those two plus U54/R20 for Full258. Existing rejection searches
must not be repeated.

`check.py` requires a complete independently audited U54/R20 receipt hash
as `--full54-receipt-sha256`, matching committed evidence for that exact
case. It also requires the fixed audited Full260 and U3/R3 receipts. Before
any output or Lean build, it re-runs the read-only Full260 artifact audit,
including the entire full base/final census and the reused input objects.
It verifies both diagnostic source/log/receipt sets, exact native reports,
and the two certificate objects. Missing, failed, or unaudited evidence
blocks the build. A timeout is not an acceptable result.

After that gate, the cloud-only checker verifies its dependency command
cannot target any imported input or certificate module, copies the five
hash-verified prerequisite objects beside the complete Proofs library,
and compiles Full259 followed by Full258. Full and deficient census import
paths are kept separate. The checker preserves source/object/log hashes,
exact exports, and per-module wall/CPU/RSS evidence; it revalidates every
prerequisite before PASS. An independent final audit is still required.

Arguments are `--prior-build` (the verified Full260 output),
`--prerequisites` (its staged full base/final/extra directory),
`--extra-objects` (the two diagnostic certificates),
`--full54-receipt-sha256` (the later independently audited receipt), and
`--output` (a fresh directory). Run with `lake env python3` only inside
cloud Docker from `proofs/`. No automatic retry or submission occurs.

Local Python syntax, CLI import, and host-execution-refusal checks pass.
No Lean computation was performed locally.
