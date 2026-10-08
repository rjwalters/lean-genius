# Consume the U1/R15 pilot in the full H3 census

Status: **cloud PASS and independently audited; 260 rejection hypotheses remain open**.

Cloud job `20261008T062957-erdos85__h3-triple-formal-20261007-260985`
completed with exit zero at 06:31:44 UTC, at commit `8cf6b79ce2da127d9a80383f8a019947fff0d58d`,
with 32 GiB, one Lake thread, and a 30-minute cap. The final census
now passes its independent artifact audit (342 modules, 1,077 reports).
`census-staging.json` records hash-verified copies of the complete base and
final output directories in this worktree, re-audited after copying. The
three extra objects also passed their existing-evidence checks. No native
search or Lean compilation was performed during staging.

The U1/R15 native rejection and its original no-joint consumer are independently
verified in `../h3_cloud_u1r15_20261008/split-evidence/`. `Full260.lean`
connects that exact certificate to the representative in the final full census,
erases `(1,15)`, and proposes the resulting 260-pair witness and conditional
exclusion theorems. The other 260 rejections remain explicit hypotheses.

All six reports passed. The first three check membership, count, and input
identity using standard axioms only. The last three retain exactly the one
existing native rejection axiom, in addition to standard axioms. No new
native search is performed. No full H3 or deficient-branch exclusion follows.

Compilation uses the cloud-verified `Full261` and `CapacityReduction`
objects from the completed census. Reuse those objects and the already
verified native certificate; do not repeat the 97-minute rejection search.
The build preserves source/object/log hashes and all six exact axiom
reports. The source remains outside
the library's default build glob.

`check.py` takes `--base-build`, `--final-build`, the independently audited
`--final-receipt-sha256`, `--extra-objects`, and a fresh `--output`. Run it
with `lake env python3` only inside cloud Docker from `proofs/`. It checks
the entire base and final source/log/object inventories with the existing
strict census auditor before compiling. The original full-base receipt is
pinned to `9924e45dfa932bae6af3607eb7de97e4b77d590366bf8d4bb9eaaf8de480236f`.
No final receipt hash is assumed while the census remains running.

The extra-object directory must contain these three previously verified
objects (flat filenames ending in `.olean`):

- `Erdos85ThreeHighNativeTerminalPilotCertificate`, from the U1/R15 pilot.
- `Erdos85ThreeHighPilotFullU3R3Inputs`, from the varied input preflight.
- `Erdos85ThreeHighPilotFullU54R20Inputs`, from the same preflight.

Their hashes and evidence are checked against the pinned, audited prior
receipts. They are copied beside the complete library `Proofs` namespace;
an existing different object is refused. The dependency build explicitly
refuses to target these imported modules. This avoids both another native
search and shadowing the library with a partial `Proofs/` directory.

The checker first compiles `FullMembership.lean` from the varied pilot
package, requiring its four membership/input reports to use standard
axioms only. It then compiles `Full260.lean`, checking all six exports and
the exact existing native axiom on the last three. It retains individual
timing, CPU/RSS, source/object/log hashes, the current plan, and the two
reused input-module receipts with their provenance. All prerequisite
artifacts are validated again before PASS. There is no automatic retry.

`audit.py` independently checked the original cloud objects, sources, logs,
commands, prerequisite inventories, reused input receipts, and exact exports.
Its PASS receipt is retained as `evidence/AUDIT.json`; the evidence directory
can now serve as `--membership-evidence` for the two full varied timing cases.
Both selected-case preflights also passed locally without invoking Lean.
The checker does not manufacture that approval itself.

FullMembership compiled in 7.370 seconds (6,965,080 KiB maximum RSS);
Full260 compiled in 5.826 seconds (6,907,472 KiB maximum RSS).
The four membership/input exports use standard axioms only.
The original source comment saying it had not yet passed is retained
byte-for-byte with the compiled source; this receipt records its later PASS.
