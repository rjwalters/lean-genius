# Consume the U1/R15 pilot in the full H3 census

Status: **source-only, uncompiled, unqueued**.

The cloud checker is prepared but has not been executed. The final census
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

The first three reports check membership, count, and input identity using
standard axioms only (or none). The last three are expected to retain the
one existing native rejection axiom, in addition to standard axioms. No new
native search is performed. No full H3 or deficient-branch exclusion follows.

Compilation uses the cloud-verified `Full261` and `CapacityReduction`
objects from the completed census. Reuse those objects and the already
verified native certificate; do not repeat the 97-minute rejection search.
The build must preserve source/object/log hashes and all six exact axiom
reports before this reduction is called verified. The source remains outside
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

The resulting output still needs an independent audit and an `AUDIT.json`
before it can serve as `--membership-evidence` for the two full varied
timing cases. The checker does not manufacture that approval itself.
