# H3 formal contribution, 7 October 2026

Four new library modules compile and export 14 theorems using only `propext`,
`Classical.choice`, and `Quot.sound`. They supply the distinct-neighbor condition
required by the Python H3 triple verifier, its graph witness and relabeling, a
sound terminal search, and a conditional finite-pair exclusion wrapper.
These standard-axiom structural results are conditional. The separate native
pilot below now rejects one concrete pair; no full H3 stratum exclusion follows.

The mathematical commits, in dependency order, are `55c9ceea2a1`,
`607d0e7ad6c`, `ad27935201e`, and `e6ebfb739d8`.
The Docker thread-limit fix is `34caae65a09`.

## Verified evidence

- `graph-receipt.json` / `graph-axioms.txt`: first four exports.
- `terminal-receipt.json` / `terminal-axioms.txt`: all 14 exports.
- Receipts record source, toolchain, manifest, and full local log hashes.
  Retained text files are axiom excerpts, not complete dependency logs.

These receipts record earlier Docker runs. Current verification uses the cloud
builder; Lean and Docker builds must not run on the Mac. The historical final
successful run used a two-minute cap with already-built dependencies.

## Verified native finite pilot

The pilot sources are retained here, outside the default `proofs/Proofs` build
glob. The split cloud pilot now has a **passing concrete rejection receipt**.
The original
four-minute, one-thread, 8 GiB run reached the target
compiler process and timed out with exit 124. See `pilot-receipt.json` and
`pilot-timeout.txt`. The full pair is U representative 1, compact code `(6,6,15)`,
and secondary representative 15, which remains in the 261-pair full census.

The later cloud run took 5,859 seconds on the target module and printed the
native rejection declaration, but failed on recursion depth in its `no_joint`
consumer. The consumer fix was then verified independently with an explicit
rejection hypothesis. `Erdos85ThreeHighNativeTerminalPilotCertificate.lean` now
holds the unchanged rejection computation; `Erdos85ThreeHighNativeTerminalPilot.lean`
imports it and applies the fixed consumer. The cloud runner in
[`../h3_cloud_u1r15_20261008/`](../h3_cloud_u1r15_20261008/) builds these separately
and preserves the first object if the second fails. Both modules passed in job
`20261008T024639-erdos85__h3-triple-formal-20261007-116600` at source
`bd75f1b58288bb94294825d9d1c58e009f1847c2`, finishing 8 October at 04:24:22 UTC.
The rejection took 5,844.03 seconds; the consumer took 9.57 seconds. Both report
exactly the standard three axioms plus
`Erdos85.NativeTerminalPilot.rejected._native.native_decide.ax_1_1`.
The consumer retains cross-domain and external-block-cap premises.
Complete source/log/receipt evidence and independently matched cloud object
hashes are in `../h3_cloud_u1r15_20261008/split-evidence/`.
This is one concrete pair; the native trust boundary is separate from the
standard-axiom structural exports.

## Handoff

The stronger witness transport and full-276/deficient-1554 census connections
are now verified in [`../h3_strong_census_20261008/`](../h3_strong_census_20261008/).
The full-261 connection is still building. Remaining finite rejections, the H3 pair
profile, and final stratum assembly are open. See
[`../H3_MACHINE_CHECK_FRONTIER_20261007.md`](../H3_MACHINE_CHECK_FRONTIER_20261007.md)
for existing coverage/pruning packages and the precise terminal mismatch.

The exact first-column decomposition is now cloud-verified in
[`../h3_first_column_20261008/`](../h3_first_column_20261008/): five additional
structural/conditional exports, standard axioms only. It permits independently
checking each first-column branch while requiring rejection of every candidate
before deriving the original pair rejection. The separate cloud diagnostic
found first-column candidate counts 15, 1, 36, 1, and 40 for the five pilot
pairs. The [second-column decomposition](../h3_second_column_20261008/)
adds four verified standard-axiom exports for a deeper split. The
[second-column diagnostic](../h3_second_column_inventory_20261008/)
finds 36 branches for Full U3/R3 and 40 for Deficient U26/R2; all pass both
prefix gates. These branches have not yet been individually timed or rejected.
No concrete branch rejection or measured speedup is claimed by this result.

A separate [first-column native pilot](../h3_first_column_pilot_20261008/)
has now rejected U1/R15's column `{0}` in 645.476 seconds, with one explicit
native-computation axiom. Its source/object/log provenance and exact axiom
report were independently audited. The other fourteen columns remain outside
that branch pilot. The independently verified whole-pair pilot above now covers
the full U1/R15 search.
