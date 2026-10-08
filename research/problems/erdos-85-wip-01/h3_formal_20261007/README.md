# H3 formal contribution, 7 October 2026

Four new library modules compile and export 14 theorems using only `propext`,
`Classical.choice`, and `Quot.sound`. They supply the distinct-neighbor condition
required by the Python H3 triple verifier, its graph witness and relabeling, a
sound terminal search, and a conditional finite-pair exclusion wrapper.
**No concrete pair or H3 stratum exclusion is established by this package.**

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

## Unverified finite pilot

The pilot sources are retained here, outside the default `proofs/Proofs` build
glob. There is **no passing concrete rejection receipt**. The original
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
and preserves the first object if the second fails. A successful native check
would add a native-computation axiom, separately from the 14 standard-axiom exports.

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
pairs; the two one-candidate cases would need a deeper split for parallelism.
No concrete branch rejection or measured speedup is claimed by this result.
