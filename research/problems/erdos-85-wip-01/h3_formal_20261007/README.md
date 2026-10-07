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

From the repository root, with the single shared Docker slot available:

```sh
LEAN_NUM_THREADS=1 LEAN_MEMORY_LIMIT=8192 LEAN_BUILD_TIMEOUT=10m LEAN_SKIP_CACHE=true ./proofs/scripts/docker-build.sh Proofs.Erdos85ThreeHighNativePairSearch
```

A cold dependency build may exceed this cap. The recorded final successful run
used a two-minute cap with already-built dependencies.

## Unverified finite pilot

`Erdos85ThreeHighNativeTerminalPilot.lean` is retained here, outside the default
`proofs/Proofs` build glob. Its proposed `native_decide` rejection theorem has
**not** compiled. The four-minute, one-thread, 8 GiB run reached the target
compiler process and timed out with exit 124. See `pilot-receipt.json` and
`pilot-timeout.txt`. The full pair is U representative 1, compact code `(6,6,15)`,
and secondary representative 15, which remains in the 261-pair full census.

To retry in an isolated worktree, copy this source to
`proofs/Proofs/Erdos85ThreeHighNativeTerminalPilot.lean`, ensure the Docker slot
is available, and use the exact command in `pilot-receipt.json`. Remove that
experimental copy afterward if it remains unverified. A successful native check
would add a native-computation axiom and must be reported separately from the
14 standard-axiom exports.

## Handoff

The stronger joint witness still needs transport through the retained compact
and orbit census. Remaining full/deficient finite rejections, the H3 pair
profile, and final stratum assembly are open. See
[`../H3_MACHINE_CHECK_FRONTIER_20261007.md`](../H3_MACHINE_CHECK_FRONTIER_20261007.md)
for existing coverage/pruning packages and the precise terminal mismatch.
