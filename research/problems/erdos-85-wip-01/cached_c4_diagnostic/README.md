# Cached C4 gate diagnostic

One full-U fixture uses masks `[129,34,34]` and permutation `(1 2)`; R uses three matching edges, no N-to-far edges, and the far edge. Lean runtime preflight previously returned U C4-free and R-domain membership true.

Each script checks the eight first-row choices 100 times. Baseline C4 took 21,977 ms and cached C4 took 1,279 ms; both accepted all 800. Capacity took 125 ms and deficit feasibility took 144 ms in each run. This roughly 17.2-fold ratio concerns this gate and fixture only. It does not measure full-search speedup or prove any exclusion. Both processes terminated with exit code 0.

Run from the integration worktree `proofs` directory with `lake env lean --run ../research/problems/erdos-85-wip-01/cached_c4_diagnostic/baseline.lean` (or `cached.lean`). Original runs used a 30-second external process-group deadline; apply the same bound when reproducing. Timings inside the scripts exclude import/setup time; wall times in receipts include it.

Exact Boolean equality is proved in `Erdos85EncodedC4CachedRows.lean`. The source was uncommitted when measured; provenance includes its SHA-256. The full search on this fixture had earlier reached its deadline without returning a Boolean result.
