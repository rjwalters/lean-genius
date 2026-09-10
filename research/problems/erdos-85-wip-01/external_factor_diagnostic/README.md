# External-block gate factorization diagnostic

One run compared 800 first-row prefix checks for each gate on the same fixture
used by the cached-C4 diagnostic (eight row choices repeated 100 times).
Both gates accepted all 800 checks. The fixed U gate evaluated to true.

| Gate | Time in measured loop |
| --- | ---: |
| Full E24 external-block cap | 982 ms |
| Cached fixed U cap plus cross-column cap | 94 ms |

This run measured about 10.4 times lower gate time after factorization. The
runtime process exited 0 in 5.56 seconds with a 30-second deadline. The
measured loops exclude process startup and fixed-U setup. This is a small
repeated-input microbenchmark; it does not establish full-search performance,
finite rejection, or kernel computation performance.

The accompanying Lean modules separately prove exact Boolean equality for
arbitrary U/R/cross data and preserve DFS witness completeness. The benchmark
uses Lean runtime evaluation only as a diagnostic, not as a proof oracle.

From `proofs`, reproduce with:

```sh
lake env lean --run ../research/problems/erdos-85-wip-01/external_factor_diagnostic/benchmark.lean
```

The raw log, original deadline receipt and source hashes are retained here.
