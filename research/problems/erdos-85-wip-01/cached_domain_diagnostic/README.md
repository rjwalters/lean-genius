# Cached row-domain diagnostic

The cached traversal materializes all 15 root-pruned row lists with `Array.ofFn` once, inside the timed section. The baseline recomputes each row list when its depth is visited. The original bounded diagnostic scripts and JSON receipts are retained unchanged. Both stop after 5,000 attempted prefixes; terminal family search is disabled. Both processes returned code 0 within their explicit 30-second deadlines.

Both traversals report identical counters and depth histograms, with zero leaves. Recorded traversal time was 8,260 ms baseline and 6,014 ms cached. This single pair suggests a useful optimization but does not establish a general speedup or exhaustive rejection. The scripts instrument the DFS structure; they are not kernel certificates and do not themselves prove equivalence of production searches.

From the integration worktree `proofs` directory, use `lake env lean --run ../research/problems/erdos-85-wip-01/cached_domain_diagnostic/cached.lean` under an external deadline. Receipts retain the original temporary paths. `source-hashes.json` pins the retained scripts and production cache module, not the complete dependency graph.
