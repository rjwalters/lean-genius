# A6 residual batching from reviewed host leaves

This adapter takes a fixed49vertex H/E/S/P-high base, seven empty labels and a list of seven-mask pair-host assignments. Low labels can be arbitrary. It adds the supplied undirected P-empty edges and invokes the byte-identical accepted2120native residual checker. It preserves full ARC/UNKNOWN JSON; a row-negative receipt retains the empty vertex and node count, whose independent replay must regenerate that complete empty domain.

`api.check_hosts(base, empty_vertices, host_assignments, max_nodes=100000, deadline=None)` returns results in input order for the visited prefix. The deadline is absolute Python monotonic time, checked against the native clock epoch on import. An expired batch returns no visited results; a zero node cap returns UNKNOWN for each graph visited before the deadline. Each graph has its own counter. Callers must retain explicit unvisited indices and preserve the original family aggregate limit.

The adapter checks dimensions, mask/index bounds, base symmetry/looplessness, distinct empty labels and absence of preassigned P-low edges. The final checker validates the full a6 graph. Invalid inputs raise ValueError and never become negative certificates. The record stride uses size_t to avoid signed multiplication overflow.

On the adjacent-double fixture and11high/low relabellings,84exact compact/full-object comparisons match the accepted Python reference. Another72checks cover expiry, two-graph zero budgets, empty batches, duplicate empty labels, invalid host masks and selfloops. No new host family or residual family was searched. The counter and traversal are inherited unchanged from2120.

Compile `clang++ -std=c++17 -O2 -shared -fPIC batch.cpp -o batch.dylib`, then run `python3 test.py`. Source reference, fixtures and hashes are retained. Independent review is required before new-family use; this adapter itself proves no a6/H7/Lean/global exclusion.
