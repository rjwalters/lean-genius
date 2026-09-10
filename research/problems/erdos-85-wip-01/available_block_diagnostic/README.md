# Available-block prefix diagnostic

One bounded local run of each gate, using the same explicit U/R fixture and row order. These instrumented traversals stop after 5,000 attempted prefixes; terminal family search is disabled. They are runtime diagnostics, not kernel rejection certificates or complete searches. No additional runs are implied.

Both runs returned process code 0 and reached the prefix cap. Their counters and depth histograms are identical: 986 capacity failures, 1,928 deficit failures, 729 C4 failures, 904 external-cap failures, and zero leaves. No pruning improvement was observed on this prefix. The recorded traversal times are 6,981 ms for unfinished-block counting and 8,260 ms for available-block counting; these single runs do not establish a general timing comparison.

The available run had an explicit 30-second process deadline. Original JSON receipts and source scripts are retained unchanged, including their temporary command paths. To rerun from the integration worktree proofs directory, use `lake env lean --run ../research/problems/erdos-85-wip-01/available_block_diagnostic/available.lean` with an external deadline. The source hash file pins the principal gates used; it is not a complete transitive dependency manifest.
