# Specialized C4-free generator: canonical-cache length repair

Status: tooling defect reproduced and local repair independently checked by
Sol2 (squad #40695, 2026-09-06). This does not establish enumeration completeness,
a missing graph, an order-64 exclusion, or any new Erdős 85 theorem.

## Source and defect

The source is [KGNoGPlus1Graphs](https://github.com/JorikJooken/KGNoGPlus1Graphs),
commit `35b35d189834c408f7adf166c51a487fd81f10c7`, file
`Code/generateRGGraphsNoGPlus1Cycle.c`. Its SHA-256 is
`662d9567e70eefd3105c52d8dcb1887a5f73ebf6ee7c255718a7baa54ac29b0b`.

`recursivelyAddEdges` allocates a canonical array with `nextIsolatedVertex`
words (line 427) and queries a splay tree indexed by edge count (line 430).
Cached nodes omit array length. The comparator (line 273) passes the incoming
array length to `memcmp`, including when a cached array is shorter. Edge count
does not determine the number of active vertices.

On the unmodified source, Clang AddressSanitizer with `WORDSIZE=128` and
`MAXN=128`, the small calibration `16 4 3` aborts:

```text
ERROR: AddressSanitizer: heap-buffer-overflow
READ of size 240
0 bytes after 224-byte region
allocated ... recursivelyAddEdges ... :427
... recursivelyAddEdges ... :430
```

This is a comparison of 15 incoming words with a 14-word cached allocation.
The subprocess returned -6 after approximately 0.15 seconds on macOS arm64.
Sol2 independently reproduced the same overread. This finding is distinct from
the earlier, unproved concern about canonical caching and branch-specific
eligible edges; no omitted completion was demonstrated by that concern.

## Repair and reproduction

The adjacent [patch](kg_generator_cache_length.patch) stores each cached array's
active order, initializes it when inserting a node, and compares orders before
comparing equal-length arrays. Comparator orientation agrees with the original
`memcmp`. The patched source SHA-256 is
`74b6dad5a98a6c33d5ec9fbd522e1d200f41db1476ac455f3a19c393560d4e5c`.

In a checkout of the pinned source, compile using its bundled nauty C sources
(the bundled static archives are not portable to this macOS host):

```sh
clang -std=gnu11 -O1 -g -fsanitize=address -fno-omit-frame-pointer \
  -DWORDSIZE=128 -DMAXN=128 -ICode -ICode/nauty2_8_8 \
  Code/generateRGGraphsNoGPlus1Cycle.c Code/read_graph/readGraph6.c \
  Code/nauty2_8_8/nauty.c Code/nauty2_8_8/nautil.c \
  Code/nauty2_8_8/naugraph.c Code/nauty2_8_8/schreier.c \
  Code/nauty2_8_8/naurng.c -o generator-asan
./generator-asan 16 4 3 > q4.stdout 2> q4.stderr
```

The original run reproduces the error. Apply the adjacent patch with
`git apply /absolute/path/to/kg_generator_cache_length.patch`, rebuild, and run
the same calibration. Our original and repaired runs each had a 20-second
subprocess timeout; both terminated within one second. The patched run returned
0, printed the matching completion marker, reported no ASan error, and emitted
exactly the previously independently verified graph6 line:

```text
O{dAH?_D?e@cAP?i?IO@b
```

Including its terminal newline, stdout SHA-256 is
`dee1a7f99693067aadb3fa52f164265fb876fb72cfb496738ec3bbf3a1b02db3`.
Sol2 independently reran both binaries and obtained the same comparison.
The graph has 16 vertices, degree 4 everywhere, and every pair has at most one
common neighbor; its structural isomorphism to the classified q4 graph was
checked independently of the generator before this repair.

## Evidence limits

The repaired small run checks this memory repair and the calibration output;
it does not prove correctness of all pruning or global exhaustiveness.
No order-64 run was started with the repair. The earlier unmodified `64 8 3`
diagnostic ended `UNKNOWN_TIMEOUT` after 30.007 seconds, with no completion
marker and no emitted graph. That status remains UNKNOWN.

For future evidence intake, exit 0 alone is insufficient: the upstream program
also exits 0 when rejecting degrees above its hard cap of 15. Require the
completion marker matching the requested parameters, and a separate coverage
audit before treating empty output as a nonexistence certificate. Timed runs
must preserve stdout (the original writer lacks an explicit flush).
