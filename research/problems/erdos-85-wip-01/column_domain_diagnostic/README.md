# Column-domain construction diagnostic

One executable Lean comparison on secondary representative 14. Baseline constructs
all subsets of15 U labels; compact construction uses216 optional block choices.
Both return column-list sizes `[1,75,75,75,125,125,125,125]`.

The retained run measured2525ms for baseline construction and19ms for compact
construction, including printing the size list in each interval. This is one local
measurement, not a whole-search speedup or rejection result. Equal sizes alone
are not a proof of equal lists. The separate column-completeness and DFS-soundness
proofs preserve actual witnesses; they do not assert identical traversal order.

Run from `proofs` with `lake env lean
../research/problems/erdos-85-wip-01/column_domain_diagnostic/Benchmark.lean`.
No cross matrices or resolution families are enumerated by this diagnostic.
