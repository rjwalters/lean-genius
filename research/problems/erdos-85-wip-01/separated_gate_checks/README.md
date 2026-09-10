# Separated-set resolution gate checks

The gate greedily chooses residual vertices so that each listed candidate triple
contains at most one chosen vertex. Any resolution with six triples must cover
this chosen set, so its cardinality cannot exceed six. The generic soundness
proof does not depend on the greedy set being largest possible.

`checks.lean` verifies two concrete cases with ordinary kernel `decide`:

- Six disjoint triples on eighteen labels pass.
- Triples sharing labels 7 and 8 cover all eighteen labels but fail the gate.
  This demonstrates a rejection that simple residual coverage cannot detect.

From `proofs`, run:

```sh
lake env lean ../research/problems/erdos-85-wip-01/separated_gate_checks/checks.lean
```

Both checks compiled with only `propext`, `Classical.choice`, and `Quot.sound`.
They are small constructed examples, not actual Erdős-85 candidate rejection
certificates or performance benchmarks. The main library separately proves
that the added gate preserves every retained valid resolution family.
