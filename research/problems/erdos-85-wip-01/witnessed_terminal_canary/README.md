# Explicit-reason terminal certificate

This rechecks the original terminal_canary completion using explicit common-neighbor
reasons for discarded triples. It proves the same seven facts, including literal
adjacency equality, cross-domain membership, external block cap and no joint witness.
It does not reject an additional completion or establish any pair coverage.

The1608 canonical triples have1520 conflict reasons and88 kept reasons. Each conflict
checks two distinct vertices in the triple and their common neighbor. Kept reasons
check membership in the supplied list. The generic checker rejects a too-short reason
list, so a missing entry cannot skip a candidate. It proves the original initial-cover
condition used by the selected-separated certificate.

The retained ordinary-kernel compile finished rc0 in40.61s, with seven standard-axiom
exports or subsets. The previous certificate's retained compile took60.17s. These are
single local measurements of the full checks and elaboration, not general timing
bounds. The checker is proved sound independently of these measurements.

From `proofs`, reproduce the source in a separate location with:

```
python3 ../research/problems/erdos-85-wip-01/witnessed_terminal_canary/generate.py --output /tmp/witnessed-canary.lean
lake env lean /tmp/witnessed-canary.lean
```

`shapes.jsonl` was exported by `lake env lean --run Shapes.lean` from the exact Lean
canonical candidate lists. Regenerating that export is optional: the certificate
checks against the actual lists, so incorrect external shape data cannot establish
an invalid cover. Python generation and diagnostic output are not proof axioms.
