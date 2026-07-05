# Problem: Erdős #1162 OQ-04

## Statement

### Plain Language

Erdős #1162 asks for an asymptotic formula for f(n) = the number of subgroups of
the symmetric group S_n. **OQ-04** asks for the analogous result for the
alternating group A_n: give the asymptotic of g(n) = #{subgroups of A_n}.

### Answer

log g(n) = (1/16 + o(1)) n²  — the same leading constant as S_n.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
parent: erdos-1162
tags:
  - erdos
  - group-theory
  - symmetric-group
  - alternating-group
  - enumeration
  - asymptotic
```

## Why This Matters

1. **Completes the Erdős–Turán picture** — the alternating group is the natural
   next case after S_n; the same 1/16 constant confirms the phenomenon is driven
   by elementary abelian 2-subgroups, not by odd permutations.
2. **Illustrates a clean proof-transfer pattern** — g(n) ≤ f(n) gives the whole
   upper asymptotic for free; only a lower bound is new input.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-1162 | Parent: S_n subgroup-count asymptotic (RDT 2025) |

## References

- [RoTr25] Roney-Dougal, Tracey, "The number of subgroups of the symmetric
  group" (2025).
- [Py93] Pyber, "Enumerating finite groups of given order" (1993).
