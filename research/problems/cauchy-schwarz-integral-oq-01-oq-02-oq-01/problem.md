# Problem: cauchy-schwarz-integral-oq-01-oq-02-oq-01

## Statement

### Plain Language
The parent entry "Riesz–Thorin Interpolation from Hölder's Inequality"
(cauchy-schwarz-integral-oq-01-oq-02) assumes the **Hadamard three-lines lemma**
as an axiom. This open question asks whether that analytic step can be discharged
in Lean — proved as a theorem rather than assumed.

## Classification

```yaml
tier: B
significance: 7
tractability: 8
tags:
  - complex-analysis
  - hadamard-three-lines
  - interpolation
  - riesz-thorin
  - axiom-discharge
```

## Status

**RESOLVED (verified, 0 axioms).** `hadamard_three_lines` is proved as a theorem in
`Proofs/CauchySchwarzIntegralOQ01OQ02OQ01.lean`, derived from Mathlib's
`Complex.HadamardThreeLines`. See the gallery entry of the same slug.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cauchy-schwarz-integral-oq-01-oq-02` | Parent: assumes the three-lines lemma as an axiom |
