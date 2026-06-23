# Problem: Fix ShannonEntropy

## Statement

### Plain Language
Use the now-working `ShannonEntropy.lean` machinery (post PR #16334, which
proved `strong_subadditivity`) to discharge the `fano_inequality` axiom in
`ShannonChannelCoding.lean`. This is the "integration plan" described in the
parent OQ-02-OQ-01 PR #17189.

### Formal Statement
Produce a theorem with the exact signature of
`InformationTheory.ChannelCoding.fano_inequality` (in
`proofs/Proofs/ShannonChannelCoding.lean`) so that the axiom can be replaced
by an `:=` reference. Required:

* uses `InformationTheory.conditionalEntropy` (not the self-contained
  `FanoInequality.conditionalEntropy` in OQ-03);
* no cardinality hypothesis (the axiom does not have one);
* `Real.log` convention `Real.log 0 = 0`.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - axiom-elimination
  - information-theory
```

**Significance**: 6/10 (one of 4 axioms in the parent gallery entry)
**Tractability**: 6/10 (integration plan is fully specified)

## Why This Matters

1. **Axiom elimination** - drops `axiomCount` for `shannon-channel-coding`
   from 4 to 3 (or 4 → 3 once the parent file actually swaps axiom for
   theorem).
2. **Unlocks downstream** - `channel_coding_converse` depends on Fano; this
   strengthens that derivation chain.
3. **Concrete, well-scoped** - the math is done (OQ-03 already proves the
   |α|≥2 case); the remaining work is API plumbing.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `shannon-channel-coding-oq-02-oq-01` | Parent — sets up bridge file |
| `shannon-channel-coding-oq-03` | Provides `fano_theorem` (|α|≥2 case) |
| `shannon-channel-coding-oq-04` | Binary entropy `h` and `h_nonneg` |
| `shannon-entropy` | `InformationTheory.conditionalEntropy` definition |
