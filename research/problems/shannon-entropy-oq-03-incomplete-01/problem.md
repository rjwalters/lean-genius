# Problem: Strong Subadditivity of Shannon Entropy

**Slug**: shannon-entropy-oq-03-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
H(X,Y,Z) + H(Y) \leq H(X,Y) + H(Y,Z)
$$

### Plain Language

The deepest classical entropy inequality. All infrastructure is in ShannonEntropySSA.lean; only the main theorem at line 303 remains as `sorry`.

### Why This Matters

See `src/data/proofs/shannon-entropy-oq-03/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `shannon-entropy-oq-03` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

Express deficit as I(X;Z|Y) = Σ_y p(y) D(p(x,z|y) || p(x|y)·p(z|y)) ≥ 0. Use KL divergence non-negativity (Gibbs inequality / Real.log_le_sub_one_of_le).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `shannon-entropy-oq-03` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Medium

## Metadata

```yaml
tags:
  - information-theory
  - entropy
  - shannon
  - strong-subadditivity
related_proofs:
  - shannon-entropy-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 7/10
