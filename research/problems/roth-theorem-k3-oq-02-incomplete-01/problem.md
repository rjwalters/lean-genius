# Problem: Roth's Theorem via Triangle Removal Lemma

**Slug**: roth-theorem-k3-oq-02-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
r_3(N) = o(N) \text{ via Ruzsa-Szemerédi triangle removal}
$$

### Plain Language

Alternative proof of Roth's theorem using triangle removal. The Ruzsa-Szemerédi RS graph construction encodes 3-APs as triangles. 1 sorry at line 339 for the main reduction.

### Why This Matters

See `src/data/proofs/roth-theorem-k3-oq-02/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `roth-theorem-k3-oq-02` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

Apply quantitative triangle removal lemma with δ' = δ/18. For the RS graph on 3N vertices with ≤6N² triangles, TRL gives edge removal set of size ≤δN²/2. But |R| ≥ δN² by AP-free assumption — contradiction.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem-k3-oq-02` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - combinatorics
  - roth
  - triangle-removal
  - szemeredi
related_proofs:
  - roth-theorem-k3-oq-02
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 6/10
