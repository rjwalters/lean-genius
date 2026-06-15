# Problem: Fermat Defect-One: are both signs realised for every n ≥ 3?

**Slug**: fermat-defect-one-oq-02
**Created**: 2026-06-15T06:15:07.078468+00:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \ge 3:\quad \Big(\exists x,y,z \in \mathbb{Z}_{>0},\ x^n + y^n - z^n = +1\Big)\ \wedge\ \Big(\exists x,y,z \in \mathbb{Z}_{>0},\ x^n + y^n - z^n = -1\Big)\ ?
$$

### Plain Language

The Fermat defect-one question asks, for each exponent n ≥ 3, whether the Diophantine equation |xⁿ + yⁿ − zⁿ| = 1 has solutions in positive integers realising BOTH the +1 and the −1 sign ("Level 3"). At n = 3 both signs occur; for general n a modular (congruence) obstruction might rule out one sign at specific exponents. The goal is to decide whether both signs are realised for every n ≥ 3, or to exhibit an exponent n where one sign is provably impossible.

### Why This Matters

Sharpens the gallery's Fermat defect-one development: separating the two signs is a concrete handle on near-misses to Fermat's equation and ties to Pillai / Fermat–Catalan circles of ideas.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
```

**Significance**: 6/10
**Tractability**: 5/10

## Known Results

### What's Already Proven

- Fermat's Last Theorem (Wiles): xⁿ + yⁿ = zⁿ has no positive solutions for n ≥ 3 — the defect-zero case.
- At n = 3 both signs of defect 1 are realised (gallery base result).

### What's Still Open

- Whether the +1 sign is realised for every n ≥ 3.
- Whether the −1 sign is realised for every n ≥ 3, or excluded by a congruence at some n.

### Our Goal

Decide "Level 3": both signs realised for all n ≥ 3, or find a modular obstruction excluding one sign at a specific n.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| fermat-defect-one | Parent gallery proof this open question extends |

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Small-n search is fully decidable and gives data quickly.
- Congruence obstructions (mod small primes / prime powers) are a finite, mechanisable search.
- A full positive answer is open and likely hard; partial/empirical results are tractable.

## Metadata

```yaml
tags:
  - number-theory
  - diophantine
  - fermat
  - open-conjecture
  - pillai
  - challenging
  - extension
  - gallery-extracted
  - seeker-selected
  - research
related_proofs:
  - fermat-defect-one
difficulty: high
source: gallery-gap
created: 2026-06-15T06:15:07.078468+00:00
```
