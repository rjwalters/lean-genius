# Problem: Is the factor-of-2 constant in `szemeredi_implies_fk` tight?

**Slug**: szemeredi-regularity-oq-02-oq-02
**Created**: 2026-07-04T12:34:40-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Szemerédi } \varepsilon\text{-regular partition} \;\Rightarrow\; \text{Frieze–Kannan}
\ C\varepsilon\text{-cut-approximation, with } C = ?
$$

The current formalization proves this with $C = 2$. Is $C = 1$ achievable, or is $2$ tight?

### Plain Language

A Szemerédi $\varepsilon$-regular partition of a graph controls edge densities between most
pairs of parts. The Frieze–Kannan (weak) regularity condition instead controls the global
cut norm. The gallery entry proves that Szemerédi regularity implies FK cut-approximation
with an $\varepsilon \to 2\varepsilon$ loss. This problem asks whether the constant $2$ is
an artifact of the proof (and can be pushed to $1$) or is genuinely necessary.

### Why This Matters

Sharp constants in regularity transfer lemmas matter for downstream quantitative bounds
(counting lemma error terms, algorithmic sampling sizes). Resolving whether $2$ is tight
either improves the gallery bound or records a matching lower-bound construction, both of
which strengthen the `szemeredi-regularity-oq-02` entry.

## Known Results

### What's Already Proven

- `szemeredi_implies_fk` with constant $2$ — the current gallery entry.
- FK weak regularity is strictly weaker than Szemerédi regularity (the converse needs extra hypotheses) — classical Frieze–Kannan (1999).

### What's Still Open (for this formalization)

- Whether a joint estimate of the two small-set contributions yields constant $1$.
- If not, a small explicit graph/partition witnessing that constant $< 2$ fails.

### Our Goal

Either (a) reprove `szemeredi_implies_fk` with $C = 1$ via a joint bound on the two error
contributions, or (b) construct and formalize an example forcing $C \ge c > 1$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| szemeredi-regularity-oq-02 | parent entry proving the constant-2 bound | cut norm, regular partitions |
| unit-distance-independence-oq-04 | extremal combinatorics constant-chasing | counting, density arguments |

## Initial Thoughts

### Potential Approaches

1. **Joint small-set bound**: the current proof bounds $|e|\le \varepsilon|P||Q|$ and
   $d|A||B|\le \varepsilon|P||Q|$ separately, summing to $2\varepsilon$. Treat the signed
   discrepancy $|e - d|A||B||$ directly to avoid double counting.
   - Why it might work: the two terms overlap; a single triangle-inequality step may suffice.
   - Risk: the small-set and regular-pair cases may need different constants that recombine to $2$.

2. **Lower-bound construction**: half-density random-like bipartite blocks where the cut
   discrepancy is close to $2\varepsilon$, formalized as a finite example.
   - Why it might work: pins tightness concretely and is Lean-checkable on finite graphs.
   - Risk: finding a clean finite witness rather than an asymptotic family.

### Key Difficulties

- Bookkeeping over the irregular-pair exceptional set within the cut-norm sum.
- Formalizing the cut norm inequality manipulations in Lean without losing the constant.

### What Would a Proof Need?

- Key lemma 1: a joint bound $|\sum_{P,Q}(e_{PQ} - d|P||Q|)| \le C\varepsilon n^2$ with explicit $C$.
- Key lemma 2 (for tightness): a finite graph where the cut discrepancy $\approx 2\varepsilon n^2$.
- Technical requirements: the existing cut-norm and regular-partition definitions from the parent entry.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The scope is a single explicit constant in an already-formalized lemma.
- Both directions (improve to 1 / show 2 tight) are concrete and finite-flavored.
- Builds directly on the existing `szemeredi-regularity-oq-02` Lean development.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1 week
- If hard: 2-3 weeks (if a lower-bound family is needed)

## References

### Papers
- A. Frieze, R. Kannan, "Quick approximation to matrices and applications" (1999) — weak regularity and cut norm.
- E. Szemerédi, "Regular partitions of graphs" (1978) — the regularity lemma.

### Online Resources
- https://en.wikipedia.org/wiki/Szemer%C3%A9di_regularity_lemma — statement and variants.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Regularity` — regular partitions and the regularity lemma scaffolding.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - szemeredi
  - regularity
  - frieze-kannan
  - cut-norm
related_proofs:
  - szemeredi-regularity-oq-02
  - unit-distance-independence-oq-04
difficulty: medium
source: proof-suggestion
created: 2026-07-04T12:34:40-07:00
```

**Significance**: 5/10
**Tractability**: 5/10
