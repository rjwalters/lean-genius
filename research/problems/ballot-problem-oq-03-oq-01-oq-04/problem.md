# Problem: Catalan Number Recurrence from the Ballot Theorem

**Slug**: ballot-problem-oq-03-oq-01-oq-04
**Created**: 2026-04-23T11:40:52+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
C_0 = 1,\quad C_{n+1} = \sum_{k=0}^{n} C_k \cdot C_{n-k}
$$

Prove the Catalan recurrence $C_{n+1} = \sum_{k=0}^{n} C_k C_{n-k}$ in Lean 4 via the ballot theorem / reflection principle: decompose a Dyck path of semilength $n+1$ at its unique first return to 0.

### Plain Language

The Catalan numbers $C_n = \frac{1}{n+1}\binom{2n}{n}$ count Dyck paths, triangulations, and hundreds of other combinatorial objects. Their defining recurrence comes from splitting a Dyck path at the point where it first returns to the $x$-axis, yielding two independent shorter Dyck paths.

The `ballot-problem-oq-03-oq-01` gallery entry recently proved results using the LGV lemma and reflection principle. This extends those techniques to derive the Catalan recurrence formally.

### Why This Matters

The Catalan recurrence is one of the most fundamental identities in combinatorics. Formalizing it via ballot theorem / reflection connects two major gallery entries and provides a reusable path-counting technique in Lean 4.

## Known Results

### What's Already Proven

- `ballot-problem`: ballot theorem, reflection principle
- `ballot-problem-oq-03-oq-01`: LGV lemma, `card_SYT_twoRectYD` via reflection
- Mathlib: `Nat.catalan`, bijection with Dyck paths

### What's Still Open

- Formal derivation of the Catalan recurrence from the ballot problem first-return decomposition

### Our Goal

Formalize the Catalan recurrence using the decomposition: a Dyck path of length $2(n+1)$ splits at its first return to 0 into two shorter Dyck paths, giving the convolution recurrence.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ballot-problem` | Ballot theorem, reflection principle | Path counting, reflection |
| `ballot-problem-oq-03-oq-01` | LGV lemma application | Lindström-Gessel-Viennot |

## Initial Thoughts

### Potential Approaches

1. **Decomposition at first return**: A Dyck path of semilength $n+1$ has a unique first return to 0 at step $2k+2$; strip the first up/last down step to get Dyck paths of semilengths $k$ and $n-k$.
   - Why it might work: Clean bijective argument; ballot theorem provides counting
   - Risk: Need to formalize the bijection carefully in Lean 4

2. **Generating function approach**: Derive $C(x) = 1 + x C(x)^2$ and extract the recurrence.
   - Why it might work: Algebraic manipulation
   - Risk: Formal power series in Lean 4 may be cumbersome

### Key Difficulties

- Formalizing "first return to 0" as a well-defined bijection in Lean 4
- Connecting lattice path count to the ballot theorem setup in the gallery
- Avoiding circular dependencies with Mathlib's `Nat.catalan`

### What Would a Proof Need?

- Key lemma 1: Every Dyck path of semilength ≥ 1 has a unique first return to 0
- Key lemma 2: The decomposition is a bijection onto pairs of shorter Dyck paths
- Technical: `Finset.card`, path enumeration, `Finset.card_biUnion`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical argument, well-understood
- Ballot problem gallery provides relevant infrastructure (reflection, path counting)
- Main challenge: formalizing the first-return bijection in Lean 4
- Mathlib has `Nat.catalan` for stating the result

**Estimated Effort**:
- Exploration: 1 day (check Mathlib catalan API, ballot gallery code)
- If tractable: 3-4 days (formalize bijection and counting)

## References

### Papers
- Bertrand, J. (1887), "Solution d'un problème" — ballot problem
- Catalan, E. (1838), "Note sur une équation aux différences finies"

### Mathlib
- `Mathlib.Data.Nat.Catalan` — Catalan number definition and properties
- `Mathlib.Combinatorics.Catalan` — combinatorial interpretations (if exists)

## Metadata

```yaml
tags:
  - combinatorics
  - catalan-numbers
  - ballot-problem
  - lattice-paths
  - lgv-lemma
  - reflection-principle
related_proofs:
  - ballot-problem
  - ballot-problem-oq-03-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-23T11:40:52+02:00
```

**Significance**: 6/10
**Tractability**: 7/10
