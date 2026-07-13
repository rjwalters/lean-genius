# Problem: Symmetric Numerical Semigroups via Apéry Sets

**Slug**: frobenius-number-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
S \text{ symmetric} \iff a \in \mathbb{Z}\setminus S \implies (g - a) \in S, \quad g = F(S),
$$
characterized through the Apéry set $\mathrm{Ap}(S, m) = \{\, s \in S : s - m \notin S \,\}$ and Kunz's coordinate description.

### Plain Language

A numerical semigroup $S \subseteq \mathbb{N}$ (cofinite, closed under addition, containing $0$) is *symmetric* when its set of gaps is exactly the "mirror image" of $S$ across the Frobenius number $g$: for every integer $a$, exactly one of $a$, $g-a$ lies in $S$. For two generators this is automatic; the open question is to characterize symmetry for semigroups with three or more generators using Apéry sets (Kunz, 1970), and to determine which generator tuples preserve the involution $k \mapsto g - k$.

### Why This Matters

Symmetric numerical semigroups correspond to Gorenstein affine monomial curves, linking elementary number theory to commutative algebra and algebraic geometry. The Apéry set gives a finite, computable certificate of symmetry, and the involution structure underlies duality phenomena (canonical modules, type-one semigroups).

## Known Results

### What's Already Proven

- Parent entry `frobenius-number-oq-02` establishes the Frobenius number machinery for numerical semigroups in Lean.
- `frobenius-number-oq-01-oq-03-oq-01` (gallery): generator-agnostic converse that type one ⟹ symmetric for arbitrary numerical semigroups.
- Classical: $S$ symmetric $\iff |\text{gaps}| = (g+1)/2$ $\iff$ pseudo-Frobenius set is the singleton $\{g\}$ (type one).

### What's Still Open

- An Apéry-set (Kunz coordinates) characterization of symmetry for $\geq 3$ generators in Lean.
- Identifying which generator tuples $(n_1, \dots, n_k)$ yield a semigroup whose Apéry set is symmetric under $k \mapsto g-k$.

### Our Goal

Formalize the equivalence between symmetry and the self-duality of the Apéry set $\mathrm{Ap}(S,m)$ under $w \mapsto (\max \mathrm{Ap}(S,m)) - w$, and connect it to the existing type-one characterization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| frobenius-number-oq-02 | Direct parent; Frobenius number API | numerical semigroups |
| frobenius-number-oq-01-oq-03-oq-01 | Type-one ⟹ symmetric converse | pseudo-Frobenius / gap domination |

## Initial Thoughts

### Potential Approaches

1. **Apéry self-duality**: Define the Apéry set as a Finset, prove symmetry $\iff$ the map $w \mapsto \max - w$ is an involution of the Apéry set.
   - Why it might work: Apéry sets are finite and decidable; the involution is a concrete bijection.
   - Risk: Bridging gap-counting and Apéry coordinates may need careful counting lemmas.

2. **Reduce to type one**: Reuse the existing type-one ⟹ symmetric engine and add the Apéry-coordinate computation of the type.
   - Why it might work: Leverages already-formalized infrastructure.
   - Risk: Apéry-to-pseudo-Frobenius translation must be made explicit.

### Key Difficulties

- Encoding Apéry sets and Kunz coordinates cleanly in Lean.
- Counting gaps vs. counting Apéry elements modulo the multiplicity.

### What Would a Proof Need?

- Key lemma: $|\text{gaps}(S)| = \frac{1}{m}\sum_{w \in \mathrm{Ap}(S,m)} w - \frac{m-1}{2}$ (Selmer-type formula).
- Key lemma: symmetry $\iff$ Apéry self-duality.
- Technical requirements: Finset cardinality and involution counting.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Builds directly on two existing verified gallery entries.
- Apéry sets are finite, decidable structures amenable to Lean.
- The hardest classical case (type one ⟺ symmetric) is already formalized.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: several days

## References

### Papers
- E. Kunz, "The value-semigroup of a one-dimensional Gorenstein ring," Proc. AMS, 1970 — symmetric ⟺ Gorenstein.
- Rosales & García-Sánchez, "Numerical Semigroups," Springer 2009 — Apéry sets and symmetry.

### Mathlib
- `Mathlib.GroupTheory` / `Finset` cardinality API — for gap and Apéry-set counting.

## Metadata

```yaml
tags:
  - number-theory
  - numerical-semigroups
  - frobenius
  - apery
related_proofs:
  - frobenius-number-oq-02
  - frobenius-number-oq-01-oq-03-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
