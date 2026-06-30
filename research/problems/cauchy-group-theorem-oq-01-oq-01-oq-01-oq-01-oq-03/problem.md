# Problem: Exact count of solutions of xⁿ = g in a finite group

**Slug**: cauchy-group-theorem-oq-01-oq-01-oq-01-oq-01-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a finite (abelian) group $G$, a fixed exponent $n$, and a fixed element $g \in G$, determine the size of the solution set
$$
N_n(g) \;=\; \#\{\,x \in G : x^{n} = g\,\}.
$$
The parent thread handles $g = e$ (Frobenius: $\#\{x : x^n = e\}$ is a multiple of $\gcd(n, |G|)$). This leaf asks for the count at a **fixed non-identity** $g$: characterize $N_n(g)$, in particular that it is either $0$ or equal to $\#\{x : x^n = e\} = |\ker(\,\cdot^n)|$ according to whether $g$ lies in the image of the power map $x \mapsto x^n$.

### Plain Language

Cauchy's theorem and its descendants count elements satisfying $x^n = e$. This leaf generalizes the right-hand side from the identity to an arbitrary fixed element $g$. For abelian $G$ the map $\phi_n : x \mapsto x^n$ is a homomorphism, so the fiber $\phi_n^{-1}(g)$ is either empty (if $g \notin \operatorname{im}\phi_n$) or a coset of $\ker\phi_n$, hence has size exactly $|\ker\phi_n|$. The task is to prove this clean dichotomy and connect $|\ker\phi_n|$ to the parent's $g=e$ count.

### Why This Matters

Completes the "how many $n$-th roots does an element have" picture for finite abelian groups, tying together Cauchy/Frobenius counting, the power endomorphism, and coset/fiber cardinality — a tidy, reusable group-theory result.

## Known Results

### What's Already Proven

- Parent `cauchy-group-theorem-oq-01-oq-01-oq-01-oq-01` — the $g = e$ count / power-map kernel analysis.
- Mathlib: `powMonoidHom`/`zpowGroupHom` (the power map as a homomorphism for abelian/commutative groups), `MonoidHom.ker`, fiber = coset (`MonoidHom.preimage` / `QuotientGroup`), `Subgroup.card_eq_card_quotient_mul_card_subgroup`, Lagrange.

### What's Still Open

- The non-identity fiber-cardinality dichotomy ($0$ or $|\ker\phi_n|$) as a named theorem.
- The membership criterion $g \in \operatorname{im}\phi_n$ and its relation to $\gcd(n,|G|)$ for cyclic/abelian $G$.

### Our Goal

Prove $N_n(g) \in \{0, |\ker\phi_n|\}$ for finite abelian $G$, with $N_n(g) = |\ker\phi_n|$ iff $g \in \operatorname{im}\phi_n$, and relate $|\ker\phi_n|$ to the parent $g=e$ count. Axiom-free.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-group-theorem-oq-01-oq-01-oq-01-oq-01 | Parent: $g=e$ root count | power map kernel, Frobenius |
| cauchy-group-theorem-oq-01 | Cauchy's theorem core | group actions / orbit counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — power map as homomorphism (abelian case)**: For abelian $G$, $\phi_n = $ `powMonoidHom n` is a hom; the fiber over $g$ is empty or a coset of $\ker\phi_n$, so its card is $0$ or $|\ker\phi_n|$ (`MonoidHom` fiber = coset).
   - Why it might work: clean, fully Mathlib-supported for `CommGroup`.
   - Risk: assembling "fiber = coset ⟹ equal cardinality" from Mathlib's quotient lemmas.

2. **Approach B — orbit/coset counting**: Use `Subgroup` coset cardinality and `Fintype.card` of the fiber as a `Set`.
   - Why it might work: explicit cardinality bookkeeping.
   - Risk: `Fintype`/`Finset` instance plumbing on the fiber set.

### Key Difficulties

- Restricting cleanly to the abelian case (non-abelian counts are genuinely harder and not the target).
- Cardinality of a coset = cardinality of the subgroup, in Mathlib idiom.

### What Would a Proof Need?

- Key lemma 1: `powMonoidHom n` is a homomorphism on `CommGroup`.
- Key lemma 2: a nonempty fiber of a group hom is a coset of the kernel with equal cardinality.
- Technical requirements: `MonoidHom.ker`, coset cardinality, `Fintype` on fibers.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- For abelian $G$ the homomorphism structure makes the fiber analysis standard.
- Mathlib has the power homomorphism, kernels, and coset cardinality.
- Scoping to abelian keeps it tractable; the general non-abelian count should be explicitly deferred.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 2–3 days
- If hard: unknown (if pushed beyond the abelian case)

## References

### Mathlib
- `Mathlib.GroupTheory.QuotientGroup` — fiber = coset, quotient cardinality.
- `Mathlib.Algebra.Group.Hom` / `powMonoidHom` — power map as homomorphism.
- `Mathlib.GroupTheory.OrderOfElement` — Frobenius-style root counts.

## Metadata

```yaml
tags:
  - group-theory
  - finite-groups
  - cauchy-theorem
  - equation-counting
related_proofs:
  - cauchy-group-theorem-oq-01-oq-01-oq-01-oq-01
  - cauchy-group-theorem-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
