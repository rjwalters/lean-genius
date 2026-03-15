# Problem: Lagrange's Four Squares Theorem

**Slug**: fermat-two-squares-oq-01
**Created**: 2026-03-14
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{N},\; \exists\, a, b, c, d \in \mathbb{Z} \text{ such that } n = a^2 + b^2 + c^2 + d^2
$$

### Plain Language

Every non-negative integer can be written as the sum of four integer squares. This is Lagrange's theorem (1770), extending Fermat's two-squares theorem to all integers (which only characterizes primes of the form $4k+1$ as sums of two squares).

### Why This Matters

- One of the oldest and most celebrated results in additive number theory
- Natural generalization of Fermat's two-squares theorem (already in gallery)
- Connects to Waring's problem, quaternion algebras, and modular forms
- Foundation for understanding representation by quadratic forms

## Known Results

### What's Already Proven

- Fermat's two-squares theorem (`fermat-two-squares` in gallery) — primes $p \equiv 1 \pmod{4}$ are sums of two squares
- Euler's four-square identity (product of sums of 4 squares is a sum of 4 squares)
- Three-squares theorem (Legendre/Gauss): $n$ is a sum of 3 squares iff $n \neq 4^a(8b+7)$

### What's Still Open

- Formalization in Lean 4 of the four-squares theorem itself
- Efficient algorithmic decomposition

### Our Goal

Formalize Lagrange's Four Squares Theorem in Lean 4: every non-negative integer is expressible as a sum of four squares.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fermat-two-squares | Parent proof, two-squares case | Zagier's involution, Fermat descent |
| infinitude-of-primes | Foundational number theory | Basic prime properties |
| quadratic-reciprocity | Related quadratic residue theory | Gauss sums, Legendre symbol |

## Initial Thoughts

### Potential Approaches

1. **Euler's identity + descent on primes**
   - Why it might work: By Euler's four-square identity, it suffices to prove every prime is a sum of 4 squares. Then use a descent argument (similar to Fermat descent for two squares).
   - Risk: The descent argument for 4 squares is more involved than for 2 squares.

2. **Quaternion algebra approach**
   - Why it might work: Hurwitz integers (quaternions with integer/half-integer parts) provide an elegant proof via division algorithm in quaternion algebras.
   - Risk: May require significant quaternion infrastructure not in Mathlib.

3. **Modular arithmetic + Minkowski's theorem**
   - Why it might work: Show that for prime $p$, $-1$ is a sum of two squares mod $p$, then use lattice point theorem.
   - Risk: Requires Minkowski's convex body theorem.

### Key Difficulties

- Euler's four-square identity has 24 terms when expanded
- The descent step requires careful case analysis
- Quaternion approach needs algebraic infrastructure

### What Would a Proof Need?

- Key lemma: Euler's four-square identity (product formula)
- Key lemma: Every prime $p$ divides some $a^2 + b^2 + 1$
- Key lemma: Descent from $mp = a^2 + b^2 + c^2 + d^2$ to smaller $m$
- Technical: `Int` arithmetic, `Nat` case analysis

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical theorem with well-known proof strategies
- Fermat two-squares already formalized (related techniques)
- Mathlib has good integer/prime arithmetic support
- Multiple proof approaches available

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 3-7 days
- If hard: 2 weeks (mainly algebraic infrastructure)

## References

### Mathlib
- `Mathlib.Data.Int.Basic` — integer arithmetic
- `Mathlib.Data.Nat.Prime` — prime number properties
- `Mathlib.NumberTheory.SumTwoSquares` — if exists, Fermat's theorem

## Metadata

```yaml
tags:
  - number-theory
  - sum-of-squares
  - additive-number-theory
  - classic
  - extension
related_proofs:
  - fermat-two-squares
difficulty: medium
source: proof-suggestion
created: 2026-03-14
```

**Significance**: 7/10
**Tractability**: 6/10
