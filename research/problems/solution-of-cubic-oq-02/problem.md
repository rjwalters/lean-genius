# Problem: Casus Irreducibilis — Real Roots Require Complex Radicals

**Slug**: solution-of-cubic-oq-02
**Created**: 2026-04-05T13:56:47-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a depressed cubic $x^3 + px + q = 0$ with discriminant $\Delta = -4p^3 - 27q^2 > 0$
(three distinct real roots), the roots **cannot** be expressed using only real radicals.
That is, there is no real-radical tower $\mathbb{Q}(p,q) \subseteq F_1 \subseteq \cdots \subseteq F_k$
with $F_{i+1} = F_i(\alpha_i)$, $\alpha_i^{n_i} \in F_i$, $\alpha_i \in \mathbb{R}$, such that
all three roots lie in $F_k$.

### Plain Language

Cardano's formula for the cubic involves taking cube roots of complex numbers even
when the final answers are real. The **casus irreducibilis** theorem says this is
unavoidable: when a cubic has three real roots, you must pass through complex
arithmetic to express them with radicals. You cannot stay in the reals.

### Why This Matters

A classical result in Galois theory with a non-obvious flavor: the cubic has real
solutions, yet real arithmetic is insufficient to construct them via radicals. Explains
why Cardano's formula requires complex arithmetic even for real outputs. A Lean
formalization would add a significant result to the algebra section of the gallery.

## Known Results

### What's Already Proven

- Cardano's formula for the cubic — `solution-of-cubic` (gallery)
- Abel-Ruffini theorem — `abel-ruffini` (gallery)
- Galois group computations — `galois-group-cos-pi-7` (gallery)

### What's Still Open

- Lean formalization of casus irreducibilis
- Formal connection between $\Delta > 0$ and the necessity of complex radicals

### Our Goal

Prove in Lean 4: when $\Delta > 0$, the splitting field of the cubic is not contained
in any real-radical tower. This is a consequence of the Galois group being $S_3$, which
is not solvable by real radicals of odd prime degree.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| solution-of-cubic | Parent: Cardano's formula | Field extensions, radicals |
| abel-ruffini | Galois-theoretic method | Solvability of groups, radical towers |
| galois-group-cos-pi-7 | Galois group computation | Minimal polynomial, splitting fields |

## Initial Thoughts

### Potential Approaches

1. **Galois-theoretic**: Show the Galois group of the cubic (when $\Delta > 0$) is $S_3$,
   and argue that any real-radical tower has 2-power degree at odd-degree steps, blocking
   the degree-3 extension required for the splitting field.
   - Why it might work: Standard proof; Mathlib has Galois theory.
   - Risk: Requires formalizing "real-radical tower" concept in Lean.

2. **Direct via discriminant + complex conjugation**: Show $\sqrt{\Delta}$ generates a
   non-trivial purely imaginary extension at some point in any radical tower.
   - Risk: Technical; less standard.

3. **Topological/monodromy argument**: The roots cannot be continuously assigned to
   real-radical branches as $\Delta$ varies.
   - Risk: Harder to formalize.

### Key Difficulties

- Formalizing `IsRealRadicalExtension` as an inductive definition in Lean
- Connecting $\Delta > 0$ to the obstruction in the real-radical tower
- Mathlib's Galois theory exists but this specific configuration needs setup

### What Would a Proof Need?

- Definition: `IsRealRadicalExtension` — tower of real $n$-th root extensions
- Lemma: The splitting field has $[K:\mathbb{Q}] = 6$ when $\Delta > 0$ and $p, q \in \mathbb{Q}$
- Key fact: $S_3$ is not solvable by real radicals of odd prime degree

## Tractability Assessment

**Difficulty**: Medium-Hard

**Justification**:
- Classical result with a clean mathematical proof
- Requires non-trivial Galois theory setup in Lean
- Mathlib has `IntermediateField`, `GaloisGroup`, `IsSolvable` — pieces exist
- This is a deeper formalization than the parent Cardano proof

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib Galois theory coverage)
- If tractable: 2-4 weeks for complete proof

## References

### Papers
- Cardano (1545) — Ars Magna (original cubic formula)
- Hadlock (1978) — "Field Theory for the Perplexed" (casus irreducibilis treatment)

### Mathlib
- `Mathlib.FieldTheory.GaloisGroup` — Galois groups
- `Mathlib.RingTheory.RootsOfUnity.Basic` — splitting fields
- `Mathlib.GroupTheory.IsSolvable` — solvability of groups

## Metadata

```yaml
tags:
  - algebra
  - polynomial
  - radicals
  - galois-theory
  - cubic
related_proofs:
  - solution-of-cubic
  - abel-ruffini
difficulty: medium-hard
source: gallery-gap
created: 2026-04-05T13:56:47-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
