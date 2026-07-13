# Problem: Composition/commutation theory for Chebyshev Uₙ and Dickson polynomials

**Slug**: chebyshev-polynomials-oq-01-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent `chebyshev-polynomials-oq-01` establishes the composition/commutation theory
for the Chebyshev polynomials of the **first** kind: $T_m \circ T_n = T_{mn} = T_n \circ T_m$.
This OQ asks which structural laws carry over to the Chebyshev polynomials of the
**second** kind $U_n$ and to the **Dickson** polynomials $D_n(x,a)$:

$$
D_m(D_n(x,a),\,a^n) = D_{mn}(x,a), \qquad\text{and the corresponding } U_n \text{ relations.}
$$

### Plain Language

`Tₙ` famously commute under composition (`Tₘ ∘ Tₙ = Tₘₙ`). The second-kind `Uₙ` and the
Dickson polynomials `Dₙ` satisfy related but *not identical* laws — Dickson polynomials
have a genuine composition/commutation law `Dₘ(Dₙ(x,a), aⁿ) = Dₘₙ(x,a)`, while `Uₙ`
do **not** compose as cleanly. Identify precisely which laws survive for each family and
formalize the ones that do.

### Why This Matters

Clarifies the boundary of the Chebyshev composition phenomenon: Dickson polynomials are
the natural generalization for which the commutation law persists (they are essentially
`Tₙ` up to normalization / the Ritt theory of permutation polynomials), whereas `Uₙ` mark
where it breaks. A clean formalization records both the positive law and the negative.

## Known Results

### What's Already Proven

- Parent `chebyshev-polynomials-oq-01`: `T` composition/commutation `Tₘ ∘ Tₙ = Tₘₙ`.
- Mathlib: `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.U`, recurrences and the
  `T`-composition lemma `Polynomial.Chebyshev.T_mul_T` / `T_comp` family.

### Our Goal

Formalize the Dickson composition law `Dₘ(Dₙ(x,a), aⁿ) = Dₘₙ(x,a)` and state precisely
what the `U`-family does/does not satisfy (e.g. product/recurrence identities rather than
a clean composition law).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-polynomials-oq-01 | parent; first-kind composition theory | polynomial composition, recurrences |

## Initial Thoughts

### Potential Approaches

1. **Dickson via `T`**: use the normalization `Dₙ(2√a·x, a) = 2 a^{n/2} Tₙ(x)` to transport
   the `Tₙ` composition law to Dickson polynomials.
   - Risk: normalization/half-power bookkeeping over a general commutative ring.
2. **Direct recurrence induction** on the Dickson three-term recurrence.

## Tractability Assessment

**Difficulty**: Medium

**Justification**: `T`-composition already exists (parent + Mathlib). Dickson is either
in or close to Mathlib; the transport is standard. Scoping to the Dickson positive law
plus the `U` negative statement keeps it bounded.

## References

### Mathlib
- `Mathlib.RingTheory.Polynomial.Chebyshev` — `T`, `U`, recurrences, composition lemmas.

## Metadata

```yaml
tags:
  - polynomials
  - chebyshev-polynomials
  - ring-theory
  - function-composition
related_proofs:
  - chebyshev-polynomials-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 6/10
**Tractability**: 6/10
