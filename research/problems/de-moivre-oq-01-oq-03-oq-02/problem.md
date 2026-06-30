# Problem: Chebyshev Semigroup Law C_{mn} = C_m ∘ C_n over 𝔽_p

**Slug**: de-moivre-oq-01-oq-03-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent established the Chebyshev–De Moivre recurrence over arbitrary commutative rings
(finite fields, ℂ, ℚ_p). Writing `C_n` for the degree-`n` Chebyshev polynomial of the first
kind evaluated as a map, the goal is the **semigroup / nesting law**:

$$
C_{mn}(x) = C_m\big(C_n(x)\big) \qquad \text{for all } m, n \in \mathbb{N},
$$
specialized and packaged over a finite field `𝔽_p`. Equivalently, `n ↦ C_n` is a monoid
homomorphism `(ℕ, ·) → (End 𝔽_p, ∘)`, which is exactly the algebraic core of the
Chebyshev/Lucas-sequence public-key scheme (commutativity of `C_m ∘ C_n = C_n ∘ C_m`).

### Plain Language

Chebyshev polynomials compose multiplicatively: applying `C_n` and then `C_m` is the same as
applying `C_{mn}`. The parent proved the defining recurrence over general rings; here we
package the composition (nesting) law `C_{mn} = C_m ∘ C_n` over a finite field `𝔽_p` and note
that the resulting commuting family is the trapdoor structure behind a Chebyshev/Lucas
public-key cryptosystem.

### Why This Matters

The semigroup law is the single identity that makes Chebyshev-based key exchange work
(`C_a(C_b(x)) = C_b(C_a(x))`). Formalizing it over `𝔽_p` connects the gallery's pure
Chebyshev–De Moivre algebra to a concrete cryptographic application and gives a reusable
monoid-homomorphism statement.

### Why This Matters (Mathlib hook)

Mathlib has `Polynomial.Chebyshev.T` and `Polynomial.Chebyshev.T_mul_T` /
`Polynomial.Chebyshev.T_comp_T`-style composition lemmas; the task is to transport the
composition identity to evaluation maps over `ZMod p` (`p` prime) and state the homomorphism.

## Known Results

### What's Already Proven

- `de-moivre-oq-01-oq-03` — Chebyshev–De Moivre over arbitrary rings: `𝔽_p`, ℂ, ℚ_p (verified, original).
- `de-moivre-oq-01` and ancestors — De Moivre / Chebyshev recurrence foundations.
- Mathlib: `Polynomial.Chebyshev.T`, the composition law `T (m*n) = (T m).comp (T n)`, and `ZMod p` field instances.

### What's Still Open

- The evaluation-map form `C_{mn}(x) = C_m(C_n(x))` over `𝔽_p` as a standalone, named result.
- The packaging as a monoid hom `(ℕ, ·) → (𝔽_p → 𝔽_p, ∘)` and the commuting-family corollary.

### Our Goal

Prove `C_{mn} = C_m ∘ C_n` as evaluation maps over `ZMod p`, deduce
`C_m ∘ C_n = C_n ∘ C_m`, and state the semigroup/monoid-hom packaging that underlies the
Chebyshev public-key construction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-01-oq-03 | Parent: Chebyshev–De Moivre over arbitrary rings | ring homs, polynomial recurrence |
| de-moivre-oq-01 | De Moivre / Chebyshev foundations | trig identities, induction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — transport Mathlib's polynomial composition law**: Use
   `Polynomial.Chebyshev.T_comp_T` (or derive `T (m*n) = (T m).comp (T n)`) and apply
   `Polynomial.eval` over `ZMod p`, using `eval_comp` to get the evaluation-map identity.
   - Why it might work: Mathlib already has the polynomial-level composition lemma; only need `eval` transport.
   - Risk: exact lemma name/normalization (`T` indexing over ℤ vs ℕ); `eval_comp` bookkeeping.

2. **Approach B — induction on m**: Prove `C_{mn} = C_m ∘ C_n` by induction using the
   parent's recurrence directly over `𝔽_p`.
   - Why it might work: self-contained, reuses parent recurrence.
   - Risk: more manual than transporting an existing composition lemma.

### Key Difficulties

- Aligning Mathlib's `Polynomial.Chebyshev.T` indexing (defined over ℤ) with the ℕ-indexed `C_n` here.
- Stating the monoid-hom packaging cleanly (target monoid `End` under composition).

### What Would a Proof Need?

- Key lemma 1: `T (m * n) = (T m).comp (T n)` over `ZMod p` (or its evaluation form).
- Key lemma 2: `Polynomial.eval_comp` to push composition through evaluation.
- Technical requirements: `ZMod p` field/`Fact p.Prime` instance, `Polynomial.eval`, `Function.comp`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The composition law exists at the polynomial level in Mathlib; this is mostly transport + packaging.
- The parent already set up Chebyshev over `𝔽_p`, so the ambient instances are in place.
- Main risk is indexing/normalization friction, not mathematical depth.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard: a few days if Mathlib's composition lemma needs re-deriving

## References

### Mathlib
- `Mathlib.RingTheory.Polynomial.Chebyshev` — `Polynomial.Chebyshev.T`, `T_mul`, composition lemmas.
- `Mathlib.Data.ZMod.Basic` — `ZMod p` field structure for prime `p`.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - finite-fields
related_proofs:
  - de-moivre-oq-01-oq-03
  - de-moivre-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
