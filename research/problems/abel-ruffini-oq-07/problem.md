# Problem: Selmer-Style S₅ Galois Group for x⁵ − x − 1

**Slug**: abel-ruffini-oq-07
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\operatorname{Gal}\!\left(x^5 - x - 1 \,/\, \mathbb{Q}\right) \cong S_5 .
$$

### Plain Language

Provide a second machine-verified example of a quintic over ℚ with non-solvable Galois group, using the classical "resolvent/discriminant" route rather than the Eisenstein criterion. For f = x⁵ − x − 1: (i) f is irreducible over ℚ (Selmer 1956 proved xⁿ − x − 1 is irreducible for all n); (ii) its discriminant is Δ = 2869 = 19·151, which is not a perfect square, so the Galois group is not contained in the alternating group A₅; (iii) f has exactly three real roots, so complex conjugation acts as a transposition. An irreducible quintic whose group contains a transposition and is not inside A₅ must be all of S₅, which is not solvable — a concrete witness to Abel–Ruffini.

### Why This Matters

The gallery already has the canonical Eisenstein-based unsolvable quintic (`abel-ruffini-oq-04-oq-01`, Gal(x⁵ − 4x + 2) ≅ S₅, 0 sorries/0 axioms). x⁵ − x − 1 is the textbook "second proof" via discriminant non-squareness and real-root counting, and it exercises a complementary toolkit (discriminants, Sturm-style real-root counts, the transposition-from-complex-conjugation argument). Formalizing it deepens the Abel–Ruffini cluster and tests how far Mathlib's discriminant/real-root machinery reaches.

## Known Results

### What's Already Proven

- `abel-ruffini-oq-04-oq-01` — Gal(x⁵ − 4x + 2/ℚ) ≅ S₅ via Eisenstein at p = 2 and `galActionHom` bijectivity (the canonical unsolvable quintic, 0 sorries/0 axioms).
- `abel-ruffini` — the abstract Abel–Ruffini theorem and the solvable-by-radicals ⇔ solvable-Galois-group connection.
- Mathlib: `Polynomial.Gal`, `galActionHom`, A₅/S₅ (non)solvability, and the discriminant of a polynomial.

### What's Still Open

- Selmer's irreducibility of xⁿ − x − 1 over ℚ — not currently in Mathlib; needed (at least for n = 5) as an input.
- A discriminant computation Δ(x⁵ − x − 1) = 2869 reachable by `native_decide`/`decide` or by Mathlib's discriminant API, plus "non-square ⇒ Gal ⊄ A₅".
- A formal real-root count (three real roots) yielding a complex-conjugation transposition in the Galois group.

### Our Goal

Assemble Gal(x⁵ − x − 1) ≅ S₅ from three formal inputs: irreducibility (transitive ⇒ 5 | |Gal|), discriminant non-square (Gal ⊄ A₅), and a transposition (from three real roots). A reasonable first milestone is the discriminant computation and the "non-square discriminant ⇒ group not in A₅" step, reusing the `galActionHom`/subgroup scaffolding from `abel-ruffini-oq-04-oq-01`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-oq-04-oq-01 | Existing S₅ quintic; reusable galActionHom/subgroup scaffolding | Eisenstein, Polynomial.Gal, galActionHom bijectivity |
| abel-ruffini | Abstract theorem + solvability ⇔ solvable Galois group | Galois theory, solvable groups |

## Initial Thoughts

### Potential Approaches

1. **Discriminant-first.** Compute Δ = 2869 and prove it is not a rational square, giving Gal ⊄ A₅; combine with transitivity (from irreducibility) and a transposition to force S₅.
   - Why it might work: the discriminant ↔ A₅ correspondence (sign of permutation ↔ square-ness of √Δ) is standard and partially supported in Mathlib.
   - Risk: connecting "discriminant is a square" to "Galois group ⊆ A₅" formally may require building the bridge lemma.

2. **Mirror the Eisenstein proof structure.** Reuse the exact assembly from `abel-ruffini-oq-04-oq-01`, swapping the "contains a 5-cycle and a transposition ⇒ S₅" core, and feed it the new irreducibility + transposition facts.
   - Why it might work: maximizes reuse of an already-green development.
   - Risk: Selmer irreducibility for x⁵ − x − 1 is the genuinely missing input.

### Key Difficulties

- Selmer's irreducibility theorem is not in Mathlib; even the single case n = 5 needs a formal proof (or a `decide`-style irreducibility-over-ℚ certificate via reduction/Newton-polygon).
- Formalizing the "non-square discriminant ⇒ Gal ⊄ A₅" bridge if Mathlib lacks it directly.
- A rigorous three-real-roots count to obtain the complex-conjugation transposition.

### What Would a Proof Need?

- Key lemma 1: x⁵ − x − 1 is irreducible over ℚ (transitivity ⇒ 5 divides |Gal|).
- Key lemma 2: Δ(x⁵ − x − 1) = 2869 and 2869 is not a square ⇒ Gal ⊄ A₅.
- Key lemma 3: exactly three real roots ⇒ complex conjugation is a transposition in Gal.
- Technical requirement: the S₅-from-(transitive + transposition + ⊄ A₅) group-theoretic step.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- A complete, green sibling (`abel-ruffini-oq-04-oq-01`) supplies most of the scaffolding.
- The discriminant and real-root steps are concrete and computational.
- The main obstacle is Selmer irreducibility (and possibly the discriminant↔A₅ bridge) not being in Mathlib.

**Estimated Effort**:
- Exploration: days (survey Mathlib discriminant/irreducibility coverage).
- If tractable: weeks (discriminant milestone first, then full assembly).
- If hard: unknown if Selmer irreducibility must be built from scratch.

## References

### Papers
- E. S. Selmer, "On the irreducibility of certain trinomials" (1956) — irreducibility of xⁿ − x − 1.
- Standard references computing Gal(x⁵ − x − 1) = S₅ via discriminant 2869 and real-root count.

### Online Resources
- Textbook treatments (e.g., Dummit–Foote) of computing quintic Galois groups by resolvents/discriminants.

### Mathlib
- `Mathlib.FieldTheory.PolynomialGaloisGroup` — `Polynomial.Gal`, `galActionHom`.
- `Mathlib.RingTheory.Polynomial.Discriminant` — polynomial discriminants.
- `Mathlib.GroupTheory.SpecificGroups.Alternating` — A₅/S₅ structure and solvability.

## Metadata

```yaml
tags:
  - galois-theory
  - abel-ruffini
  - quintic
  - resolvent
  - discriminant
  - number-theory
related_proofs:
  - abel-ruffini-oq-04-oq-01
  - abel-ruffini
difficulty: high
source: gallery-gap
created: 2026-06-16
```
