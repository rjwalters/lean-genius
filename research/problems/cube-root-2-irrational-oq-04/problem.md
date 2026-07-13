# Problem: Delian Problem Impossibility — ∛2 is Not Constructible

**Slug**: cube-root-2-irrational-oq-04
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\neg\,\exists\,(\text{compass-and-straightedge construction of } \sqrt[3]{2}),
\qquad\text{since } [\mathbb{Q}(\sqrt[3]{2}):\mathbb{Q}] = 3 \nmid 2^{k}.
$$

### Plain Language

Doubling the cube — constructing a segment whose length is the cube root of 2 — is one of the three classical compass-and-straightedge impossibilities. The goal is to formalize the impossibility: any constructible real number is algebraic of degree a power of 2 over the rationals, but ∛2 has minimal polynomial X³ − 2 of degree 3, and 3 is not a power of 2, so ∛2 cannot be constructed.

### Why This Matters

This closes the classical-geometry impossibility trilogy in the gallery. Angle trisection is already formalized (`angle-trisection`), and the cube-root-of-2 irrationality / minimal-polynomial facts are already present (`cube-root-2-irrational`). Connecting the degree-3 fact to the constructible-degree obstruction yields the Delian impossibility with the same field-theoretic machinery, demonstrating that the trilogy shares a single underlying argument.

## Known Results

### What's Already Proven

- `cube-root-2-irrational` — establishes irrationality of ∛2 and the relevant minimal polynomial X³ − 2.
- `angle-trisection` — the constructible-number degree obstruction is already applied here to rule out trisecting a 60° angle; the same lemma about constructible numbers having 2-power degree is reused.
- Mathlib's field-theory layer provides minimal polynomials, degree of field extensions, and tower-law multiplicativity of degrees.

### What's Still Open

- A first-class statement of the Delian impossibility as a named theorem in the gallery.
- A clean lemma "constructible ⇒ degree is a power of 2 over ℚ" reusable across all three classical impossibilities, if not already isolated by the angle-trisection development.

### Our Goal

Prove `¬ IsConstructible (2 : ℝ)^(1/3)` (or the project's constructibility predicate applied to ∛2) by combining `[ℚ(∛2):ℚ] = 3` with the power-of-2 degree obstruction. Reuse, rather than re-derive, the obstruction lemma from the angle-trisection formalization where possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cube-root-2-irrational | Supplies degree-3 minimal polynomial X³ − 2 of ∛2 | Minimal polynomials, irreducibility |
| angle-trisection | Already uses the 2-power-degree constructibility obstruction | Constructible numbers, field-extension degrees |
| abel-ruffini | Shared Galois/field-extension toolkit | Galois theory, degree towers |

## Initial Thoughts

### Potential Approaches

1. **Reuse the angle-trisection obstruction lemma.** If the angle-trisection proof exposes a lemma of the form "constructible numbers have degree 2ᵏ over ℚ," apply it directly to ∛2 with degree 3.
   - Why it might work: the hard geometric content is already done; only the degree-3 input differs.
   - Risk: the lemma may be stated inline/specialized to trisection and need light generalization.

2. **Direct field-tower argument.** Show any constructible α lies in a tower of quadratic extensions, so [ℚ(α):ℚ] is a power of 2; conclude 3 ∤ 2ᵏ.
   - Why it might work: standard textbook proof, well-supported by Mathlib's tower law.
   - Risk: assembling the iterated-quadratic-tower characterization from scratch is more work.

### Key Difficulties

- Locating or extracting a reusable "constructible ⇒ 2-power degree" lemma rather than duplicating it.
- Matching the project's exact constructibility predicate / encoding of compass-and-straightedge constructions.

### What Would a Proof Need?

- Key lemma 1: constructible real numbers have degree a power of 2 over ℚ.
- Key lemma 2: [ℚ(∛2):ℚ] = 3 (from X³ − 2 irreducible over ℚ, already available).
- Technical requirement: divisibility fact that 3 does not divide any power of 2.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The companion impossibility (angle trisection) is already formalized with the same obstruction.
- The degree-3 fact for ∛2 is already in the gallery.
- Mathlib has the field-theory tower law and minimal-polynomial degree API.

**Estimated Effort**:
- Exploration: hours (locate the obstruction lemma).
- If tractable: a few days.
- If hard: weeks (only if the obstruction lemma must be built from scratch).

## References

### Papers
- Wantzel (1837), on which geometry problems are solvable by ruler and compass — original impossibility proofs.

### Online Resources
- Standard Galois-theory treatments of the three classical construction problems.

### Mathlib
- `Mathlib.FieldTheory.Minpoly.*` — minimal polynomials and their degrees.
- `Mathlib.FieldTheory.Tower` / `Module.finrank` multiplicativity — degree towers.

## Metadata

```yaml
tags:
  - field-theory
  - constructibility
  - galois-theory
  - classical-geometry
  - minimal-polynomial
related_proofs:
  - cube-root-2-irrational
  - angle-trisection
  - abel-ruffini
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
