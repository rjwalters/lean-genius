# Problem: Rational Circle Parametrization for x² + y² = p (primes p ≡ 1 mod 4)

**Slug**: pythagorean-triples-oq-03
**Created**: 2026-06-14
**Status**: Active
**Source**: gallery-gap <!-- open question extending pythagorean-triples -->

## Problem Statement

### Formal Statement

$$
\forall\, p \text{ prime},\ p \equiv 1 \pmod 4 \ \Longrightarrow\ \exists\, x,y \in \mathbb{Z},\ x^2 + y^2 = p,
$$

to be formalized along the **rational-parametrization** line: the rational points on the unit circle $u^2+v^2=1$ are exactly $\left(\tfrac{1-t^2}{1+t^2}, \tfrac{2t}{1+t^2}\right)$ for $t\in\mathbb{Q}\cup\{\infty\}$, the same parametrization that generates Pythagorean triples in the gallery proof.

### Plain Language

The gallery proof `pythagorean-triples` derives all integer right-triangle side lengths by drawing rational-slope lines through $(-1,0)$ on the unit circle. This open question asks: can that *same geometric parametrization technique* be turned into a Lean proof of Fermat's two-square theorem — that every prime that is one more than a multiple of four is a sum of two squares (e.g. $5=1+4$, $13=4+9$, $17=16+1$)?

### Why This Matters

It connects two classical results (Pythagorean triples and Fermat's two-square theorem) through one reusable method, and tests whether the rational-circle technique generalizes from the *parametrize-all-solutions* setting to an *existence* statement that genuinely uses arithmetic of $\mathbb{Z}[i]$. Mathlib already has `Nat.Prime.sq_add_sq` (existence) via Gaussian integers; the open contribution is the explicit constructive/parametric route and the bridge to the gallery's geometric method.

## Known Results

### What's Already Proven

- `Nat.Prime.sq_add_sq` : `p % 4 = 1 → ∃ a b, a^2 + b^2 = p` — Mathlib (descent / `ZMod`, Gaussian integers)
- All Pythagorean triples via rational parametrization — gallery proof `pythagorean-triples`
- `ZMod.exists_sq_eq_neg_one_iff` : $-1$ is a QR mod $p$ iff $p \not\equiv 3 \pmod 4$ — Mathlib

### What's Still Open (in Lean)

- A formalization that *derives* the two-square representation through the rational-circle / descent-on-the-circle geometry, rather than the abstract Gaussian-integer norm argument
- Extension of the parametrization toolkit to other conics $x^2 + y^2 = n$ and $x^2 + 2y^2 = p$, $x^2+3y^2=p$

### Our Goal

Build a small reusable Lean library: (1) the rational-point parametrization of $u^2+v^2=1$, (2) a clearing-denominators lemma converting a rational point of given "height" into an integer solution, (3) apply it (with $-1$ being a QR mod $p$) to obtain $x^2+y^2=p$. Relate the result to `Nat.Prime.sq_add_sq`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-triples | Source of the rational-parametrization method | Rational lines through a conic point |
| sum-of-two-squares (if present) / number-theory cluster | Same theorem, different route | Gaussian integers / descent |

## Initial Thoughts

### Potential Approaches

1. **Geometry-of-numbers / Thue descent on the circle** (recommended): use $-1 \equiv r^2 \pmod p$ to get a rational point of bounded height on the circle, then Minkowski/pigeonhole (Thue's lemma) to extract a genuine integer solution with $x^2+y^2 = p$.
   - Why it might work: Mathlib has `ZMod.exists_sq_eq_neg_one_iff` and pigeonhole infrastructure; mirrors the gallery's "rational point → integer triple" clearing step.
   - Risk: the Minkowski/Thue bound step is the technical core.

2. **Direct parametrization + denominator analysis**: parametrize, then control the denominator $1+t^2$ to land on $p$ exactly.
   - Risk: harder to force the value to be a *prime* $p$ rather than an arbitrary sum of two squares.

### Key Difficulties

- Going from "there is a rational point" to "there is an integer point summing to exactly $p$" needs a height/descent or Thue-lemma argument.
- Cleanly connecting the geometric construction to the existing `Nat.Prime.sq_add_sq` so the work is recognized as a proof, not a restatement.

### What Would a Proof Need?

- Key lemma 1: rational parametrization of $u^2+v^2=1$ (constructive bijection with $\mathbb{Q}\cup\{\infty\}$).
- Key lemma 2: Thue's lemma / pigeonhole to produce a small integer solution of $x \equiv ry \pmod p$.
- Technical requirements: `Mathlib.NumberTheory.SumTwoSquares`, `ZMod`, `Mathlib.NumberTheory.Pythagorean` (if present), pigeonhole.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The target theorem already exists in Mathlib, so correctness is anchored; the novelty is the *method*.
- Thue's lemma and QR(-1) are available; the parametrization is elementary.

**Estimated Effort**:
- Exploration: 1 day (locate Thue/pigeonhole and the circle parametrization status in Mathlib)
- If tractable: several days to ~1 week

## References

### Papers / Texts
- Hardy & Wright, *An Introduction to the Theory of Numbers*, two-square theorem.
- Aigner & Ziegler, *Proofs from THE BOOK*, "Representing numbers as sums of two squares".

### Mathlib
- `Mathlib.NumberTheory.SumTwoSquares` — `Nat.Prime.sq_add_sq`
- `ZMod.exists_sq_eq_neg_one_iff` — $-1$ as a quadratic residue
- Pigeonhole / `Finset` cardinality lemmas for Thue's lemma

## Metadata

```yaml
tags:
  - number-theory
  - diophantine
  - two-squares
  - rational-parametrization
  - fermat
related_proofs:
  - pythagorean-triples
difficulty: medium
source: gallery-gap
created: 2026-06-14
```
