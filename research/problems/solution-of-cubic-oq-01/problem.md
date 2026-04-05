# Problem: Reduce General Cubic to Depressed Form

**Slug**: solution-of-cubic-oq-01
**Created**: 2026-04-05T03:48:17-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } a \neq 0,\ \text{the substitution } x = t - \frac{b}{3a} \text{ transforms }
ax^3 + bx^2 + cx + d = 0 \text{ into } t^3 + pt + q = 0
$$

where $p = \frac{3ac - b^2}{3a^2}$ and $q = \frac{2b^3 - 9abc + 27a^2d}{27a^3}$.

### Plain Language

Given a general cubic polynomial $ax^3 + bx^2 + cx + d = 0$, the substitution
$x = t - b/(3a)$ eliminates the quadratic term, yielding the *depressed cubic*
$t^3 + pt + q = 0$. Formalize this algebraic reduction in Lean 4 over a field
(ideally `ℝ` or a general `Field` with characteristic ≠ 3).

### Why This Matters

The gallery already has `SolutionOfCubic.lean` which proves Cardano's formula for
the depressed cubic $x^3 + px + q = 0$. This OQ completes the pipeline: reducing
the general form to depressed form, so Cardano's formula applies to any cubic.
Together they give a full machine-checked proof of the general cubic formula.

## Known Results

### What's Already Proven

- `SolutionOfCubic.lean` — Cardano's formula for depressed cubics (gallery proof)
- `Mathlib.RingTheory.Polynomial.Basic` — polynomial division and evaluation
- `Mathlib.Algebra.Field.Basic` — field arithmetic
- `Mathlib.RingTheory.MvPolynomial.Basic` — multivariate polynomial identities

### What's Still Open

- Formal proof that the substitution $x = t - b/(3a)$ eliminates the $t^2$ term
- Explicit computation of the depressed cubic coefficients $p$ and $q$
- Characteristic-free statement (works over any field with char ≠ 3)

### Our Goal

Prove in Lean 4: for a general monic cubic $x^3 + bx^2 + cx + d = 0$, the
substitution $x = t - b/3$ yields $t^3 + pt + q = 0$ with explicit $p, q$.
(Start monic to simplify; generalize to $a \neq 0$ if straightforward.)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| solution-of-cubic | Parent proof: Cardano on depressed cubic | polynomial arithmetic, cube roots |
| solution-of-cubic-oq-03 | Further open questions on cubic | field extensions |
| combinations-formula-oq-01 | Combinatorial identities; similar algebraic manipulation style | ring lemmas |

## Initial Thoughts

### Potential Approaches

1. **Direct computation in `Polynomial ℝ`**: Define `f = X^3 + b*X^2 + c*X + d`
   and `g = (X - b/3)^3 + ...`, then verify `f.comp (X - b/3) = g` by `ring` or `norm_num`.
   - Why it might work: `ring` tactic handles polynomial identities automatically.
   - Risk: Polynomial composition in Mathlib may need coercion massaging.

2. **Pointwise evaluation**: Show `∀ t, f(t - b/3) = t^3 + p*t + q` using `ring`.
   - Why it might work: Simpler than polynomial composition; just algebra.
   - Risk: Need to carry `a ≠ 0` and `(3:F) ≠ 0` (char ≠ 3) hypotheses.

3. **Mathlib `Polynomial.comp`**: Use existing composition API to state this cleanly.
   - Why it might work: Mathlib has `Polynomial.comp` and evaluation lemmas.
   - Risk: Notation overhead; `ring` may not close polynomial comp goals directly.

### Key Difficulties

- Lean's `Polynomial` type vs. functions: need to choose representation carefully
- Division by 3 requires char ≠ 3 (or work over ℝ/ℚ to avoid this)
- Verifying the explicit formulas for $p$ and $q$ requires careful `ring` computation

### What Would a Proof Need?

- Define `depress : Polynomial F → Polynomial F` (the Tschirnhaus substitution)
- Key lemma: `(depress f).coeff 2 = 0` when `f.coeff 2 = 0` after substitution
- Technical: `Polynomial.comp`, `Polynomial.eval`, `Field.div_add_div_same`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The core computation is pure algebra, likely closed by `ring` after setup
- Mathlib has all needed polynomial arithmetic
- The parent proof `SolutionOfCubic.lean` shows the style works in this codebase
- No topological or analytic arguments needed

**Estimated Effort**:
- Exploration: 1-2 hours (understand Mathlib polynomial API)
- If tractable: 1-3 days (write definitions, close goals with ring/simp)
- If hard: 1 week (custom polynomial composition lemmas)

## References

### Papers
- Cardano, G. "Ars Magna" (1545) — original source of the method

### Online Resources
- Mathlib4 `Mathlib.Algebra.Polynomial.Eval` — polynomial evaluation
- Mathlib4 `Mathlib.Algebra.Polynomial.Degree.Definitions` — degree lemmas

### Mathlib
- `Mathlib.Algebra.Polynomial.Basic` — `Polynomial.comp`, `Polynomial.eval`
- `Mathlib.RingTheory.Polynomial.Chebyshev` — example of nested polynomial proofs
- `Mathlib.FieldTheory.SplittingField.Construction` — field arithmetic for cubics

## Metadata

```yaml
tags:
  - algebra
  - cubic-equations
  - cardano
  - polynomial-arithmetic
  - field-extensions
related_proofs:
  - solution-of-cubic
  - solution-of-cubic-oq-03
difficulty: low
source: gallery-gap
created: 2026-04-05T03:48:17-07:00
```
