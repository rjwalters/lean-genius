# Problem: Double-factorial form of half-integer Gamma values

**Slug**: gamma-reflection-formula-oq-01-oq-03-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every $n \in \mathbb{N}$:

$$
\Gamma\!\left(n + \tfrac12\right) = \frac{(2n-1)!!}{2^n}\,\sqrt{\pi},
\qquad\text{and}\qquad
\frac{(2n)!}{4^n\, n!} = \frac{(2n-1)!!}{2^n},
$$

where $(2n-1)!! = 1\cdot 3\cdot 5\cdots(2n-1)$ is the odd double factorial (with $(-1)!! = 1$).

### Plain Language

The parent entry (`gamma-reflection-formula-oq-01-oq-03`) proves the half-integer closed form
$\Gamma(n+\tfrac12) = \tfrac{(2n)!}{4^n n!}\sqrt{\pi}$. This leaf re-expresses the same values
through the **odd double factorial** $(2n-1)!!$, which is the form most commonly seen in tables,
and proves the purely combinatorial equivalence $\tfrac{(2n)!}{4^n n!} = \tfrac{(2n-1)!!}{2^n}$
that links the two representations.

### Why This Matters

The double-factorial form is the standard textbook expression for half-integer Gamma values and
appears throughout the evaluation of Gaussian moments and Wallis-type products. The bridging
identity $(2n)! = 2^n\, n!\,(2n-1)!!$ is a clean, fully elementary combinatorial fact worth
having machine-checked.

## Known Results

### What's Already Proven

- Parent `gamma-reflection-formula-oq-01-oq-03`: $\Gamma(n+\tfrac12) = \tfrac{(2n)!}{4^n n!}\sqrt{\pi}$ (verified, original).
- Mathlib `Nat.doubleFactorial` and `Nat.doubleFactorial_two_mul` / related lemmas relating
  $(2n)!$, $n!$, and double factorials.

### What's Still Open

- The double-factorial restatement and the equivalence identity (this entry).

### Our Goal

Prove (1) the combinatorial identity $(2n)! = 2^n\, n!\,(2n-1)!!$ (equivalently
$\tfrac{(2n)!}{4^n n!} = \tfrac{(2n-1)!!}{2^n}$), and (2) substitute into the parent's closed form
to obtain $\Gamma(n+\tfrac12) = \tfrac{(2n-1)!!}{2^n}\sqrt{\pi}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| gamma-reflection-formula-oq-01-oq-03 | Direct parent; half-integer closed form | Gamma recurrence, factorials |
| area-of-circle-oq-07-oq-05-oq-01 | Uses half-integer Gamma for Gaussian moments | Gamma half-integer values |

## Initial Thoughts

### Potential Approaches

1. **Induction on the combinatorial identity**: prove $(2(n+1))! = 2^{n+1}(n+1)!\,(2n+1)!!$ from
   the $n$ case using $(2n+2)! = (2n+2)(2n+1)(2n)!$ and $(2n+1)!! = (2n+1)(2n-1)!!$; `ring`/`omega`
   close each step. Then divide to get the rational form and substitute into the parent.
   - Why it might work: pure `Nat`/`ring` induction; Mathlib likely already has a close form.
   - Risk: matching Mathlib's `doubleFactorial` indexing/conventions exactly.

### Key Difficulties

- Aligning the $(2n-1)!!$ convention with Mathlib's `Nat.doubleFactorial`.

### What Would a Proof Need?

- Key lemma: `(2*n)! = 2^n * n! * (2*n-1)!!` by induction (or pull from Mathlib if present).
- Cast to `ℝ` and substitute into the parent's `Γ(n+1/2)` value.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The hard analytic content lives in the parent; this leaf is a combinatorial restatement.
- Mathlib's `Nat.doubleFactorial` API plus a short induction suffices.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gamma.Basic` — Gamma function values and recurrence.
- `Mathlib.Combinatorics`/`Mathlib.Data.Nat.Factorial.DoubleFactorial` — `Nat.doubleFactorial` API.

## Metadata

```yaml
tags:
  - analysis
  - gamma-function
  - double-factorial
  - special-functions
related_proofs:
  - gamma-reflection-formula-oq-01-oq-03
  - area-of-circle-oq-07-oq-05-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-24
```
