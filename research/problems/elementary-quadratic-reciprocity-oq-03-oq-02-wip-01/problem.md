# Problem: Kronecker Symbol WIP Completion

## Statement

### Plain Language
Complete the formalization of the Kronecker symbol in `ElementaryQuadraticReciprocityOQ03OQ02.lean`.
Two theorems are missing: (1) multiplicativity in the second argument (`kronecker_mul_right`), and
(2) generalized quadratic reciprocity for fundamental discriminants.

### Formal Statement

```lean
-- Target 1: Complete multiplicativity in second argument
theorem kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0) :
    kronecker a (m * n) = kronecker a m * kronecker a n

-- Target 2: Generalized quadratic reciprocity for Kronecker symbol
-- For fundamental discriminants d₁, d₂ with gcd(d₁, d₂) = 1:
-- (d₁/|d₂|)(d₂/|d₁|) = (-1)^{((d₁-1)/2)·((d₂-1)/2)}
```

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - seeker-selected
  - number-theory
  - quadratic-reciprocity
  - kronecker-symbol
  - wip-completion
```

**Significance**: 7/10 — Kronecker symbol is foundational in analytic number theory;
complete multiplicativity is needed for applications in Dirichlet characters and L-functions.

**Tractability**: 6/10 — Second arg multiplicativity follows from case analysis on
the Kronecker definition + Jacobi multiplicativity; generalized QR is harder and may
require additional Mathlib lemmas about fundamental discriminants.

## Why This Matters

1. **Completion of existing work**: File already proves first-arg multiplicativity (`kronecker_mul_left`);
   second-arg multiplicativity and generalized QR are the natural next steps.
2. **Upgrade gallery badge**: Once both are proved, status can move from `wip` to
   a complete formalization.
3. **Number theory depth**: Connects to class field theory, Dirichlet characters,
   binary quadratic forms.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `elementary-quadratic-reciprocity` | Parent proof (Gauss QR) |
| `elementary-quadratic-reciprocity-oq-03` | Jacobi symbol extension |
| `elementary-quadratic-reciprocity-oq-03-oq-02` | This file's gallery entry |
| `quadratic-reciprocity` | Classical QR via Mathlib |

## Lean File

`proofs/Proofs/ElementaryQuadraticReciprocityOQ03OQ02.lean`

The file is in namespace `KroneckerSymbol` and imports:
- `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`

Key definitions already in place:
- `kronecker2`, `kroneckerNeg1`, `kronecker0`, `kronecker`
- `kronecker_mul_left` (proved)

Missing:
- `kronecker_mul_right`
- Generalized quadratic reciprocity theorem

## Suggested Approach

1. **OBSERVE**: Read `ElementaryQuadraticReciprocityOQ03OQ02.lean` fully; check
   `jacobiSym.mul_right` in Mathlib for the Jacobi analogue.
2. **ORIENT**: `kronecker_mul_right` — case split on m = 0, -1, 1, general;
   the general case uses `jacobiSym.mul_right` plus sign character multiplicativity
   for the modulus sign.
3. **DECIDE**: If `jacobiSym.mul_right` is available in Mathlib 4.26, proceed directly;
   otherwise axiomatize and mark `by sorry` for Aristotle.
4. **ACT**: Prove `kronecker_mul_right`; attempt generalized QR or axiomatize it.
