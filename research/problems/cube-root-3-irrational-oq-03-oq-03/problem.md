# Problem: Generalize the whole development to ∛p for an arbitrary prime p (or to X^n − ...

**Slug**: cube-root-3-irrational-oq-03-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Generalize the whole development to ∛p for an arbitrary prime p (or to X^n − p, Eisenstein at p), giving [ℚ(ⁿ√p):ℚ] = n uniformly.

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"∛3 has degree 3 over ℚ: irreducibility of X³ − 3 and [ℚ(∛3):ℚ] = 3" (cube-root-3-irrational-oq-03). It records a natural next step flagged during
formalization: Generalize the whole development to ∛p for an arbitrary prime p (or to X^n − p, Eisenstein at p), giving [ℚ(ⁿ√p):ℚ] = n uniformly.

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: ∛3 has degree 3 over ℚ: irreducibility of X³ − 3 and [ℚ(∛3):ℚ] = 3 (`cube-root-3-irrational-oq-03`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Generalize the whole development to ∛p for an arbitrary prime p (or to X^n − p, Eisenstein at p), giving [ℚ(ⁿ√p):ℚ] = n uniformly.

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `cube-root-3-irrational-oq-03` — parent proof / direct source of this open question.

## Tags

irrationality, number-theory, field-theory, minimal-polynomial, irreducibility, linear-algebra, cube-roots
