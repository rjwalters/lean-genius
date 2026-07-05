# Problem: Generalize casting out nines to arbitrary moduli: digit-sum mod d is preserve...

**Slug**: divisibility-by-three-oq-01-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Generalize casting out nines to arbitrary moduli: digit-sum mod d is preserved under addition and multiplication whenever b ≡ 1 (mod d)

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"Divisibility By Three OQ-01: General Last-k-Digits, Powers of 2 and 5, and Digital Root Theory" (divisibility-by-three-oq-01). It records a natural next step flagged during
formalization: Generalize casting out nines to arbitrary moduli: digit-sum mod d is preserved under addition and multiplication whenever b ≡ 1 (mod d)

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: Divisibility By Three OQ-01: General Last-k-Digits, Powers of 2 and 5, and Digital Root Theory (`divisibility-by-three-oq-01`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Generalize casting out nines to arbitrary moduli: digit-sum mod d is preserved under addition and multiplication whenever b ≡ 1 (mod d)

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `divisibility-by-three-oq-01` — parent proof / direct source of this open question.

## Tags

number-theory, divisibility, digit-sum, modular-arithmetic, three
