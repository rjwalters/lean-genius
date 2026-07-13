# Problem: Generalize the contrapositive certificate to a decidable test on concrete gro...

**Slug**: cauchy-group-theorem-oq-01-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Generalize the contrapositive certificate to a decidable test on concrete groups: an algorithm that, given a finite group presentation, certifies the set of primes dividing |G| by exhibiting order-p elements (or their absence).

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"Cauchy's theorem for finite groups and its classical corollaries" (cauchy-group-theorem-oq-01). It records a natural next step flagged during
formalization: Generalize the contrapositive certificate to a decidable test on concrete groups: an algorithm that, given a finite group presentation, certifies the set of primes dividing |G| by exhibiting order-p elements (or their absence).

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: Cauchy's theorem for finite groups and its classical corollaries (`cauchy-group-theorem-oq-01`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Generalize the contrapositive certificate to a decidable test on concrete groups: an algorithm that, given a finite group presentation, certifies the set of primes dividing |G| by exhibiting order-p elements (or their absence).

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `cauchy-group-theorem-oq-01` — parent proof / direct source of this open question.

## Tags

algebra, group-theory, finite-groups, cauchy-theorem, order-of-element, sylow, involution, classic
