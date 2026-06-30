# Problem: Kaprekar's Constant 6174

**Slug**: kaprekar-constant-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \in \{1000, \dots, 9999\}\ \text{with non-identical digits},\quad \exists k \le 7,\ T^{k}(n) = 6174,
$$

where $T(n) = D(n) - A(n)$, $D(n)$ is the integer formed by writing $n$'s decimal
digits in descending order, and $A(n)$ the integer from the same digits in ascending
order. Moreover $T(6174) = 6174$ is the unique nonzero fixed point of $T$ on this domain.

### Plain Language

Take any four-digit number whose digits are not all the same. Arrange its digits
into the largest and smallest numbers possible and subtract. Repeat. No matter where
you start, you reach 6174 — Kaprekar's constant — in at most seven steps, and once
there you stay there.

### Why This Matters

A clean, fully decidable dynamical-systems fact over a finite domain: a single global
attractor reached in bounded time. It is an appealing formalization target because the
entire statement can be discharged by finite computation (`decide`/`Finset` enumeration),
yet stating the digit map and the bounded-convergence claim precisely is non-trivial.

## Known Results

### What's Already Proven

- The result is classical (D. R. Kaprekar, 1949) and verified by exhaustive computer search.
- Analogous Kaprekar fixed points exist in other digit lengths (e.g. 495 for 3 digits); 4 and 3 digits are the only lengths with a single nonzero fixed point.

### What's Still Open

- Nothing mathematically open at 4 digits; the task is a faithful Lean formalization.
- Optional extension: characterize the full set of Kaprekar cycles for 5+ digit numbers.

### Our Goal

Formalize the four-digit case: define the digit-sort subtraction map `T` on `Fin 10000`
(restricted to non-repdigit inputs), and prove that iterating `T` at most 7 times yields
6174, with 6174 the unique nonzero fixed point.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| niven-theorem-oq-01 | digit-based number theory in Lean | digit extraction, `Nat.digits` |
| thue-morse-oq-01 | finite digit/dynamical structure | recurrence over digit data |

## Initial Thoughts

### Potential Approaches

1. **Exhaustive `decide` / `Finset` enumeration**: Define `T` computably, then prove the
   bounded-convergence claim by evaluating `T^[7]` on all valid inputs.
   - Why it might work: domain is finite (9000 numbers) and `T` is a closed-form computable function.
   - Risk: kernel `decide` over 9000 inputs with iterated digit sorts may be slow; may need `native_decide` care or a reduced reachable-set argument.

2. **Reachable-set contraction**: Show one step maps every input into a small invariant
   set, then finish by enumerating only that set.
   - Why it might work: drastically shrinks the search space after step 1.
   - Risk: more lemmas to state; the set must be identified and proven invariant.

### Key Difficulties

- Defining $D(n)$ and $A(n)$ (descending/ascending digit reassembly) cleanly and computably.
- Keeping the enumeration within reasonable kernel-reduction cost.

### What Would a Proof Need?

- Key lemma 1: `T` is well-defined and computable on `Fin 10000`.
- Key lemma 2: `T(6174) = 6174` and no other nonzero fixed point exists.
- Technical requirements: `Nat.digits`, list sort, `Finset` enumeration / `decide`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Statement is finite and decidable, so no deep theory is required.
- Main effort is engineering a computable digit map and controlling reduction cost.
- Mathlib provides `Nat.digits`, list sorting, and `Finset` enumeration.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: days (mostly performance tuning)

## References

### Papers
- D. R. Kaprekar, "Another solitaire game", Scripta Mathematica, 1949 — original description.

### Online Resources
- https://en.wikipedia.org/wiki/6174 — overview of Kaprekar's constant and the routine.

### Mathlib
- `Mathlib.Data.Nat.Digits` — decimal digit extraction.
- `Mathlib.Data.Finset.Basic` — finite enumeration for the decidable claim.

## Metadata

```yaml
tags:
  - number-theory
  - digits
  - kaprekar
  - fixed-point
  - decidable
related_proofs:
  - niven-theorem-oq-01
  - thue-morse-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
