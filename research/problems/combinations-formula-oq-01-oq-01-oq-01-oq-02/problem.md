# Problem: Lucas analogue of Cassini's identity

**Slug**: combinations-formula-oq-01-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
L_{n-1}\,L_{n+1} - L_n^{\,2} = (-1)^{n-1}\cdot 5 \qquad (n \ge 1)
$$

where $L_n$ are the Lucas numbers $L_0 = 2,\; L_1 = 1,\; L_{n+2} = L_{n+1} + L_n$.

### Plain Language

Cassini's identity for Fibonacci numbers says $F_{n-1}F_{n+1} - F_n^2 = (-1)^n$.
The Lucas numbers satisfy the same recurrence but with seeds $2, 1$, and their
Cassini-type identity carries an extra factor of $5$ (because the "discriminant"
of the Lucas sequence is $5$): $L_{n-1}L_{n+1} - L_n^2 = (-1)^{n-1}\cdot 5$. The
goal is an axiom-free Lean proof over $\mathbb{Z}$.

### Why This Matters

The Lucas Cassini identity is the companion of the classical Fibonacci Cassini
identity already in the gallery; the factor of $5$ encodes the link
$L_n^2 - 5F_n^2 = 4(-1)^n$ between the two sequences. It is a clean induction
that strengthens the gallery's Fibonacci/Lucas coverage.

## Known Results

### What's Already Proven

- Mathlib has Fibonacci numbers (`Nat.fib`) and the Fibonacci Cassini identity
  (`Nat.fib_add_two`, `Int` Cassini variants in the gallery).
- The parent gallery proof `combinations-formula-oq-01-oq-01-oq-01` establishes
  the diagonal-sum Lucas framework (verified, 0-axiom).

### What's Still Open

- A registered Lean definition of Lucas numbers over $\mathbb{Z}$ (or reuse of
  `2 * fib (n+1) - fib n`) and a proof of the Cassini-with-5 identity.

### Our Goal

Define $L_n$ (directly by recurrence over $\mathbb{Z}$, or via
$L_n = F_{n-1} + F_{n+1} = 2F_{n+1} - F_n$) and prove
$L_{n-1}L_{n+1} - L_n^2 = (-1)^{n-1}\cdot 5$ for $n \ge 1$ by two-step induction
(or by reducing to the Fibonacci Cassini identity plus $L_n^2 - 5F_n^2 = 4(-1)^n$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-01-oq-01-oq-01 | Direct parent; Lucas diagonal sums | Pascal diagonals |
| fibonacci-identities-oq-01-oq-03 | Fibonacci Cassini via Q-matrix determinant | matrix determinant |

## Initial Thoughts

### Potential Approaches

1. **Two-step induction on the recurrence**: track
   $L_{n-1}L_{n+1} - L_n^2$ and show it flips sign each step.
   - Why it might work: the recurrence makes the difference telescope to
     $-(L_{n-2}L_n - L_{n-1}^2)$.
   - Risk: base-case sign bookkeeping for $(-1)^{n-1}$.

2. **Reduce to Fibonacci**: use $L_n = F_{n-1}+F_{n+1}$ and the known Fibonacci
   Cassini identity plus $L_n^2 - 5F_n^2 = 4(-1)^n$.
   - Why it might work: leverages Mathlib's `Nat.fib` Cassini machinery.
   - Risk: casting `Nat.fib` to $\mathbb{Z}$ and managing $n-1$ index shifts.

### Key Difficulties

- Handling the $(-1)^{n-1}$ sign cleanly (work over $\mathbb{Z}$, not $\mathbb{N}$).
- Index shifts at $n = 1$ when $L_{n-1} = L_0 = 2$.

### What Would a Proof Need?

- Key lemma 1: a Lucas recurrence lemma `L (n+2) = L (n+1) + L n`.
- Key lemma 2: the Fibonacci Cassini identity over $\mathbb{Z}$ (or a direct
  inductive invariant).
- Technical requirements: `Int`, `ring`, two-step (strong) induction.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Pure recurrence induction; no deep Mathlib dependency required.
- The Fibonacci Cassini analogue has already been formalized in the gallery.
- `ring`/`omega`/`Int.induction`-style tactics handle the algebra.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1 day

## References

### Mathlib
- `Mathlib.Data.Nat.Fib.Basic` — `Nat.fib`, recurrence and identities.
- `Mathlib.Tactic.Ring` — closing the algebraic step.

## Metadata

```yaml
tags:
  - combinatorics
  - fibonacci
  - lucas-numbers
  - cassini
related_proofs:
  - combinations-formula-oq-01-oq-01-oq-01
  - fibonacci-identities-oq-01-oq-03
difficulty: low
source: gallery-gap
created: 2026-06-24
```
