# Problem: Fibonacci Pairs as the Unique Euclidean Worst Case

**Slug**: gcd-algorithm-oq-01-oq-05
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Strengthen Lamé's worst-case theorem to a *uniqueness* statement. Let $s(a,b)$ denote the
number of division steps the Euclidean algorithm takes on the pair $(a,b)$ with $a > b \ge 1$.
Then for every $n$:

$$
s(a,b) \ge n \;\Longrightarrow\; a \ge F_{n+2}\ \text{and}\ b \ge F_{n+1},
$$

and consecutive Fibonacci numbers are the **unique** minimizers: among all pairs with
$s(a,b) = n$, the pair $(F_{n+2}, F_{n+1})$ is the only one attaining the smallest possible
$b$ (equivalently, the only pair below a size bound realizing the maximum step count).

### Plain Language

The parent proved Lamé's theorem: consecutive Fibonacci numbers are *a* worst case for the
Euclidean algorithm (they force the maximum number of steps relative to their size). This
child proves they are the *only* worst case — no other pair of the same or smaller size takes
as many steps. This pins down the extremal structure of the algorithm.

### Why This Matters

Uniqueness of the extremal input turns "Fibonacci is worst" into "Fibonacci is *exactly* the
worst," which is the sharp form of the complexity bound. It also isolates a clean inductive
characterization of remainder sequences that is reusable for tighter step-count estimates.

## Known Results

### What's Already Proven

- Parent `gcd-algorithm-oq-01`: Lamé's theorem (Fibonacci realizes the worst-case step count).
- Mathlib `Nat.fib`, `Nat.fib_add_two`, `Nat.fib_lt_fib_succ`, `Nat.fib_le_fib_succ`,
  monotonicity `Nat.fib_mono`, and `Nat.gcd` / Euclidean recursion lemmas.

### What's Still Open (in this child)

- The lower bounds $a \ge F_{n+2}$, $b \ge F_{n+1}$ from $s(a,b) \ge n$ (the standard Lamé induction).
- The *uniqueness* upgrade: equality $b = F_{n+1}$ with $s(a,b)=n$ forces $(a,b) = (F_{n+2},F_{n+1})$.

### Our Goal

Prove the two-sided extremal characterization by induction on the number of steps: each
division step $a = qb + r$ with $q \ge 1$ (and $q \ge 2$ except at the top) forces the pair to
dominate the corresponding Fibonacci pair, and equality throughout forces $q = 1$ at every
step, i.e. exactly the Fibonacci recurrence.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| gcd-algorithm-oq-01 | parent: Lamé worst-case bound | Euclidean recursion, Fibonacci |
| gcd-algorithm-oq-01-oq-04 | binary/Stein complexity (sibling) | step-count analysis |
| fibonacci-identities-* | Fibonacci monotonicity/growth lemmas | `Nat.fib` API |

## Initial Thoughts

### Potential Approaches

1. **Induction on step count with tight quotient tracking**: define the step function on
   $(a,b)$, prove $s(a,b) \ge n \Rightarrow a \ge F_{n+2} \wedge b \ge F_{n+1}$ by strong
   induction. For uniqueness, track that equality in the bound requires quotient $=1$ at each
   step (the sub-Fibonacci minimality lemma), which reconstructs $(F_{n+2}, F_{n+1})$.
   - Why it might work: standard Lamé induction; Mathlib has all `Nat.fib` monotonicity facts.
   - Risk: formalizing "quotient $\ge 2$ strictly increases the bound" to get strict uniqueness.

2. **Reverse construction**: show any remainder sequence with $n$ steps and minimal top term
   equals the Fibonacci sequence run backwards ($r_{i} = r_{i+1} + r_{i+2}$).
   - Why it might work: makes uniqueness structural rather than inequality-chasing.
   - Risk: requires defining the remainder sequence as a first-class object.

### Key Difficulties

- Encoding the Euclidean step-count $s(a,b)$ in Lean (well-founded recursion on $b$).
- The strictness needed for *uniqueness* (a non-Fibonacci pair strictly exceeds the bound).

### What Would a Proof Need?

- A step-count function with `Nat.gcd`-style well-founded recursion and its unfolding lemma.
- Fibonacci monotonicity and the strict inequality $F_{n+2} > F_{n+1}$ (Mathlib).
- The minimality/uniqueness lemma: equality in the Lamé bound forces every quotient to be $1$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The existence half (Lamé) is classical and the parent already has it; Mathlib has `Nat.fib`.
- The uniqueness upgrade is a bounded strengthening, not a new theory.

**Estimated Effort**:
- Exploration: hours–1 day (defining/reusing the step-count function)
- If tractable: 2–4 days

## References

### Papers
- Lamé (1844); Knuth, *TAOCP* Vol. 2 §4.5.3 — Euclidean-algorithm worst case and Fibonacci.

### Mathlib
- `Nat.fib`, `Nat.fib_add_two`, `Nat.fib_lt_fib_succ`, `Nat.fib_mono` — Fibonacci growth.
- `Nat.gcd` recursion / well-founded step definitions.

## Metadata

```yaml
tags:
  - number-theory
  - euclidean-algorithm
  - fibonacci
  - gcd
related_proofs:
  - gcd-algorithm-oq-01
  - fibonacci-identities
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
