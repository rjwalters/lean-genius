# Problem: Lucas Analogue of a Weighted Fibonacci Sum

**Slug**: lucas-sum-oq-01-oq-02
**Status**: Active
**Source**: proof-suggestion (open question from `lucas-sum-oq-01`)

## Problem Statement

### Formal Statement

Derive a Lucas analogue of one of the classical weighted Fibonacci sums — either

$$
\sum_{k=1}^{n} k\,F_k, \qquad\text{or}\qquad \sum_{k=1}^{n} F_k^2 = F_n F_{n+1},
$$

and relate it to the Fibonacci version through the bridge identity

$$
L_{n+1} = F_n + F_{n+2}.
$$

Concretely: prove a closed form for $\sum_{k=1}^{n} k\,L_k$ (and/or $\sum_{k=1}^{n} L_k^2$) and
express it in terms of Lucas/Fibonacci values, deriving it from (or reconciling it with) the
Fibonacci analogue via the $L = F_{\cdot} + F_{\cdot}$ bridge.

### Plain Language

The parent proved $\sum_{k=1}^{n} L_k = L_{n+2} - 3$. This asks for a *weighted* sum — either
$\sum k L_k$ or $\sum L_k^2$ — in closed form, and to connect it explicitly to the corresponding
Fibonacci identity through the standard Fibonacci–Lucas bridge.

### Why This Matters

Weighted and squared sums are the next tier of partial-sum identities. Routing the Lucas result
through the Fibonacci one demonstrates the bridge $L_{n+1}=F_n+F_{n+2}$ as a reusable transfer tool.

## Known Results

### What's Already Proven

- $\sum_{k=1}^{n} L_k = L_{n+2} - 3$ — parent entry `lucas-sum-oq-01`.
- Fibonacci $\sum F_k^2 = F_n F_{n+1}$ and $\sum k F_k$ identities (gallery `fibonacci-identities-*`, Mathlib `Nat.fib`).

### Our Goal

Prove a closed form for $\sum_{k=1}^{n} k\,L_k$ (primary target) and, if clean, $\sum_{k=1}^{n} L_k^2$,
0 axioms, 0 sorries, with the Fibonacci-bridge connection made explicit.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lucas-sum-oq-01 | Parent: $\sum L_k = L_{n+2}-3$ | telescoping, induction |
| fibonacci-identities-* | Weighted/squared Fibonacci sums | induction, Cassini |

## Initial Thoughts

### Potential Approaches

1. **Direct induction** with `Finset.sum_range_succ`; `ring`/`omega` on the Lucas recurrence.
2. **Abel summation / bridge transfer.** Expand $L_k = F_{k-1}+F_{k+1}$, reuse the known Fibonacci
   weighted-sum results, recombine.

### Key Difficulties

- Getting the additive/multiplicative constants exactly right.
- Index base cases ($k$ starting at 1) and cast hygiene between $\mathbb{N}$ and $\mathbb{Z}$.
