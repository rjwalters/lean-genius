# Problem: Alternating Lucas Sum and Odd/Even-Indexed Partial Sums

**Slug**: fibonacci-identities-oq-08-oq-01
**Status**: Active
**Source**: proof-suggestion (open question from `fibonacci-identities-oq-08`)

## Problem Statement

### Formal Statement

Over $\mathbb{Z}$ (to handle the sign alternation), establish closed forms for:

$$
\sum_{i=0}^{n} (-1)^i L_i, \qquad \sum_{i=0}^{n} L_{2i}, \qquad \sum_{i=0}^{n} L_{2i+1},
$$

where $L_i$ is the $i$-th Lucas number ($L_0 = 2,\ L_1 = 1,\ L_{i+2} = L_{i+1} + L_i$).

The expected closed forms (to be confirmed and proved):
- $\sum_{i=0}^{n} L_{2i} = L_{2n+1} + 1$
- $\sum_{i=0}^{n} L_{2i+1} = L_{2n+2} - 2$
- $\sum_{i=0}^{n} (-1)^i L_i$ = a telescoping form in a single Lucas/Fibonacci term (determine exact constant).

### Plain Language

The parent entry proved ordinary partial-sum identities for Lucas numbers. This asks for the
*alternating* sum (with signs $(-1)^i$) and the sums restricted to even/odd indices, each in a
tidy closed form.

### Why This Matters

Alternating and bisected sums are the natural companions to the plain telescoping identities and
complete the "partial-sum family" for Lucas numbers. Signs force the work over $\mathbb{Z}$ rather
than $\mathbb{N}$, exercising the integer-indexed Lucas API.

## Known Results

### What's Already Proven

- Ordinary Lucas partial sums — parent entry `fibonacci-identities-oq-08` (Lucas-Number Partial-Sum Identities).
- `Nat.fib` / Lucas recurrence and Fibonacci–Lucas bridge identities in Mathlib and sibling gallery entries.

### Our Goal

Prove all three closed forms by induction (or telescoping of the Lucas recurrence), over $\mathbb{Z}$,
0 axioms, 0 sorries. Confirm the exact constants before committing.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-08 | Parent: plain Lucas partial sums | telescoping, induction |
| lucas-sum-oq-01 | Sibling: $\sum L_k = L_{n+2}-3$ | recurrence, telescoping |

## Initial Thoughts

### Potential Approaches

1. **Induction on the recurrence.** `Finset.sum_range_succ` + Lucas recurrence; `omega`/`ring`
   close the arithmetic. Even/odd sums: reindex `Finset.range` and telescope pairs.
2. **Telescoping.** Write each summand as a difference of consecutive (shifted) Lucas terms so the
   sum collapses. Handle the alternating sign by pairing consecutive terms.

### Key Difficulties

- Pinning the exact additive constant for each form.
- Sign alternation requires working in $\mathbb{Z}$; keep casts consistent.
