# Problem: Generalized Ballot / Cycle-Lemma Count C(2n,n) − C(2n,n+k)

**Slug**: catalan-numbers-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For integers $n \ge 0$ and $k \ge 1$, the number of lattice paths from $(0,0)$ with $2n$ unit up/down steps that stay strictly within a band determined by $k$ (the generalized ballot condition) equals

$$
\binom{2n}{n} - \binom{2n}{\,n+k\,},
$$

with the reflection / André formula and the Catalan number $C_n = \binom{2n}{n} - \binom{2n}{n+1}$ recovered as the case $k = 1$.

### Plain Language

The classic ballot problem and the Catalan numbers both count lattice paths that never cross a boundary, and the count is obtained by the *reflection principle*: subtract the "bad" paths (which can be reflected into a shifted binomial count) from all paths, giving $\binom{2n}{n} - \binom{2n}{n+1}$ for the Catalan case. This problem generalizes the boundary by a parameter $k$, so the count becomes $\binom{2n}{n} - \binom{2n}{n+k}$, and asks to formalize this generalized ballot/cycle-lemma identity in Lean, recovering the parent's reflection form when $k=1$.

### Why This Matters

The generalized ballot numbers $\binom{2n}{n}-\binom{2n}{n+k}$ unify the Catalan numbers, the ballot problem, and the cycle lemma — central objects in enumerative combinatorics with applications to random walks, queues, and Young tableaux. Capturing the $k$-parameter family as a single theorem turns the parent's specific Catalan reflection into a reusable reflection-principle lemma and sets up downstream entries (Dyck-path refinements, ballot sequences, hook-length corollaries).

## Known Results

### What's Already Proven

- Parent `catalan-numbers-oq-01-oq-01-oq-01` (verified): the reflection-principle count for the Catalan case $C_n = \binom{2n}{n}-\binom{2n}{n+1}$.
- Mathlib: `Nat.choose`, `Nat.centralBinom`, `Nat.succ_mul_centralBinom_succ`, and `catalan` with `catalan_eq_centralBinom_div`/reflection lemmas.
- Classical: the André reflection principle and the cycle lemma giving $\binom{2n}{n}-\binom{2n}{n+k}$.

### What's Still Open

- A Lean statement of the generalized count $\binom{2n}{n}-\binom{2n}{n+k}$ for the $k$-band ballot condition, with the parent's $k=1$ Catalan form as a corollary.
- A clean encoding of the "stays strictly within the $k$-band" path predicate and the reflecting bijection onto bad paths.

### Our Goal

Define the bad-path set for the generalized boundary, exhibit the reflecting bijection onto paths counted by $\binom{2n}{n+k}$, and conclude the good-path count is $\binom{2n}{n}-\binom{2n}{n+k}$, specializing to the Catalan reflection at $k=1$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| catalan-numbers-oq-01-oq-01-oq-01 | Direct parent; Catalan reflection count | reflection principle, central binomials |
| catalan-numbers-oq-01 | Root entry; Catalan numbers and recurrences | enumerative combinatorics |

## Initial Thoughts

### Potential Approaches

1. **Reflection bijection at level $k$.** Encode paths as step sequences, define the first-passage reflection that maps bad paths bijectively to paths ending at the reflected height, and count the image with `Nat.choose (2n) (n+k)`.
   - Why it might work: directly generalizes the parent's $k=1$ bijection; the reflection map is the same first-passage swap with a $k$-shifted boundary.
   - Risk: formalizing the first-passage index and proving the reflection is an involution/bijection on the bad set.

2. **Algebraic identity route.** If the path model is already a binomial difference, prove the generalized closed form by binomial manipulation and recover $k=1$ by rewriting.
   - Why it might work: avoids re-deriving the bijection if Mathlib/the parent already exposes a counting lemma parameterized by the shift.
   - Risk: the combinatorial meaning (which paths are counted) must still be tied to the binomial difference to be a faithful generalization.
