# Problem: k-Fold "No Element Divides k Others" Sets

**Slug**: erdos-1062-oq-04
**Created**: 2026-06-17
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
f_k(n) \;=\; \max\Big\{\,|A| : A \subseteq \{1,\dots,n\},\ \forall a \in A,\ \#\{\,b \in A : b \neq a,\ b \mid a\,\} < k \,\Big\}.
$$

For $k = 2$ this is the "no element divides two others" (NDTO) extremal function
$f(n) = f_2(n)$ studied in Erdős Problem #1062, for which the lower bound
$f(n) \ge \lceil 2n/3 \rceil$ is known. The task is to formalize the $k$-fold
generalization and establish bounds on $f_k(n)$.

### Plain Language

The parent problem asks for the largest subset of $\{1,\dots,n\}$ in which no
element divides *two* distinct others (NDTO). The $k=1$ case is exactly a
*primitive set* (no element divides any other), which has density $0$; the $k=2$
case (NDTO) jumps to density $\ge 2/3$. This generalization asks: what happens for
general $k$ — sets where no element divides $k$ distinct others? We expect the
extremal density to increase with $k$, interpolating between primitive sets and
the full interval, and we want to formalize a constructive lower bound and, if
possible, a matching upper bound.

### Why This Matters

This is a clean structural generalization that situates Erdős #1062 inside a
one-parameter family bridging two well-studied regimes (primitive sets at $k=1$,
NDTO at $k=2$). Establishing $f_k(n)$ growth clarifies *why* the density jumps
between $k=1$ and $k=2$, and the constructions reuse the interval and
prime-layer ideas already formalized for the parent.

## Known Results

### What's Already Proven

- Parent gallery entry `erdos-1062` (`proofs/Proofs/Erdos1062.lean`, 0 sorries): lower bound $f(n) \ge \lceil 2n/3 \rceil$ via the interval $[\lfloor n/3 \rfloor + 1, n]$, the primitive-vs-NDTO comparison, and the $\{2,6,9\}$ counterexample
- Density $0$ for primitive sets ($k=1$) is classical (Behrend/Erdős)

### What's Still Open

- A general lower bound $f_k(n) \ge c_k\, n$ with an explicit constructive family
- Upper bounds / matching asymptotics for $f_k(n)$, $k \ge 2$
- The precise transition behavior of $c_k$ as $k$ grows

### Our Goal

Formalize the $k$-parameterized predicate `NoDividesKOthers k A` and prove a clean
constructive lower bound — at minimum recovering the $k=2$ result as a special
case, then generalizing the interval construction to obtain $f_k(n) \ge
\lceil (1 - 1/(k+1))\, n \rceil$ or the best constant the construction supports.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1062 | Parent: NDTO ($k=2$) lower bound, predicate, and counterexample scaffolding | Finset filters, divisibility counting, interval constructions |
| primitive sets / Behrend-type entries | $k=1$ boundary case (density 0) | divisibility, density |

## Initial Thoughts

### Potential Approaches

1. **Approach A — generalized interval construction**: Take the top block
   $(\lfloor n/(k+1) \rfloor, n]$ (or a union of upper blocks) and bound how many
   multiples of each element survive. Show each element divides $< k$ others.
   - Why it might work: directly generalizes the parent's $[n/3+1, n]$ NDTO construction.
   - Risk: the exact density constant for general $k$ may need a sharper block choice.

2. **Approach B — prime-layered construction**: Partition by largest-prime-factor
   layers and keep the top $k$ layers, counting divisibility chains of length $\le k$.
   - Why it might work: chains of divisors correspond to "divides-others" multiplicity.
   - Risk: layer bookkeeping is heavier; may overshoot the needed bound.

### Key Difficulties

- Formalizing the "$< k$ divisors inside $A$" predicate and its Finset cardinality
- Choosing a construction whose density is provable in Lean without delicate estimates
- Avoiding off-by-one issues that the parent's $k=2$ proof already had to handle

### What Would a Proof Need?

- Key lemma 1: a `Finset`-level definition `(A.filter (· ∣ a)).card < k` capturing the constraint
- Key lemma 2: for the chosen block, each element's in-set proper multiples number $< k$
- Technical requirements: `Nat.card_multiples`-style counts, `Finset.filter` cardinality, interval reasoning

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The $k=2$ case is fully formalized; generalizing the predicate is mechanical.
- The interval construction lower bound generalizes with elementary divisor counts.
- The matching upper bound (if attempted) is harder and may stay open.

**Estimated Effort**:
- Exploration: hours to a day
- If tractable (predicate + generalized lower bound): days
- If hard (sharp upper bound): unknown

## References

### Papers
- P. Erdős, "On the density of some sequences of integers", Bull. Amer. Math. Soc. 54 (1948) — primitive sets background.
- Erdős Problem #1062 source notes (extremal "no divides two others" sets).

### Online Resources
- https://www.erdosproblems.com/1062 — Erdős Problem #1062 statement and references.

### Mathlib
- `Mathlib.NumberTheory` divisibility / `Nat.divisors` API — counting divisors and multiples.
- `Finset.filter`, `Finset.card_filter` — defining and bounding the constraint set.

## Metadata

```yaml
tags:
  - number-theory
  - combinatorics
  - divisibility
  - extremal-set-theory
related_proofs:
  - erdos-1062
difficulty: medium
source: proof-suggestion
created: 2026-06-17
```
