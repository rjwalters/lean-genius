# Problem: Legendre's Formula for Multinomial Coefficients (Kummer Carry Count)

**Slug**: wilsons-theorem-oq-03-oq-01
**Created**: 2026-07-01T22:11:21-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a prime $p$ and natural numbers $n_1, n_2, \ldots, n_k$ with $n = \sum_{i=1}^k n_i$, the $p$-adic valuation of the multinomial coefficient $\binom{n}{n_1, n_2, \ldots, n_k} = \dfrac{n!}{n_1!\, n_2! \cdots n_k!}$ satisfies

$$
(p - 1)\, \nu_p\!\left(\frac{n!}{n_1!\cdots n_k!}\right) \;=\; \left(\sum_{i=1}^k S_p(n_i)\right) - S_p(n),
$$

equivalently

$$
\nu_p\!\left(\binom{n}{n_1,\ldots,n_k}\right) \;=\; \frac{\sum_{i=1}^k S_p(n_i) - S_p\!\left(\sum_{i=1}^k n_i\right)}{p - 1} \;=\; (\text{number of carries when adding } n_1,\ldots,n_k \text{ in base } p),
$$

where $S_p(m) = \sum_j d_j$ is the sum of the base-$p$ digits of $m$. This is the multinomial generalization of Kummer's theorem, reducing to Legendre's formula when $k = 1$ and to Kummer's binomial carry count when $k = 2$.

### Plain Language

Legendre's formula tells you exactly how many times a prime $p$ divides $n!$. This problem asks for the analogous exact count for a *multinomial* coefficient — the number of ways to split $n$ objects into groups of sizes $n_1, \ldots, n_k$. The answer has a strikingly concrete combinatorial form: it equals the total number of carries you perform when you add $n_1 + n_2 + \cdots + n_k$ in base $p$. For $k = 2$ this is exactly Kummer's classical theorem about binomial coefficients; we want the general-$k$ statement, formalized in Lean.

### Why This Matters

- **Integrality**: The formula immediately re-proves that multinomial coefficients are integers — every carry count is a nonnegative integer, so $\nu_p \geq 0$ for all $p$.
- **Kummer's theorem generalized**: It unifies Legendre ($k=1$) and Kummer ($k=2$) under one carry-counting principle and exposes the digit-sum subadditivity $S_p(\sum n_i) \leq \sum S_p(n_i)$ as the arithmetic engine behind divisibility of multinomials.
- **Effective computation**: It gives an $O(\log n)$ way to compute the exact prime factorization of a multinomial coefficient, useful for computing multinomials mod $p^e$ and in combinatorial number theory.
- **Gallery completeness**: The parent entry (Legendre's formula) explicitly lists this as an open question; formalizing it closes a stated gap and extends the digit-sum toolkit already present in Mathlib.

## Known Results

### What's Already Proven

- Legendre's formula $(p-1)\,\nu_p(n!) = n - S_p(n)$ — parent gallery proof `wilsons-theorem-oq-03`, wrapping Mathlib `sub_one_mul_padicValNat_factorial`.
- Kummer's theorem for binomials, $\nu_p\binom{m+n}{m}$ = number of base-$p$ carries in $m + n$ — classical (Kummer, 1852); cross-referenced from the parent as `kummer-theorem-oq-01`.
- $\nu_p$ is additive on products of nonzero naturals — Mathlib `padicValNat.mul`.
- The Finset-sum form $\nu_p(n!) = \sum_{i} \lfloor n/p^i \rfloor$ — Mathlib `Nat.Prime.factorization_factorial` / `padicValNat_factorial`.
- The digit-sum recurrence and one-digit lemma $S_p(m) = m$ for $m < p$ — parent's `digit_sum_pred_prime` and Mathlib `Nat.digits`.

### What's Still Open

- A Lean formalization of the multinomial ($k \geq 3$) digit-sum valuation identity; Mathlib has Legendre but not the general multinomial carry count.
- A clean Lean statement identifying $(\sum S_p(n_i) - S_p(n))/(p-1)$ with an actual base-$p$ carry count for the $k$-fold sum (the combinatorial reading).

### Our Goal

Formalize and verify in Lean 4 the digit-sum identity $(p-1)\,\nu_p\big(n!/\prod n_i!\big) = \sum_i S_p(n_i) - S_p(n)$ for $n = \sum_i n_i$, as a `Finset`-indexed theorem over $k$ parts, with the $k = 2$ Kummer corollary as a specialization. Deriving the explicit carry-count interpretation is a stretch goal; the digit-sum form is the primary deliverable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| wilsons-theorem-oq-03 | Direct parent — Legendre's formula $(p-1)\nu_p(n!) = n - S_p(n)$, the $k=1$ base case | `sub_one_mul_padicValNat_factorial`, `Nat.digits`, digit-sum lemmas |
| wilsons-theorem | Root theorem; Legendre gives the non-divisibility direction via $S_p(p-1)=p-1$ | `padicValNat`, factorial arithmetic |
| binomial-theorem | Binomial/multinomial coefficient identities and their integrality | `Nat.choose`, `Nat.multinomial`, factorial factorization |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Sum Legendre over the parts and telescope**: Write $\nu_p(n!/\prod n_i!) = \nu_p(n!) - \sum_i \nu_p(n_i!)$ using additivity of $\nu_p$ (Mathlib `padicValNat.mul`, applied over the `Finset` product with `Finset.prod`). Substitute Legendre's formula for each factor: $(p-1)\nu_p(n!) = n - S_p(n)$ and $(p-1)\nu_p(n_i!) = n_i - S_p(n_i)$. Since $n = \sum n_i$, the $n$ and $n_i$ terms cancel, leaving $(p-1)\nu_p(\cdots) = \sum_i S_p(n_i) - S_p(n)$.
   - Why it might work: Every ingredient is already in Mathlib and the parent entry. The cancellation is pure arithmetic (`omega` / `Finset.sum_sub_distrib`), and no new hard analysis is needed.
   - Risk: Bookkeeping over a `Finset` index and nonzeroness side-conditions ($n_i! \neq 0$, needed for `padicValNat.mul`) can be fiddly; must handle the subtraction in $\mathbb{N}$ carefully (work in $\mathbb{Z}$ or show $\sum S_p(n_i) \geq S_p(n)$ first).

2. **Approach B — Induct on $k$ via the binomial Kummer result**: Peel off one part at a time, $\binom{n}{n_1,\ldots,n_k} = \binom{n}{n_k}\binom{n - n_k}{n_1,\ldots,n_{k-1}}$, and add the binomial Kummer carry counts. Base case $k=1$ is trivial ($\nu_p = 0$); inductive step uses the binomial identity plus $S_p$ subadditivity to accumulate carries.
   - Why it might work: Reuses the (already classical, cross-referenced) binomial Kummer statement as a black box, so each step is a single application.
   - Risk: Requires the binomial Kummer theorem to already exist as a usable Lean lemma; if only Legendre is formalized, Approach A is more self-contained. Carry-count accumulation is more delicate to state than the digit-sum form.

### Key Difficulties

- **Digit-sum subadditivity and $\mathbb{N}$-subtraction**: $S_p\big(\sum n_i\big) \leq \sum S_p(n_i)$ must be established (each carry drops the total digit sum by exactly $p-1$) so the natural-number subtraction $\sum S_p(n_i) - S_p(n)$ is well-defined and nonnegative; cleanest to derive it from the valuation being $\geq 0$ rather than proving subadditivity independently.
- **Carry accounting**: Identifying the arithmetic quantity $(\sum S_p(n_i) - S_p(n))/(p-1)$ with an actual base-$p$ carry count for a $k$-fold sum requires a careful definition of "number of carries" when more than two summands are added (carries can exceed 1 per position).
- **Finset bookkeeping**: Handling nonzeroness hypotheses and the interplay of `Finset.prod`/`Finset.sum` with `padicValNat` additivity across an arbitrary index set.

### What Would a Proof Need?

- Key lemma 1: Additivity of $\nu_p$ over a finite product, $\nu_p(\prod_i n_i!) = \sum_i \nu_p(n_i!)$, via `padicValNat.mul` and `Finset.prod` induction.
- Key lemma 2: Legendre applied per part, $(p-1)\nu_p(n_i!) = n_i - S_p(n_i)$, plus the summed cancellation $\sum_i n_i = n$.
- Technical requirements: work the subtraction in $\mathbb{Z}$ (or prove $\sum S_p(n_i) \geq S_p(n)$ first), nonzeroness of factorials, and `Fact p.Prime` instances for the Mathlib API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already provides the factorial factorization lemma (`Nat.Prime.factorization_factorial` / `sub_one_mul_padicValNat_factorial`), so the $k=1$ ingredient is free.
- The parent gallery proof `wilsons-theorem-oq-03` supplies the digit-sum machinery and the exact API pattern to imitate.
- The core argument is a finite-sum cancellation (Approach A) rather than new deep mathematics; the main effort is `Finset` bookkeeping and the $\mathbb{N}$-subtraction care.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 2–4 days
- If hard: 1 week (mainly if the carry-count combinatorial interpretation is pursued in full)

## References

### Papers
- A.-M. Legendre, *Essai sur la théorie des nombres* — the original $p$-adic valuation of $n!$ formula.
- E. E. Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen* — the binomial carry-count theorem this problem generalizes.
- G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* — digit sums, factorial valuations, and multinomial integrality.

### Online Resources
- https://en.wikipedia.org/wiki/Legendre%27s_formula — Legendre's formula and its digit-sum form.
- https://en.wikipedia.org/wiki/Kummer%27s_theorem — Kummer's carry-count theorem for binomials.

### Mathlib
- `Mathlib.NumberTheory.Padics.PadicVal.Basic` — `sub_one_mul_padicValNat_factorial` ($(p-1)\nu_p(n!) = n - S_p(n)$) and `padicValNat_factorial` (Finset sum form).
- `Mathlib.NumberTheory.Padics.PadicVal.Basic` — `padicValNat.mul` (additivity of $\nu_p$ on nonzero products), the engine for splitting $\prod n_i!$.
- `Mathlib.Data.Nat.Digits` — `Nat.digits` and digit-sum lemmas providing $S_p$ and the one-digit fact $S_p(m) = m$ for $m < p$.
- `Mathlib.Data.Nat.Choose.Multinomial` — `Nat.multinomial` and its factorial-quotient characterization for stating the coefficient.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_sub_distrib` / `Finset.prod` for the $k$-fold cancellation and `Nat.sub_one_mul` for the $(p-1)$ factoring.

## Metadata

```yaml
tags:
  - number-theory
  - p-adic
  - factorial
  - legendre
  - digit-sum
  - multinomial
related_proofs:
  - wilsons-theorem-oq-03
  - wilsons-theorem
  - binomial-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:21-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
