# Problem: Closed-Form Type-Mass Distribution for Sums of Four Squares

**Slug**: four-square-distribution-oq-07
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a representation type $t$ of $n$ (a sorted tuple $a_1 \le a_2 \le a_3 \le a_4$ with $\sum a_i^2 = n$), define its normalized mass

$$
\operatorname{typeWeight}(t) \;=\; \frac{\operatorname{contribution}(t)}{r_4(n)},
\qquad
\operatorname{contribution}(t) = 2^{\,\#\{i : a_i \ne 0\}}\cdot\frac{4!}{\prod_v m_v!},
$$

where $m_v$ are the multiplicities of the distinct values. **Conjecture:** for $n = p^2$ with $p$ an odd prime, the trivial type $\tau_p = (0,0,0,p)$ has contribution $8$ and, since Jacobi gives $r_4(p^2) = 8\,\sigma(p^2) = 8\,(1 + p + p^2)$,

$$
\operatorname{typeWeight}(\tau_p) \;=\; \frac{8}{8\,(p^2 + p + 1)} \;=\; \frac{1}{p^2 + p + 1} \;\xrightarrow[p\to\infty]{}\; 0,
$$

while the non-trivial types absorb the complementary mass $\dfrac{p^2+p}{p^2+p+1} \to 1$.

### Plain Language

When you count the ways to write $n = a^2+b^2+c^2+d^2$, the solutions clump into "types" determined by the unordered set of absolute values; each type owns a fixed share of the total count $r_4(n)$ coming from its sign flips and reorderings. This problem asks for a clean formula for those shares when $n = p^2$ is the square of an odd prime. The claim is that the boring type $(0,0,0,p)$ — the one that just says $p^2 = 0+0+0+p^2$ — owns an exactly $1/(p^2+p+1)$ slice, which shrinks toward zero as the prime grows, with the structured types $(a,b,c,d)$ swallowing the rest.

### Why This Matters

This is a small but illustrative bridge between the combinatorial type-decomposition (orbit sizes of the signed-permutation group) and the analytic arithmetic of Jacobi's formula. Pinning the trivial-type weight to the rational function $1/(p^2+p+1)$ makes precise how a single "degenerate" representation becomes asymptotically negligible while the generic structured representations dominate — a concrete instance of equidistribution-of-mass intuition. It is honest in scope: the heavy arithmetic ($r_4(p^2) = 8(p^2+p+1)$) is supplied by Jacobi, so the genuinely new content is the closed-form bookkeeping of the weight and its limit, plus computational confirmation of the full split.

## Known Results

### What's Already Proven

- Jacobi's four-square theorem $r_4(n) = 8\sum_{d\mid n,\,4\nmid d} d$ (for odd $n$ this is $8\,\sigma(n)$) — classical (Jacobi 1829); gallery proof `four-square-distribution`
- The per-type contribution formula $\operatorname{contribution}(t) = 2^{\#\text{nonzero}}\cdot 4!/\prod m_v!$ and `trivial_type k` always contributing $8$ — gallery proof `four-square-distribution` (`trivial_type_1..5`)
- The verified instance $r_4(9) = 8 + 96 = 104 = 8\cdot 13$, i.e. weight $8/104 = 1/13 = 1/(3^2+3+1)$ — gallery proof `four-square-distribution` (`r₄_9_distribution`, `n4_type_weights`)
- Lagrange existence $r_4(n) > 0$ — Mathlib `Nat.sum_four_squares`

### What's Still Open

- A symbolic proof that $\operatorname{typeWeight}((0,0,0,p)) = 1/(p^2+p+1)$ for every odd prime $p$ (rather than case-by-case `native_decide`)
- Whether the complementary mass $\,(p^2+p)/(p^2+p+1)$ admits a clean breakdown across the individual non-trivial types of $p^2$

### Our Goal

Two-stage and deliberately modest: (1) computationally verify, via `native_decide` on enumerated `RepType (p^2)`, that the full type split holds and the trivial-type weight equals $1/(p^2+p+1)$ for $p = 3, 5, 7, 11$; (2) prove the closed form symbolically by combining the constant $\operatorname{contribution}((0,0,0,p)) = 8$ with $r_4(p^2) = 8\,\sigma(p^2)$ and $\sigma(p^2) = 1 + p + p^2$ (the latter from Mathlib's `Nat.sigma`/prime-power lemmas), then read off the $p\to\infty$ limit. We take Jacobi's value of $r_4(p^2)$ as an input rather than reproving it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| four-square-distribution | Parent proof; defines `contribution`, `typeWeight`, `trivial_type`, and the `n4_type_weights` split this generalizes | `native_decide`, orbit sizes, multinomials |
| four-square-distribution-oq-01 | The full Jacobi $r_4(n) = 8\sigma^*(n)$ formalization that supplies the denominator | Modular forms / divisor sums |
| lagrange-four-squares-waring-g2 | Quantitative four-square representation counts | Descent, counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Symbolic closed form via Mathlib divisor sums.
   - Why it might work: $\operatorname{contribution}((0,0,0,p)) = 8$ is a constant (4 permutations $\times$ 2 signs, independent of $p$), and $\sigma(p^2) = 1 + p + p^2$ follows from `Nat.sigma_one_eq_sigmaOne` / `Nat.Prime`-power divisor lemmas; dividing gives $1/(p^2+p+1)$ directly.
   - Risk: requires Jacobi's $r_4(p^2) = 8\sigma(p^2)$ as a hypothesis (OQ-01 is not yet formalized), so the result is conditional on that input.

2. **Approach B**: Numerical confirmation by enumeration.
   - Why it might work: for fixed $p \in \{3,5,7,11\}$ the set `RepType (p^2)` is finite and `deriving DecidableEq`, so `native_decide` can confirm the total split and each weight; mirrors the existing `distribution_complete_*` pattern.
   - Risk: `native_decide` only handles concrete $p$ (no induction over primes) and adds a `Lean.ofReduceBool` dependency, so it confirms but does not prove the general statement.

### Key Difficulties

- The denominator $r_4(p^2)$ is Jacobi's value; without OQ-01 the closed form is conditional on importing $r_4(p^2) = 8(p^2+p+1)$ as an assumption.
- The "non-trivial types absorb the remaining mass" half requires enumerating which $p^2 - a^2$ are sums of three squares, which has no simple uniform shape across primes — only the trivial-type weight is genuinely clean.

### What Would a Proof Need?

- Key lemma 1: $\operatorname{contribution}((0,0,0,p)) = 8$ for all $p$ (constant; already in parent as `trivial_type`).
- Key lemma 2: $\sigma(p^2) = 1 + p + p^2$ for $p$ prime (Mathlib prime-power divisor sum).
- Key lemma 3: $r_4(p^2) = 8\,\sigma(p^2)$ (Jacobi input, possibly an axiom/hypothesis pending OQ-01), hence $\operatorname{typeWeight} = 1/(p^2+p+1)$ and the limit is $0$.
- Technical requirements: rational/real division to state the weight, `Nat.sigma`, `Nat.Prime`, `Filter.Tendsto` for the $p\to\infty$ limit.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The numerical half is essentially mechanical, reusing the parent proof's `native_decide` enumeration pattern; the symbolic half reduces to one prime-power divisor identity plus a Jacobi input.
- Similar prime-power $\sigma$ computations already appear across the gallery's number-theory cluster (e.g. odd-perfect / divisor-sum work), and Mathlib's `Nat.sigma` and `Filter.Tendsto` machinery cover the remaining pieces.
- The main friction is honest scoping: the cleanest result is conditional on Jacobi ($r_4(p^2) = 8\sigma(p^2)$), and only the trivial-type weight has a uniform closed form.

**Estimated Effort**:
- Exploration: 0.5–1 day (confirm the $\sigma(p^2)$ identity and the parent's `RepType` enumeration interface)
- If tractable: 3–5 days for the conditional closed form plus $k = 3,5,7,11$ numerical verification
- If hard: an unconditional, fully general non-trivial-mass breakdown is likely open (entangled with OQ-01)

## References

### Papers
- C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum*, 1829 — origin of $r_4(n) = 8\sigma^*(n)$ via theta functions.
- E. Grosswald, *Representations of Integers as Sums of Squares*, 1985 — comprehensive treatment of $r_k(n)$ and divisor-sum formulas.

### Online Resources
- https://oeis.org/A000118 — OEIS sequence $r_4(n)$ (number of ways to write $n$ as a sum of 4 squares); confirms $r_4(9)=104$, $r_4(25)=248$, $r_4(49)=456$, $r_4(121)=1064$.

### Mathlib
- `Mathlib.NumberTheory.SumFourSquares` — Lagrange's four-square theorem (`Nat.sum_four_squares`), the existence backbone.
- `Mathlib.NumberTheory.Divisors` — `Nat.sigma` and prime-power divisor-sum lemmas for $\sigma(p^2) = 1 + p + p^2$.
- `Mathlib.Order.Filter.Basic` / `Mathlib.Topology.Algebra.Order` — `Filter.Tendsto` for the $1/(p^2+p+1) \to 0$ limit.

## Metadata

```yaml
tags:
  - number-theory
  - sums-of-squares
  - jacobi
  - representations
  - divisor-sums
related_proofs:
  - four-square-distribution
  - four-square-distribution-oq-01
  - lagrange-four-squares-waring-g2
difficulty: medium
source: user-request
created: 2026-06-27T11:33:01-07:00
```
