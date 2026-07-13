# Problem: General Factorial Moments of a Pascal Row

**Slug**: combinations-formula-oq-09-oq-01
**Created**: 2026-07-01T22:11:23-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For all natural numbers $n$ and $j$, with the falling factorial written $(x)_j = x(x-1)\cdots(x-j+1) = x!/(x-j)!$,

$$
\sum_{k=0}^{n} (k)_j \, \binom{n}{k} \;=\; (n)_j \, 2^{\,n-j},
$$

where $(k)_j = k(k-1)\cdots(k-j+1)$ is the $j$-th falling factorial of $k$ (equal to $0$ whenever $k < j$). Equivalently, in Lean's $\mathbb{N}$ vocabulary using `Nat.descFactorial`,

$$
\sum_{k=0}^{n} k^{\underline{j}} \binom{n}{k} = n^{\underline{j}} \, 2^{\,n-j}.
$$

The cases $j = 1$ and $j = 2$ recover the first and second moments proved in the parent (after rewriting $k^2 = (k)_2 + k$).

### Plain Language

The parent entry computed the "weighted row sums" $\sum_k k\binom{n}{k} = n\,2^{n-1}$ and $\sum_k k^2\binom{n}{k} = n(n+1)2^{n-2}$ — the first and second moments of a row of Pascal's triangle. This extension proves the general pattern for every order $j$ at once, but using the *factorial* moment (falling-factorial weight $(k)_j$) rather than the ordinary power $k^j$, because the factorial moment has the cleanest closed form.

The mechanism is the **absorption identity** $k\binom{n}{k} = n\binom{n-1}{k-1}$. Applying it once "peels" a factor from the falling factorial and shifts the row from $n$ to $n-1$: it turns $\sum_k (k)_j \binom{n}{k}$ into $n \sum_k (k-1)_{j-1}\binom{n-1}{k-1}$. Reindexing the inner sum makes it a factorial moment of order $j-1$ over row $n-1$, so induction on $j$ closes the loop. After $j$ peels, the leftover sum is just $\sum_k \binom{n-j}{k} = 2^{n-j}$, and the peeled prefactors have accumulated to $(n)_j$.

### Why This Matters

This single identity unifies every moment identity the gallery has for binomial rows. Dividing by $2^n$, it says the $j$-th factorial moment of a $\text{Binomial}(n, \tfrac12)$ random variable is $(n)_j \, (\tfrac12)^j = n^{\underline{j}} p^j$ with $p = \tfrac12$ — the textbook formula for factorial moments of a binomial distribution. Ordinary power moments ($\sum_k k^j \binom{n}{k}$) then follow mechanically by expanding $k^j$ into falling factorials via Stirling numbers of the second kind, so the factorial-moment form is the natural "master" identity from which the mean $n/2$, the variance $n/4$, and all higher moments descend.

## Known Results

### What's Already Proven

- First moment $\sum_{k=0}^{n} k\binom{n}{k} = n\,2^{n-1}$ — parent proof `combinations-formula-oq-09` (`sum_range_mul_choose`), the $j=1$ case.
- Second moment $\sum_{k=0}^{n} k^2\binom{n}{k} = n(n+1)2^{n-2}$ — parent proof `combinations-formula-oq-09` (`sum_range_sq_mul_choose`), which is the $j=2$ factorial moment plus the $j=1$ moment since $k^2 = (k)_2 + k$.
- Absorption identity $(k+1)\binom{n+1}{k+1} = (n+1)\binom{n}{k}$ — Mathlib `Nat.succ_mul_choose_eq` / `Nat.add_one_mul_choose_eq`, repackaged as `absorb` in the parent.
- Row sum $\sum_{k=0}^{n} \binom{n}{k} = 2^n$ — Mathlib `Nat.sum_range_choose`.
- Falling-factorial arithmetic $x^{\underline{j+1}} = x^{\underline{j}}\,(x-j)$ and $x^{\underline{j}} = 0$ for $x < j$ — Mathlib `Nat.descFactorial`.

### What's Still Open

- The general-$j$ identity $\sum_{k=0}^{n} (k)_j \binom{n}{k} = (n)_j\, 2^{n-j}$ by induction on $j$ — not yet formalized in the gallery for arbitrary $j$.
- Whether the ordinary power-moment form $\sum_k k^j \binom{n}{k}$ can be assembled from this factorial-moment master identity through the Stirling-number change of basis.

### Our Goal

Prove the general factorial-moment identity $\sum_{k=0}^{n} (k)_j \binom{n}{k} = (n)_j\, 2^{n-j}$ in $\mathbb{N}$ for all $n, j$, by induction on $j$ using the parent's `absorb` lemma once per step. Deliver a verified, 0-axiom Lean entry with the identity, the reindexing lemmas it needs, and worked numerical checks; recovering the parent's $j=1,2$ cases as corollaries is a bonus, not a requirement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-09 | Direct parent — proves the $j=1,2$ moments and supplies the `absorb` lemma and peel-then-sum pattern this generalizes | absorption identity, `Finset.sum_range_succ'`, `Nat.sum_range_choose` |
| combinations-formula-oq-01 | Sibling — provides the row sum $\sum \binom{n}{k} = 2^n$ and alternating sum $\sum (-1)^k \binom{n}{k} = 0$ that these moments complement | binomial theorem, Finset sums |
| binomial-theorem | Alternative route — moments arise from differentiating $(1+x)^n$ and evaluating at $x=1$ | polynomial expansion, `Commute.add_pow` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Induction on $j$ with one absorption per step**: Prove a shifted lemma $\sum_{k=0}^{n} (k)_{j}\binom{n}{k} = (n)_{j}\,2^{n-j}$ by induction on $j$. Base case $j=0$: $(k)_0 = 1$ so the sum is the row sum $2^n$. Step: rewrite $(k)_{j+1} = (k)_{j}\,(k-j)$ — or better, arrange the peel so absorption fires on the outermost factor $k\binom{n}{k} = n\binom{n-1}{k-1}$ (`absorb` with `Finset.sum_range_succ'` to kill the $k=0$ term), reindex $k \mapsto k+1$, and recognize the remaining sum as the order-$j$ factorial moment over row $n-1$, which the induction hypothesis evaluates to $(n-1)_{j}\,2^{n-1-j}$. Multiply by the peeled $n$: $n\cdot (n-1)_{j} = (n)_{j+1}$ and $n\cdot 2^{n-1-j} = 2^{n-(j+1)}$ collapses cleanly.
   - Why it might work: reuses the parent's verified `absorb` verbatim; each inductive step is exactly one application of the same lemma the parent already exercised; everything stays in $\mathbb{N}$ with `Nat.descFactorial`.
   - Risk: the reindexing `Finset` bookkeeping ($k \mapsto k+1$, range shift, aligning `Nat.descFactorial` arguments) is fiddly and where most of the effort will go.

2. **Approach B — Generating functions / formal differentiation**: Note $(k)_j \binom{n}{k}$ is the coefficient extracted by the $j$-th derivative: $\sum_k (k)_j \binom{n}{k} x^{k-j} = \frac{d^j}{dx^j}(1+x)^n = (n)_j (1+x)^{n-j}$; evaluate at $x = 1$ to get $(n)_j\, 2^{n-j}$.
   - Why it might work: conceptually immediate and matches the classical "differentiate the binomial theorem" story; ties into the `binomial-theorem` gallery entry.
   - Risk: requires moving to $\mathbb{R}$ (or polynomials) and formal $j$-fold differentiation of $(1+x)^n$ with falling-factorial bookkeeping — heavier Mathlib machinery than the purely combinatorial Approach A, and a re-casting into $\mathbb{N}$ at the end.

### Key Difficulties

- Reindexing the `Finset` sum after each absorption shift ($k \mapsto k+1$, `range (n+1)` alignment) so the inner sum is literally the order-$j$ moment the induction hypothesis expects.
- Handling the vanishing low-order terms: $(k)_j = 0$ for $k < j$ (and the $k=0$ term peeled by `Finset.sum_range_succ'`) must be shown not to disturb the sum.
- Working with `Nat.descFactorial` throughout: the identity $x^{\underline{j+1}} = x \cdot (x-1)^{\underline{j}}$ vs. $x^{\underline{j}}(x-j)$ — choosing the recursion direction that aligns with absorption's $k \mapsto k+1$, $n \mapsto n-1$ shift.
- Keeping the exponent $2^{n-j}$ in $\mathbb{N}$ without truncated subtraction; prefer the shifted statement over `range (n+j)` forms.

### What Would a Proof Need?

- Key lemma 1: the parent's `absorb`, $(k+1)\binom{n+1}{k+1} = (n+1)\binom{n}{k}$ (Mathlib `Nat.succ_mul_choose_eq`).
- Key lemma 2: a `descFactorial` recursion aligning the peel, e.g. `Nat.descFactorial_succ` / `Nat.succ_descFactorial_succ`, plus `Nat.descFactorial_eq_zero_iff_lt` for the vanishing terms.
- Technical requirements: a reindexing step (`Finset.sum_range_succ'` to peel $k=0$, then $k \mapsto k+1$), `Nat.sum_range_choose` for the $j=0$ base, and careful induction so the induction hypothesis is applied at row $n-1$ and order $j$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The proof is a clean induction on $j$ reusing a lemma (`absorb`) already verified in the parent; there is no new mathematical idea, only careful Finset reindexing.
- The parent already executed the $j=1$ and $j=2$ instances of exactly this peel-then-absorb pattern, so the template is proven to work in Lean.
- Mathlib supplies all primitives: `Nat.descFactorial` with its full recursion API, `Nat.succ_mul_choose_eq` (absorption), and `Nat.sum_range_choose` (row sum). The only real work is the Finset index gymnastics, which is routine but error-prone.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1–3 days
- If hard: 1 week (if the reindexing forces awkward `descFactorial`/`range` normal forms)

## References

### Papers
- R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, Addison-Wesley, 1994 — falling factorials, binomial-coefficient absorption, and factorial-moment sums.
- J. Riordan, *Combinatorial Identities*, Wiley, 1968 — systematic treatment of weighted binomial sums.

### Online Resources
- https://en.wikipedia.org/wiki/Binomial_distribution#Moments — factorial moments of $\text{Binomial}(n,p)$ equal $(n)_j\,p^j$, the $p=\tfrac12$ specialization scaled by $2^n$.
- https://en.wikipedia.org/wiki/Falling_and_rising_factorials — falling factorial identities used in the peel step.

### Mathlib
- `Nat.descFactorial` — the natural-number falling factorial $n^{\underline{j}}$ with recursion `Nat.descFactorial_succ`, `Nat.succ_descFactorial_succ`, and `Nat.descFactorial_eq_zero_iff_lt`.
- `Nat.succ_mul_choose_eq` / `Nat.add_one_mul_choose_eq` — the absorption identity $(k+1)\binom{n+1}{k+1} = (n+1)\binom{n}{k}$.
- `Nat.sum_range_choose` — the row sum $\sum_{k=0}^{n}\binom{n}{k} = 2^n$ (base case $j=0$).
- `Finset.sum_range_succ'` / `Finset.sum_range_succ` — peel the boundary term to align the $k\mapsto k+1$ reindex; `Nat.choose_symm` for symmetric rewrites if needed.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - weighted-sums
  - factorial-moments
  - absorption-identity
related_proofs:
  - combinations-formula-oq-09
  - combinations-formula-oq-01
  - binomial-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:23-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
